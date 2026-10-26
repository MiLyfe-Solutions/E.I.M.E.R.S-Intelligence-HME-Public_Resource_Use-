import V185TrunkScan22Chunk401

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3585337 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 6]
def baseStart_3585337 : Nat := 118140960795 + 3585337 * 2 ^ 59
def prefixEnd_3585337 : Nat := 4983230072969 + 3 ^ 40 * 3585337 * 2
def baseEnd_3585337 : Nat := 409111375410920908044187

theorem tailTrace_3585337 : CollatzResearch.WordTrace tailWord_3585337 prefixEnd_3585337 409111375410920908044187 := by
  unfold tailWord_3585337
  simp only [CollatzResearch.WordTrace]
  refine ⟨130767983411943850654882265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87178655607962567103254843 130767983411943850654882265)
  ·
    refine ⟨98075987558957887991161699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130767983411943850654882265 98075987558957887991161699)
    ·
      refine ⟨147113981338436831986742549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98075987558957887991161699 147113981338436831986742549)
      ·
        refine ⟨6895967875239226499378557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147113981338436831986742549 6895967875239226499378557)
        ·
          refine ⟨2585987953214709937266959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6895967875239226499378557 2585987953214709937266959)
          ·
            refine ⟨3878981929822064905900439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585987953214709937266959 3878981929822064905900439)
            ·
              refine ⟨5818472894733097358850659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878981929822064905900439 5818472894733097358850659)
              ·
                refine ⟨8727709342099646038275989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5818472894733097358850659 8727709342099646038275989)
                ·
                  refine ⟨409111375410920908044187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8727709342099646038275989 409111375410920908044187)
                  ·
                    rfl

theorem cell22_3585337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_3585337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585337 prefixEnd_3585337 := by exact prefixLift 3585337
  have htrace : WordTrace (prefixWord ++ tailWord_3585337) baseStart_3585337 baseEnd_3585337 := by
    simpa [prefixWord, tailWord_3585337, baseEnd_3585337] using wordTrace_append hprefix tailTrace_3585337
  have hstable : (prefixWord ++ tailWord_3585337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585337).length < 2 ^ (prefixWord ++ tailWord_3585337).sum := by decide
  have hdescent : baseEnd_3585337 < baseStart_3585337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585363 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 5, 3]
def baseStart_3585363 : Nat := 118140960795 + 3585363 * 2 ^ 59
def prefixEnd_3585363 : Nat := 4983230072969 + 3 ^ 40 * 3585363 * 2
def baseEnd_3585363 : Nat := 1227343026564107322982481

theorem tailTrace_3585363 : CollatzResearch.WordTrace tailWord_3585363 prefixEnd_3585363 1227343026564107322982481 := by
  unfold tailWord_3585363
  simp only [CollatzResearch.WordTrace]
  refine ⟨130768931709849657095328743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87179287806566438063552495 130768931709849657095328743)
  ·
    refine ⟨196153397564774485642993115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130768931709849657095328743 196153397564774485642993115)
    ·
      refine ⟨294230096347161728464489673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196153397564774485642993115 294230096347161728464489673)
      ·
        refine ⟨220672572260371296348367255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294230096347161728464489673 220672572260371296348367255)
        ·
          refine ⟨331008858390556944522550883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220672572260371296348367255 331008858390556944522550883)
          ·
            refine ⟨496513287585835416783826325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331008858390556944522550883 496513287585835416783826325)
            ·
              refine ⟨23274060355586035161741859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 496513287585835416783826325 23274060355586035161741859)
              ·
                refine ⟨34911090533379052742612789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23274060355586035161741859 34911090533379052742612789)
                ·
                  refine ⟨3272914737504286194619949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34911090533379052742612789 3272914737504286194619949)
                  ·
                    refine ⟨1227343026564107322982481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272914737504286194619949 1227343026564107322982481)
                    ·
                      rfl

theorem cell22_3585363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 5, 3].length) (baseStart_3585363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585363 prefixEnd_3585363 := by exact prefixLift 3585363
  have htrace : WordTrace (prefixWord ++ tailWord_3585363) baseStart_3585363 baseEnd_3585363 := by
    simpa [prefixWord, tailWord_3585363, baseEnd_3585363] using wordTrace_append hprefix tailTrace_3585363
  have hstable : (prefixWord ++ tailWord_3585363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585363).length < 2 ^ (prefixWord ++ tailWord_3585363).sum := by decide
  have hdescent : baseEnd_3585363 < baseStart_3585363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585393 : List Nat := [1, 2, 2, 2, 1, 2, 3, 4, 5]
def baseStart_3585393 : Nat := 118140960795 + 3585393 * 2 ^ 59
def prefixEnd_3585393 : Nat := 4983230072969 + 3 ^ 40 * 3585393 * 2
def baseEnd_3585393 : Nat := 409117765392399081577463

theorem tailTrace_3585393 : CollatzResearch.WordTrace tailWord_3585393 prefixEnd_3585393 409117765392399081577463 := by
  unfold tailWord_3585393
  simp only [CollatzResearch.WordTrace]
  refine ⟨130770025899740972218920833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87180017266493981479280555 130770025899740972218920833)
  ·
    refine ⟨98077519424805729164190625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130770025899740972218920833 98077519424805729164190625)
    ·
      refine ⟨73558139568604296873142969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98077519424805729164190625 73558139568604296873142969)
      ·
        refine ⟨55168604676453222654857227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73558139568604296873142969 55168604676453222654857227)
        ·
          refine ⟨82752907014679833982285841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55168604676453222654857227 82752907014679833982285841)
          ·
            refine ⟨62064680261009875486714381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82752907014679833982285841 62064680261009875486714381)
            ·
              refine ⟨23274255097878703307517893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62064680261009875486714381 23274255097878703307517893)
              ·
                refine ⟨4363922830852256870159605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23274255097878703307517893 4363922830852256870159605)
                ·
                  refine ⟨409117765392399081577463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4363922830852256870159605 409117765392399081577463)
                  ·
                    rfl

theorem cell22_3585393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_3585393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585393 prefixEnd_3585393 := by exact prefixLift 3585393
  have htrace : WordTrace (prefixWord ++ tailWord_3585393) baseStart_3585393 baseEnd_3585393 := by
    simpa [prefixWord, tailWord_3585393, baseEnd_3585393] using wordTrace_append hprefix tailTrace_3585393
  have hstable : (prefixWord ++ tailWord_3585393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585393).length < 2 ^ (prefixWord ++ tailWord_3585393).sum := by decide
  have hdescent : baseEnd_3585393 < baseStart_3585393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585440 : List Nat := [2, 1, 1, 4, 1, 2, 3, 3, 1, 4]
def baseStart_3585440 : Nat := 118140960795 + 3585440 * 2 ^ 59
def prefixEnd_3585440 : Nat := 4983230072969 + 3 ^ 40 * 3585440 * 2
def baseEnd_3585440 : Nat := 1227369385237704788807245

theorem tailTrace_3585440 : CollatzResearch.WordTrace tailWord_3585440 prefixEnd_3585440 1227369385237704788807245 := by
  unfold tailWord_3585440
  simp only [CollatzResearch.WordTrace]
  refine ⟨65385870065285349622940887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87181160087047132830587849 65385870065285349622940887)
  ·
    refine ⟨98078805097928024434411331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65385870065285349622940887 98078805097928024434411331)
    ·
      refine ⟨147118207646892036651616997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98078805097928024434411331 147118207646892036651616997)
      ·
        refine ⟨27584663933792256872178187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147118207646892036651616997 27584663933792256872178187)
        ·
          refine ⟨41376995900688385308267281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27584663933792256872178187 41376995900688385308267281)
          ·
            refine ⟨31032746925516288981200461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41376995900688385308267281 31032746925516288981200461)
            ·
              refine ⟨11637280097068608367950173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31032746925516288981200461 11637280097068608367950173)
              ·
                refine ⟨4363980036400728137981315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11637280097068608367950173 4363980036400728137981315)
                ·
                  refine ⟨6545970054601092206971973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363980036400728137981315 6545970054601092206971973)
                  ·
                    refine ⟨1227369385237704788807245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6545970054601092206971973 1227369385237704788807245)
                    ·
                      rfl

theorem cell22_3585440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_3585440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585440 prefixEnd_3585440 := by exact prefixLift 3585440
  have htrace : WordTrace (prefixWord ++ tailWord_3585440) baseStart_3585440 baseEnd_3585440 := by
    simpa [prefixWord, tailWord_3585440, baseEnd_3585440] using wordTrace_append hprefix tailTrace_3585440
  have hstable : (prefixWord ++ tailWord_3585440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585440).length < 2 ^ (prefixWord ++ tailWord_3585440).sum := by decide
  have hdescent : baseEnd_3585440 < baseStart_3585440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585515 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 3, 3]
def baseStart_3585515 : Nat := 118140960795 + 3585515 * 2 ^ 59
def prefixEnd_3585515 : Nat := 4983230072969 + 3 ^ 40 * 3585515 * 2
def baseEnd_3585515 : Nat := 1227395059270429593182015

theorem tailTrace_3585515 : CollatzResearch.WordTrace tailWord_3585515 prefixEnd_3585515 1227395059270429593182015 := by
  unfold tailWord_3585515
  simp only [CollatzResearch.WordTrace]
  refine ⟨130774475605298987054861999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87182983736865991369907999 130774475605298987054861999)
  ·
    refine ⟨196161713407948480582292999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130774475605298987054861999 196161713407948480582292999)
    ·
      refine ⟨294242570111922720873439499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196161713407948480582292999 294242570111922720873439499)
      ·
        refine ⟨441363855167884081310159249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294242570111922720873439499 441363855167884081310159249)
        ·
          refine ⟨331022891375913060982619437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441363855167884081310159249 331022891375913060982619437)
          ·
            refine ⟨124133584265967397868482289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331022891375913060982619437 124133584265967397868482289)
            ·
              refine ⟨93100188199475548401361717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124133584265967397868482289 93100188199475548401361717)
              ·
                refine ⟨8728142643700832662627661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93100188199475548401361717 8728142643700832662627661)
                ·
                  refine ⟨3273053491387812248485373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8728142643700832662627661 3273053491387812248485373)
                  ·
                    refine ⟨1227395059270429593182015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273053491387812248485373 1227395059270429593182015)
                    ·
                      rfl

theorem cell22_3585515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 3, 3].length) (baseStart_3585515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585515 prefixEnd_3585515 := by exact prefixLift 3585515
  have htrace : WordTrace (prefixWord ++ tailWord_3585515) baseStart_3585515 baseEnd_3585515 := by
    simpa [prefixWord, tailWord_3585515, baseEnd_3585515] using wordTrace_append hprefix tailTrace_3585515
  have hstable : (prefixWord ++ tailWord_3585515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585515).length < 2 ^ (prefixWord ++ tailWord_3585515).sum := by decide
  have hdescent : baseEnd_3585515 < baseStart_3585515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585517 : List Nat := [1, 5, 1, 3, 2, 1, 2, 7]
def baseStart_3585517 : Nat := 118140960795 + 3585517 * 2 ^ 59
def prefixEnd_3585517 : Nat := 4983230072969 + 3 ^ 40 * 3585517 * 2
def baseEnd_3585517 : Nat := 136377304879033583848001

theorem tailTrace_3585517 : CollatzResearch.WordTrace tailWord_3585517 prefixEnd_3585517 136377304879033583848001 := by
  unfold tailWord_3585517
  simp only [CollatzResearch.WordTrace]
  refine ⟨130774548551291741396434805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87183032367527827597623203 130774548551291741396434805)
  ·
    refine ⟨12260113926683600755915763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130774548551291741396434805 12260113926683600755915763)
    ·
      refine ⟨18390170890025401133873645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12260113926683600755915763 18390170890025401133873645)
      ·
        refine ⟨6896314083759525425202617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18390170890025401133873645 6896314083759525425202617)
        ·
          refine ⟨5172235562819644068901963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6896314083759525425202617 5172235562819644068901963)
          ·
            refine ⟨7758353344229466103352945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172235562819644068901963 7758353344229466103352945)
            ·
              refine ⟨5818765008172099577514709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7758353344229466103352945 5818765008172099577514709)
              ·
                refine ⟨136377304879033583848001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5818765008172099577514709 136377304879033583848001)
                ·
                  rfl

theorem cell22_3585517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 7].length) (baseStart_3585517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585517 prefixEnd_3585517 := by exact prefixLift 3585517
  have htrace : WordTrace (prefixWord ++ tailWord_3585517) baseStart_3585517 baseEnd_3585517 := by
    simpa [prefixWord, tailWord_3585517, baseEnd_3585517] using wordTrace_append hprefix tailTrace_3585517
  have hstable : (prefixWord ++ tailWord_3585517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585517).length < 2 ^ (prefixWord ++ tailWord_3585517).sum := by decide
  have hdescent : baseEnd_3585517 < baseStart_3585517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585605 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_3585605 : Nat := 118140960795 + 3585605 * 2 ^ 59
def prefixEnd_3585605 : Nat := 4983230072969 + 3 ^ 40 * 3585605 * 2
def baseEnd_3585605 : Nat := 1227425868109699358431739

theorem tailTrace_3585605 : CollatzResearch.WordTrace tailWord_3585605 prefixEnd_3585605 1227425868109699358431739 := by
  unfold tailWord_3585605
  simp only [CollatzResearch.WordTrace]
  refine ⟨130777758174972932425638269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87185172116648621617092179 130777758174972932425638269)
  ·
    refine ⟨49041659315614849659614351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130777758174972932425638269 49041659315614849659614351)
    ·
      refine ⟨73562488973422274489421527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49041659315614849659614351 73562488973422274489421527)
      ·
        refine ⟨110343733460133411734132291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73562488973422274489421527 110343733460133411734132291)
        ·
          refine ⟨165515600190200117601198437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110343733460133411734132291 165515600190200117601198437)
          ·
            refine ⟨31034175035662522050224707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165515600190200117601198437 31034175035662522050224707)
            ·
              refine ⟨46551262553493783075337061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31034175035662522050224707 46551262553493783075337061)
              ·
                refine ⟨8728361728780084326625699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46551262553493783075337061 8728361728780084326625699)
                ·
                  refine ⟨13092542593170126489938549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8728361728780084326625699 13092542593170126489938549)
                  ·
                    refine ⟨1227425868109699358431739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13092542593170126489938549 1227425868109699358431739)
                    ·
                      rfl

theorem cell22_3585605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_3585605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585605 prefixEnd_3585605 := by exact prefixLift 3585605
  have htrace : WordTrace (prefixWord ++ tailWord_3585605) baseStart_3585605 baseEnd_3585605 := by
    simpa [prefixWord, tailWord_3585605, baseEnd_3585605] using wordTrace_append hprefix tailTrace_3585605
  have hstable : (prefixWord ++ tailWord_3585605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585605).length < 2 ^ (prefixWord ++ tailWord_3585605).sum := by decide
  have hdescent : baseEnd_3585605 < baseStart_3585605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585742 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 6]
def baseStart_3585742 : Nat := 118140960795 + 3585742 * 2 ^ 59
def prefixEnd_3585742 : Nat := 4983230072969 + 3 ^ 40 * 3585742 * 2
def baseEnd_3585742 : Nat := 409157588669825555918773

theorem tailTrace_3585742 : CollatzResearch.WordTrace tailWord_3585742 prefixEnd_3585742 409157588669825555918773 := by
  unfold tailWord_3585742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16347844371934575602921935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87188503316984403215583653 16347844371934575602921935)
  ·
    refine ⟨24521766557901863404382903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16347844371934575602921935 24521766557901863404382903)
    ·
      refine ⟨36782649836852795106574355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24521766557901863404382903 36782649836852795106574355)
      ·
        refine ⟨55173974755279192659861533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36782649836852795106574355 55173974755279192659861533)
        ·
          refine ⟨20690240533229697247448075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55173974755279192659861533 20690240533229697247448075)
          ·
            refine ⟨31035360799844545871172113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20690240533229697247448075 31035360799844545871172113)
            ·
              refine ⟨23276520599883409403379085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31035360799844545871172113 23276520599883409403379085)
              ·
                refine ⟨8728695224956278526267157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23276520599883409403379085 8728695224956278526267157)
                ·
                  refine ⟨409157588669825555918773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8728695224956278526267157 409157588669825555918773)
                  ·
                    rfl

theorem cell22_3585742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_3585742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585742 prefixEnd_3585742 := by exact prefixLift 3585742
  have htrace : WordTrace (prefixWord ++ tailWord_3585742) baseStart_3585742 baseEnd_3585742 := by
    simpa [prefixWord, tailWord_3585742, baseEnd_3585742] using wordTrace_append hprefix tailTrace_3585742
  have hstable : (prefixWord ++ tailWord_3585742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585742).length < 2 ^ (prefixWord ++ tailWord_3585742).sum := by decide
  have hdescent : baseEnd_3585742 < baseStart_3585742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585774 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_3585774 : Nat := 118140960795 + 3585774 * 2 ^ 59
def prefixEnd_3585774 : Nat := 4983230072969 + 3 ^ 40 * 3585774 * 2
def baseEnd_3585774 : Nat := 1227483720263439250956221

theorem tailTrace_3585774 : CollatzResearch.WordTrace tailWord_3585774 prefixEnd_3585774 1227483720263439250956221 := by
  unfold tailWord_3585774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16347990263920084286067547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87189281407573782859026917 16347990263920084286067547)
  ·
    refine ⟨24521985395880126429101321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16347990263920084286067547 24521985395880126429101321)
    ·
      refine ⟨18391489046910094821825991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24521985395880126429101321 18391489046910094821825991)
      ·
        refine ⟨27587233570365142232738987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18391489046910094821825991 27587233570365142232738987)
        ·
          refine ⟨41380850355547713349108481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27587233570365142232738987 41380850355547713349108481)
          ·
            refine ⟨31035637766660785011831361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41380850355547713349108481 31035637766660785011831361)
            ·
              refine ⟨23276728324995588758873521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31035637766660785011831361 23276728324995588758873521)
              ·
                refine ⟨17457546243746691569155141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23276728324995588758873521 17457546243746691569155141)
                ·
                  refine ⟨3273289920702504669216589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17457546243746691569155141 3273289920702504669216589)
                  ·
                    refine ⟨1227483720263439250956221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273289920702504669216589 1227483720263439250956221)
                    ·
                      rfl

theorem cell22_3585774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_3585774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585774 prefixEnd_3585774 := by exact prefixLift 3585774
  have htrace : WordTrace (prefixWord ++ tailWord_3585774) baseStart_3585774 baseEnd_3585774 := by
    simpa [prefixWord, tailWord_3585774, baseEnd_3585774] using wordTrace_append hprefix tailTrace_3585774
  have hstable : (prefixWord ++ tailWord_3585774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585774).length < 2 ^ (prefixWord ++ tailWord_3585774).sum := by decide
  have hdescent : baseEnd_3585774 < baseStart_3585774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585847 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 2, 5]
def baseStart_3585847 : Nat := 118140960795 + 3585847 * 2 ^ 59
def prefixEnd_3585847 : Nat := 4983230072969 + 3 ^ 40 * 3585847 * 2
def baseEnd_3585847 : Nat := 1227508709655291393880997

theorem tailTrace_3585847 : CollatzResearch.WordTrace tailWord_3585847 prefixEnd_3585847 1227508709655291393880997 := by
  unfold tailWord_3585847
  simp only [CollatzResearch.WordTrace]
  refine ⟨130786584640096207755947795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87191056426730805170631863 130786584640096207755947795)
  ·
    refine ⟨196179876960144311633921693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130786584640096207755947795 196179876960144311633921693)
    ·
      refine ⟨73567453860054116862720635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196179876960144311633921693 73567453860054116862720635)
      ·
        refine ⟨110351180790081175294080953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73567453860054116862720635 110351180790081175294080953)
        ·
          refine ⟨82763385592560881470560715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110351180790081175294080953 82763385592560881470560715)
          ·
            refine ⟨124145078388841322205841073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82763385592560881470560715 124145078388841322205841073)
            ·
              refine ⟨93108808791630991654380805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124145078388841322205841073 93108808791630991654380805)
              ·
                refine ⟨17457901648430810935196401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93108808791630991654380805 17457901648430810935196401)
                ·
                  refine ⟨13093426236323108201397301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17457901648430810935196401 13093426236323108201397301)
                  ·
                    refine ⟨1227508709655291393880997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13093426236323108201397301 1227508709655291393880997)
                    ·
                      rfl

theorem cell22_3585847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_3585847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585847 prefixEnd_3585847 := by exact prefixLift 3585847
  have htrace : WordTrace (prefixWord ++ tailWord_3585847) baseStart_3585847 baseEnd_3585847 := by
    simpa [prefixWord, tailWord_3585847, baseEnd_3585847] using wordTrace_append hprefix tailTrace_3585847
  have hstable : (prefixWord ++ tailWord_3585847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585847).length < 2 ^ (prefixWord ++ tailWord_3585847).sum := by decide
  have hdescent : baseEnd_3585847 < baseStart_3585847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585853 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_3585853 : Nat := 118140960795 + 3585853 * 2 ^ 59
def prefixEnd_3585853 : Nat := 4983230072969 + 3 ^ 40 * 3585853 * 2
def baseEnd_3585853 : Nat := 1227510763577909378230979

theorem tailTrace_3585853 : CollatzResearch.WordTrace tailWord_3585853 prefixEnd_3585853 1227510763577909378230979 := by
  unfold tailWord_3585853
  simp only [CollatzResearch.WordTrace]
  refine ⟨130786803478074470780666213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87191202318716313853777475 130786803478074470780666213)
  ·
    refine ⟨24522525652138963271374915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130786803478074470780666213 24522525652138963271374915)
    ·
      refine ⟨36783788478208444907062373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24522525652138963271374915 36783788478208444907062373)
      ·
        refine ⟨6896960339664083420074195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36783788478208444907062373 6896960339664083420074195)
        ·
          refine ⟨10345440509496125130111293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6896960339664083420074195 10345440509496125130111293)
          ·
            refine ⟨3879540191061046923791735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10345440509496125130111293 3879540191061046923791735)
            ·
              refine ⟨5819310286591570385687603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3879540191061046923791735 5819310286591570385687603)
              ·
                refine ⟨8728965429887355578531405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5819310286591570385687603 8728965429887355578531405)
                ·
                  refine ⟨3273362036207758341949277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8728965429887355578531405 3273362036207758341949277)
                  ·
                    refine ⟨1227510763577909378230979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273362036207758341949277 1227510763577909378230979)
                    ·
                      rfl

theorem cell22_3585853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_3585853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585853 prefixEnd_3585853 := by exact prefixLift 3585853
  have htrace : WordTrace (prefixWord ++ tailWord_3585853) baseStart_3585853 baseEnd_3585853 := by
    simpa [prefixWord, tailWord_3585853, baseEnd_3585853] using wordTrace_append hprefix tailTrace_3585853
  have hstable : (prefixWord ++ tailWord_3585853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585853).length < 2 ^ (prefixWord ++ tailWord_3585853).sum := by decide
  have hdescent : baseEnd_3585853 < baseStart_3585853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585907 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 3, 6]
def baseStart_3585907 : Nat := 118140960795 + 3585907 * 2 ^ 59
def prefixEnd_3585907 : Nat := 4983230072969 + 3 ^ 40 * 3585907 * 2
def baseEnd_3585907 : Nat := 1227529248881471237380813

theorem tailTrace_3585907 : CollatzResearch.WordTrace tailWord_3585907 prefixEnd_3585907 1227529248881471237380813 := by
  unfold tailWord_3585907
  simp only [CollatzResearch.WordTrace]
  refine ⟨130788773019878838003131975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87192515346585892002087983 130788773019878838003131975)
  ·
    refine ⟨196183159529818257004697963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130788773019878838003131975 196183159529818257004697963)
    ·
      refine ⟨294274739294727385507046945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196183159529818257004697963 294274739294727385507046945)
      ·
        refine ⟨220706054471045539130285209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294274739294727385507046945 220706054471045539130285209)
        ·
          refine ⟨165529540853284154347713907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220706054471045539130285209 165529540853284154347713907)
          ·
            refine ⟨248294311279926231521570861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165529540853284154347713907 248294311279926231521570861)
            ·
              refine ⟨93110366729972336820589073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248294311279926231521570861 93110366729972336820589073)
              ·
                refine ⟨69832775047479252615441805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93110366729972336820589073 69832775047479252615441805)
                ·
                  refine ⟨26187290642804719730790677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69832775047479252615441805 26187290642804719730790677)
                  ·
                    refine ⟨1227529248881471237380813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26187290642804719730790677 1227529248881471237380813)
                    ·
                      rfl

theorem cell22_3585907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_3585907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585907 prefixEnd_3585907 := by exact prefixLift 3585907
  have htrace : WordTrace (prefixWord ++ tailWord_3585907) baseStart_3585907 baseEnd_3585907 := by
    simpa [prefixWord, tailWord_3585907, baseEnd_3585907] using wordTrace_append hprefix tailTrace_3585907
  have hstable : (prefixWord ++ tailWord_3585907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585907).length < 2 ^ (prefixWord ++ tailWord_3585907).sum := by decide
  have hdescent : baseEnd_3585907 < baseStart_3585907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585909 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3585909 : Nat := 118140960795 + 3585909 * 2 ^ 59
def prefixEnd_3585909 : Nat := 4983230072969 + 3 ^ 40 * 3585909 * 2
def baseEnd_3585909 : Nat := 1227529933522343898830807

theorem tailTrace_3585909 : CollatzResearch.WordTrace tailWord_3585909 prefixEnd_3585909 1227529933522343898830807 := by
  unfold tailWord_3585909
  simp only [CollatzResearch.WordTrace]
  refine ⟨130788845965871592344704781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87192563977247728229803187 130788845965871592344704781)
  ·
    refine ⟨49045817237201847129264293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130788845965871592344704781 49045817237201847129264293)
    ·
      refine ⟨9196090731975346336737055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49045817237201847129264293 9196090731975346336737055)
      ·
        refine ⟨13794136097963019505105583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9196090731975346336737055 13794136097963019505105583)
        ·
          refine ⟨20691204146944529257658375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13794136097963019505105583 20691204146944529257658375)
          ·
            refine ⟨31036806220416793886487563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20691204146944529257658375 31036806220416793886487563)
            ·
              refine ⟨46555209330625190829731345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31036806220416793886487563 46555209330625190829731345)
              ·
                refine ⟨34916406997968893122298509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46555209330625190829731345 34916406997968893122298509)
                ·
                  refine ⟨13093652624238334920861941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34916406997968893122298509 13093652624238334920861941)
                  ·
                    refine ⟨1227529933522343898830807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13093652624238334920861941 1227529933522343898830807)
                    ·
                      rfl

theorem cell22_3585909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3585909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585909 prefixEnd_3585909 := by exact prefixLift 3585909
  have htrace : WordTrace (prefixWord ++ tailWord_3585909) baseStart_3585909 baseEnd_3585909 := by
    simpa [prefixWord, tailWord_3585909, baseEnd_3585909] using wordTrace_append hprefix tailTrace_3585909
  have hstable : (prefixWord ++ tailWord_3585909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585909).length < 2 ^ (prefixWord ++ tailWord_3585909).sum := by decide
  have hdescent : baseEnd_3585909 < baseStart_3585909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585924 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3585924 : Nat := 118140960795 + 3585924 * 2 ^ 59
def prefixEnd_3585924 : Nat := 4983230072969 + 3 ^ 40 * 3585924 * 2
def baseEnd_3585924 : Nat := 1227535068328888859705761

theorem tailTrace_3585924 : CollatzResearch.WordTrace tailWord_3585924 prefixEnd_3585924 1227535068328888859705761 := by
  unfold tailWord_3585924
  simp only [CollatzResearch.WordTrace]
  refine ⟨65394696530408624953250413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87192928707211499937667217 65394696530408624953250413)
  ·
    refine ⟨24523011198903234357468905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65394696530408624953250413 24523011198903234357468905)
    ·
      refine ⟨18392258399177425768101679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24523011198903234357468905 18392258399177425768101679)
      ·
        refine ⟨27588387598766138652152519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18392258399177425768101679 27588387598766138652152519)
        ·
          refine ⟨41382581398149207978228779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27588387598766138652152519 41382581398149207978228779)
          ·
            refine ⟨62073872097223811967343169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41382581398149207978228779 62073872097223811967343169)
            ·
              refine ⟨46555404072917858975507377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62073872097223811967343169 46555404072917858975507377)
              ·
                refine ⟨34916553054688394231630533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46555404072917858975507377 34916553054688394231630533)
                ·
                  refine ⟨6546853697754073918430725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34916553054688394231630533 6546853697754073918430725)
                  ·
                    refine ⟨1227535068328888859705761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6546853697754073918430725 1227535068328888859705761)
                    ·
                      rfl

theorem cell22_3585924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3585924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585924 prefixEnd_3585924 := by exact prefixLift 3585924
  have htrace : WordTrace (prefixWord ++ tailWord_3585924) baseStart_3585924 baseEnd_3585924 := by
    simpa [prefixWord, tailWord_3585924, baseEnd_3585924] using wordTrace_append hprefix tailTrace_3585924
  have hstable : (prefixWord ++ tailWord_3585924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585924).length < 2 ^ (prefixWord ++ tailWord_3585924).sum := by decide
  have hdescent : baseEnd_3585924 < baseStart_3585924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585960 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3585960 : Nat := 118140960795 + 3585960 * 2 ^ 59
def prefixEnd_3585960 : Nat := 4983230072969 + 3 ^ 40 * 3585960 * 2
def baseEnd_3585960 : Nat := 1227547391864596765805651

theorem tailTrace_3585960 : CollatzResearch.WordTrace tailWord_3585960 prefixEnd_3585960 1227547391864596765805651 := by
  unfold tailWord_3585960
  simp only [CollatzResearch.WordTrace]
  refine ⟨65395353044343414027405667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87193804059124552036540889 65395353044343414027405667)
  ·
    refine ⟨98093029566515121041108501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65395353044343414027405667 98093029566515121041108501)
    ·
      refine ⟨4598110760930396298801961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98093029566515121041108501 4598110760930396298801961)
      ·
        refine ⟨3448583070697797224101471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4598110760930396298801961 3448583070697797224101471)
        ·
          refine ⟨5172874606046695836152207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3448583070697797224101471 5172874606046695836152207)
          ·
            refine ⟨7759311909070043754228311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5172874606046695836152207 7759311909070043754228311)
            ·
              refine ⟨11638967863605065631342467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759311909070043754228311 11638967863605065631342467)
              ·
                refine ⟨17458451795407598447013701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11638967863605065631342467 17458451795407598447013701)
                ·
                  refine ⟨3273459711638924708815069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17458451795407598447013701 3273459711638924708815069)
                  ·
                    refine ⟨1227547391864596765805651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273459711638924708815069 1227547391864596765805651)
                    ·
                      rfl

theorem cell22_3585960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3585960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585960 prefixEnd_3585960 := by exact prefixLift 3585960
  have htrace : WordTrace (prefixWord ++ tailWord_3585960) baseStart_3585960 baseEnd_3585960 := by
    simpa [prefixWord, tailWord_3585960, baseEnd_3585960] using wordTrace_append hprefix tailTrace_3585960
  have hstable : (prefixWord ++ tailWord_3585960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585960).length < 2 ^ (prefixWord ++ tailWord_3585960).sum := by decide
  have hdescent : baseEnd_3585960 < baseStart_3585960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585971 : List Nat := [1, 1, 1, 2, 3, 1, 6, 1, 3, 3]
def baseStart_3585971 : Nat := 118140960795 + 3585971 * 2 ^ 59
def prefixEnd_3585971 : Nat := 4983230072969 + 3 ^ 40 * 3585971 * 2
def baseEnd_3585971 : Nat := 1227551157389396403780617

theorem tailTrace_3585971 : CollatzResearch.WordTrace tailWord_3585971 prefixEnd_3585971 1227551157389396403780617 := by
  unfold tailWord_3585971
  simp only [CollatzResearch.WordTrace]
  refine ⟨130791107291646976933461767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87194071527764651288974511 130791107291646976933461767)
  ·
    refine ⟨196186660937470465400192651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130791107291646976933461767 196186660937470465400192651)
    ·
      refine ⟨294279991406205698100288977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196186660937470465400192651 294279991406205698100288977)
      ·
        refine ⟨220709993554654273575216733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294279991406205698100288977 220709993554654273575216733)
        ·
          refine ⟨82766247582995352590706275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220709993554654273575216733 82766247582995352590706275)
          ·
            refine ⟨124149371374493028886059413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82766247582995352590706275 124149371374493028886059413)
            ·
              refine ⟨5819501783179360729034035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124149371374493028886059413 5819501783179360729034035)
              ·
                refine ⟨8729252674769041093551053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5819501783179360729034035 8729252674769041093551053)
                ·
                  refine ⟨3273469753038390410081645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8729252674769041093551053 3273469753038390410081645)
                  ·
                    refine ⟨1227551157389396403780617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273469753038390410081645 1227551157389396403780617)
                    ·
                      rfl

theorem cell22_3585971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3, 3].length) (baseStart_3585971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585971 prefixEnd_3585971 := by exact prefixLift 3585971
  have htrace : WordTrace (prefixWord ++ tailWord_3585971) baseStart_3585971 baseEnd_3585971 := by
    simpa [prefixWord, tailWord_3585971, baseEnd_3585971] using wordTrace_append hprefix tailTrace_3585971
  have hstable : (prefixWord ++ tailWord_3585971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585971).length < 2 ^ (prefixWord ++ tailWord_3585971).sum := by decide
  have hdescent : baseEnd_3585971 < baseStart_3585971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586005 : List Nat := [1, 3, 2, 3, 2, 1, 3, 3, 1, 3]
def baseStart_3586005 : Nat := 118140960795 + 3586005 * 2 ^ 59
def prefixEnd_3586005 : Nat := 4983230072969 + 3 ^ 40 * 3586005 * 2
def baseEnd_3586005 : Nat := 1227562796284231648430513

theorem tailTrace_3586005 : CollatzResearch.WordTrace tailWord_3586005 prefixEnd_3586005 1227562796284231648430513 := by
  unfold tailWord_3586005
  simp only [CollatzResearch.WordTrace]
  refine ⟨130792347373523800740199469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87194898249015867160132979 130792347373523800740199469)
  ·
    refine ⟨49047130265071425277574801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130792347373523800740199469 49047130265071425277574801)
    ·
      refine ⟨36785347698803568958181101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49047130265071425277574801 36785347698803568958181101)
      ·
        refine ⟨13794505387051338359317913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36785347698803568958181101 13794505387051338359317913)
        ·
          refine ⟨10345879040288503769488435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13794505387051338359317913 10345879040288503769488435)
          ·
            refine ⟨15518818560432755654232653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10345879040288503769488435 15518818560432755654232653)
            ·
              refine ⟨5819556960162283370337245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15518818560432755654232653 5819556960162283370337245)
              ·
                refine ⟨2182333860060856263876467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5819556960162283370337245 2182333860060856263876467)
                ·
                  refine ⟨3273500790091284395814701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182333860060856263876467 3273500790091284395814701)
                  ·
                    refine ⟨1227562796284231648430513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273500790091284395814701 1227562796284231648430513)
                    ·
                      rfl

theorem cell22_3586005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_3586005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586005 prefixEnd_3586005 := by exact prefixLift 3586005
  have htrace : WordTrace (prefixWord ++ tailWord_3586005) baseStart_3586005 baseEnd_3586005 := by
    simpa [prefixWord, tailWord_3586005, baseEnd_3586005] using wordTrace_append hprefix tailTrace_3586005
  have hstable : (prefixWord ++ tailWord_3586005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586005).length < 2 ^ (prefixWord ++ tailWord_3586005).sum := by decide
  have hdescent : baseEnd_3586005 < baseStart_3586005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586074 : List Nat := [3, 1, 1, 3, 1, 13]
def baseStart_3586074 : Nat := 118140960795 + 3586074 * 2 ^ 59
def prefixEnd_3586074 : Nat := 4983230072969 + 3 ^ 40 * 3586074 * 2
def baseEnd_3586074 : Nat := 15155387856720228005621

theorem tailTrace_3586074 : CollatzResearch.WordTrace tailWord_3586074 prefixEnd_3586074 15155387856720228005621 := by
  unfold tailWord_3586074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32698716002568456381115319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87196576006849217016307517 32698716002568456381115319)
  ·
    refine ⟨49048074003852684571672979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32698716002568456381115319 49048074003852684571672979)
    ·
      refine ⟨73572111005779026857509469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49048074003852684571672979 73572111005779026857509469)
      ·
        refine ⟨27589541627167135071566051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73572111005779026857509469 27589541627167135071566051)
        ·
          refine ⟨41384312440750702607349077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27589541627167135071566051 41384312440750702607349077)
          ·
            refine ⟨15155387856720228005621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 41384312440750702607349077 15155387856720228005621)
            ·
              rfl

theorem cell22_3586074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 13].length) (baseStart_3586074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586074 prefixEnd_3586074 := by exact prefixLift 3586074
  have htrace : WordTrace (prefixWord ++ tailWord_3586074) baseStart_3586074 baseEnd_3586074 := by
    simpa [prefixWord, tailWord_3586074, baseEnd_3586074] using wordTrace_append hprefix tailTrace_3586074
  have hstable : (prefixWord ++ tailWord_3586074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586074).length < 2 ^ (prefixWord ++ tailWord_3586074).sum := by decide
  have hdescent : baseEnd_3586074 < baseStart_3586074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586136 : List Nat := [2, 1, 2, 2, 1, 5, 1, 1, 7]
def baseStart_3586136 : Nat := 118140960795 + 3586136 * 2 ^ 59
def prefixEnd_3586136 : Nat := 4983230072969 + 3 ^ 40 * 3586136 * 2
def baseEnd_3586136 : Nat := 409202546753796991135037

theorem tailTrace_3586136 : CollatzResearch.WordTrace tailWord_3586136 prefixEnd_3586136 409202546753796991135037 := by
  unfold tailWord_3586136
  simp only [CollatzResearch.WordTrace]
  refine ⟨65398562668024605056609131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87198083557366140075478841 65398562668024605056609131)
  ·
    refine ⟨98097844002036907584913697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65398562668024605056609131 98097844002036907584913697)
    ·
      refine ⟨73573383001527680688685273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98097844002036907584913697 73573383001527680688685273)
      ·
        refine ⟨55180037251145760516513955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73573383001527680688685273 55180037251145760516513955)
        ·
          refine ⟨82770055876718640774770933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55180037251145760516513955 82770055876718640774770933)
          ·
            refine ⟨7759692738442372572634775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82770055876718640774770933 7759692738442372572634775)
            ·
              refine ⟨11639539107663558858952163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7759692738442372572634775 11639539107663558858952163)
              ·
                refine ⟨17459308661495338288428245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11639539107663558858952163 17459308661495338288428245)
                ·
                  refine ⟨409202546753796991135037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17459308661495338288428245 409202546753796991135037)
                  ·
                    rfl

theorem cell22_3586136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 7].length) (baseStart_3586136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586136 prefixEnd_3586136 := by exact prefixLift 3586136
  have htrace : WordTrace (prefixWord ++ tailWord_3586136) baseStart_3586136 baseEnd_3586136 := by
    simpa [prefixWord, tailWord_3586136, baseEnd_3586136] using wordTrace_append hprefix tailTrace_3586136
  have hstable : (prefixWord ++ tailWord_3586136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586136).length < 2 ^ (prefixWord ++ tailWord_3586136).sum := by decide
  have hdescent : baseEnd_3586136 < baseStart_3586136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586140 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3586140 : Nat := 118140960795 + 3586140 * 2 ^ 59
def prefixEnd_3586140 : Nat := 4983230072969 + 3 ^ 40 * 3586140 * 2
def baseEnd_3586140 : Nat := 1227609009543136296305099

theorem tailTrace_3586140 : CollatzResearch.WordTrace tailWord_3586140 prefixEnd_3586140 1227609009543136296305099 := by
  unfold tailWord_3586140
  simp only [CollatzResearch.WordTrace]
  refine ⟨65398635614017359398181937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87198180818689812530909249 65398635614017359398181937)
  ·
    refine ⟨49048976710513019548636453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65398635614017359398181937 49048976710513019548636453)
    ·
      refine ⟨9196683133221191165369335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49048976710513019548636453 9196683133221191165369335)
      ·
        refine ⟨13795024699831786748054003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9196683133221191165369335 13795024699831786748054003)
        ·
          refine ⟨20692537049747680122081005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13795024699831786748054003 20692537049747680122081005)
          ·
            refine ⟨7759701393655380045780377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20692537049747680122081005 7759701393655380045780377)
            ·
              refine ⟨5819776045241535034335283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7759701393655380045780377 5819776045241535034335283)
              ·
                refine ⟨8729664067862302551502925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5819776045241535034335283 8729664067862302551502925)
                ·
                  refine ⟨3273624025448363456813597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8729664067862302551502925 3273624025448363456813597)
                  ·
                    refine ⟨1227609009543136296305099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273624025448363456813597 1227609009543136296305099)
                    ·
                      rfl

theorem cell22_3586140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3586140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586140 prefixEnd_3586140 := by exact prefixLift 3586140
  have htrace : WordTrace (prefixWord ++ tailWord_3586140) baseStart_3586140 baseEnd_3586140 := by
    simpa [prefixWord, tailWord_3586140, baseEnd_3586140] using wordTrace_append hprefix tailTrace_3586140
  have hstable : (prefixWord ++ tailWord_3586140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586140).length < 2 ^ (prefixWord ++ tailWord_3586140).sum := by decide
  have hdescent : baseEnd_3586140 < baseStart_3586140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586151 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 2, 5]
def baseStart_3586151 : Nat := 118140960795 + 3586151 * 2 ^ 59
def prefixEnd_3586151 : Nat := 4983230072969 + 3 ^ 40 * 3586151 * 2
def baseEnd_3586151 : Nat := 1227612775067935934280065

theorem tailTrace_3586151 : CollatzResearch.WordTrace tailWord_3586151 prefixEnd_3586151 1227612775067935934280065 := by
  unfold tailWord_3586151
  simp only [CollatzResearch.WordTrace]
  refine ⟨130797672430994867675014307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87198448287329911783342871 130797672430994867675014307)
  ·
    refine ⟨196196508646492301512521461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130797672430994867675014307 196196508646492301512521461)
    ·
      refine ⟨18393422685608653266798887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196196508646492301512521461 18393422685608653266798887)
      ·
        refine ⟨27590134028412979900198331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18393422685608653266798887 27590134028412979900198331)
        ·
          refine ⟨41385201042619469850297497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27590134028412979900198331 41385201042619469850297497)
          ·
            refine ⟨31038900781964602387723123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41385201042619469850297497 31038900781964602387723123)
            ·
              refine ⟨46558351172946903581584685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31038900781964602387723123 46558351172946903581584685)
              ·
                refine ⟨17459381689855088843094257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46558351172946903581584685 17459381689855088843094257)
                ·
                  refine ⟨13094536267391316632320693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17459381689855088843094257 13094536267391316632320693)
                  ·
                    refine ⟨1227612775067935934280065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13094536267391316632320693 1227612775067935934280065)
                    ·
                      rfl

theorem cell22_3586151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_3586151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586151 prefixEnd_3586151 := by exact prefixLift 3586151
  have htrace : WordTrace (prefixWord ++ tailWord_3586151) baseStart_3586151 baseEnd_3586151 := by
    simpa [prefixWord, tailWord_3586151, baseEnd_3586151] using wordTrace_append hprefix tailTrace_3586151
  have hstable : (prefixWord ++ tailWord_3586151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586151).length < 2 ^ (prefixWord ++ tailWord_3586151).sum := by decide
  have hdescent : baseEnd_3586151 < baseStart_3586151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586153 : List Nat := [1, 2, 1, 1, 1, 5, 5, 1, 5]
def baseStart_3586153 : Nat := 118140960795 + 3586153 * 2 ^ 59
def prefixEnd_3586153 : Nat := 4983230072969 + 3 ^ 40 * 3586153 * 2
def baseEnd_3586153 : Nat := 409204486569602865243353

theorem tailTrace_3586153 : CollatzResearch.WordTrace tailWord_3586153 prefixEnd_3586153 409204486569602865243353 := by
  unfold tailWord_3586153
  simp only [CollatzResearch.WordTrace]
  refine ⟨130797745376987622016587113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87198496917991748011058075 130797745376987622016587113)
  ·
    refine ⟨98098309032740716512440335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130797745376987622016587113 98098309032740716512440335)
    ·
      refine ⟨147147463549111074768660503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98098309032740716512440335 147147463549111074768660503)
      ·
        refine ⟨220721195323666612152990755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147147463549111074768660503 220721195323666612152990755)
        ·
          refine ⟨331081792985499918229486133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220721195323666612152990755 331081792985499918229486133)
          ·
            refine ⟨31038918092390617334014325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 331081792985499918229486133 31038918092390617334014325)
            ·
              refine ⟨2909898571161620375063843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31038918092390617334014325 2909898571161620375063843)
              ·
                refine ⟨4364847856742430562595765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2909898571161620375063843 4364847856742430562595765)
                ·
                  refine ⟨409204486569602865243353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4364847856742430562595765 409204486569602865243353)
                  ·
                    rfl

theorem cell22_3586153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_3586153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586153 prefixEnd_3586153 := by exact prefixLift 3586153
  have htrace : WordTrace (prefixWord ++ tailWord_3586153) baseStart_3586153 baseEnd_3586153 := by
    simpa [prefixWord, tailWord_3586153, baseEnd_3586153] using wordTrace_append hprefix tailTrace_3586153
  have hstable : (prefixWord ++ tailWord_3586153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586153).length < 2 ^ (prefixWord ++ tailWord_3586153).sum := by decide
  have hdescent : baseEnd_3586153 < baseStart_3586153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586183 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 1, 4]
def baseStart_3586183 : Nat := 118140960795 + 3586183 * 2 ^ 59
def prefixEnd_3586183 : Nat := 4983230072969 + 3 ^ 40 * 3586183 * 2
def baseEnd_3586183 : Nat := 1227623729321898517479967

theorem tailTrace_3586183 : CollatzResearch.WordTrace tailWord_3586183 prefixEnd_3586183 1227623729321898517479967 := by
  unfold tailWord_3586183
  simp only [CollatzResearch.WordTrace]
  refine ⟨130798839566878937140179203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87199226377919291426786135 130798839566878937140179203)
  ·
    refine ⟨196198259350318405710268805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130798839566878937140179203 196198259350318405710268805)
    ·
      refine ⟨36787173628184701070675401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196198259350318405710268805 36787173628184701070675401)
      ·
        refine ⟨27590380221138525803006551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36787173628184701070675401 27590380221138525803006551)
        ·
          refine ⟨41385570331707788704509827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27590380221138525803006551 41385570331707788704509827)
          ·
            refine ⟨62078355497561683056764741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41385570331707788704509827 62078355497561683056764741)
            ·
              refine ⟨11639691655792815573143389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62078355497561683056764741 11639691655792815573143389)
              ·
                refine ⟨4364884370922305839928771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11639691655792815573143389 4364884370922305839928771)
                ·
                  refine ⟨6547326556383458759893157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4364884370922305839928771 6547326556383458759893157)
                  ·
                    refine ⟨1227623729321898517479967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6547326556383458759893157 1227623729321898517479967)
                    ·
                      rfl

theorem cell22_3586183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_3586183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586183 prefixEnd_3586183 := by exact prefixLift 3586183
  have htrace : WordTrace (prefixWord ++ tailWord_3586183) baseStart_3586183 baseEnd_3586183 := by
    simpa [prefixWord, tailWord_3586183, baseEnd_3586183] using wordTrace_append hprefix tailTrace_3586183
  have hstable : (prefixWord ++ tailWord_3586183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586183).length < 2 ^ (prefixWord ++ tailWord_3586183).sum := by decide
  have hdescent : baseEnd_3586183 < baseStart_3586183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586226 : List Nat := [3, 2, 1, 1, 1, 3, 1, 10]
def baseStart_3586226 : Nat := 118140960795 + 3586226 * 2 ^ 59
def prefixEnd_3586226 : Nat := 4983230072969 + 3 ^ 40 * 3586226 * 2
def baseEnd_3586226 : Nat := 136404272122295637628315

theorem tailTrace_3586226 : CollatzResearch.WordTrace tailWord_3586226 prefixEnd_3586226 136404272122295637628315 := by
  unfold tailWord_3586226
  simp only [CollatzResearch.WordTrace]
  refine ⟨32700101976430788870998633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87200271937148770322663021 32700101976430788870998633)
  ·
    refine ⟨24525076482323091653248975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32700101976430788870998633 24525076482323091653248975)
    ·
      refine ⟨36787614723484637479873463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24525076482323091653248975 36787614723484637479873463)
      ·
        refine ⟨55181422085226956219810195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36787614723484637479873463 55181422085226956219810195)
        ·
          refine ⟨82772133127840434329715293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55181422085226956219810195 82772133127840434329715293)
          ·
            refine ⟨31039549922940162873643235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82772133127840434329715293 31039549922940162873643235)
            ·
              refine ⟨46559324884410244310464853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31039549922940162873643235 46559324884410244310464853)
              ·
                refine ⟨136404272122295637628315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46559324884410244310464853 136404272122295637628315)
                ·
                  rfl

theorem cell22_3586226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_3586226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586226 prefixEnd_3586226 := by exact prefixLift 3586226
  have htrace : WordTrace (prefixWord ++ tailWord_3586226) baseStart_3586226 baseEnd_3586226 := by
    simpa [prefixWord, tailWord_3586226, baseEnd_3586226] using wordTrace_append hprefix tailTrace_3586226
  have hstable : (prefixWord ++ tailWord_3586226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586226).length < 2 ^ (prefixWord ++ tailWord_3586226).sum := by decide
  have hdescent : baseEnd_3586226 < baseStart_3586226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586271 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 9]
def baseStart_3586271 : Nat := 118140960795 + 3586271 * 2 ^ 59
def prefixEnd_3586271 : Nat := 4983230072969 + 3 ^ 40 * 3586271 * 2
def baseEnd_3586271 : Nat := 409217951173431873759899

theorem tailTrace_3586271 : CollatzResearch.WordTrace tailWord_3586271 prefixEnd_3586271 409217951173431873759899 := by
  unfold tailWord_3586271
  simp only [CollatzResearch.WordTrace]
  refine ⟨130802049190560128169382667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87201366127040085446255111 130802049190560128169382667)
  ·
    refine ⟨196203073785840192254074001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130802049190560128169382667 196203073785840192254074001)
    ·
      refine ⟨147152305339380144190555501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196203073785840192254074001 147152305339380144190555501)
      ·
        refine ⟨55182114502267554071458313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147152305339380144190555501 55182114502267554071458313)
        ·
          refine ⟨41386585876700665553593735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55182114502267554071458313 41386585876700665553593735)
          ·
            refine ⟨62079878815050998330390603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41386585876700665553593735 62079878815050998330390603)
            ·
              refine ⟨93119818222576497495585905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62079878815050998330390603 93119818222576497495585905)
              ·
                refine ⟨69839863666932373121689429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93119818222576497495585905 69839863666932373121689429)
                ·
                  refine ⟨409217951173431873759899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69839863666932373121689429 409217951173431873759899)
                  ·
                    rfl

theorem cell22_3586271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 9].length) (baseStart_3586271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586271 prefixEnd_3586271 := by exact prefixLift 3586271
  have htrace : WordTrace (prefixWord ++ tailWord_3586271) baseStart_3586271 baseEnd_3586271 := by
    simpa [prefixWord, tailWord_3586271, baseEnd_3586271] using wordTrace_append hprefix tailTrace_3586271
  have hstable : (prefixWord ++ tailWord_3586271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586271).length < 2 ^ (prefixWord ++ tailWord_3586271).sum := by decide
  have hdescent : baseEnd_3586271 < baseStart_3586271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586335 : List Nat := [1, 1, 2, 4, 3, 1, 1, 4, 1, 4]
def baseStart_3586335 : Nat := 118140960795 + 3586335 * 2 ^ 59
def prefixEnd_3586335 : Nat := 4983230072969 + 3 ^ 40 * 3586335 * 2
def baseEnd_3586335 : Nat := 1227675762028220787679501

theorem tailTrace_3586335 : CollatzResearch.WordTrace tailWord_3586335 prefixEnd_3586335 1227675762028220787679501 := by
  unfold tailWord_3586335
  simp only [CollatzResearch.WordTrace]
  refine ⟨130804383462328267099712459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87202922308218844733141639 130804383462328267099712459)
  ·
    refine ⟨196206575193492400649568689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130804383462328267099712459 196206575193492400649568689)
    ·
      refine ⟨147154931395119300487176517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196206575193492400649568689 147154931395119300487176517)
      ·
        refine ⟨27591549636584868841345597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147154931395119300487176517 27591549636584868841345597)
        ·
          refine ⟨10346831113719325815504599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27591549636584868841345597 10346831113719325815504599)
          ·
            refine ⟨15520246670578988723256899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10346831113719325815504599 15520246670578988723256899)
            ·
              refine ⟨23280370005868483084885349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15520246670578988723256899 23280370005868483084885349)
              ·
                refine ⟨4365069376100340578416003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23280370005868483084885349 4365069376100340578416003)
                ·
                  refine ⟨6547604064150510867624005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365069376100340578416003 6547604064150510867624005)
                  ·
                    refine ⟨1227675762028220787679501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6547604064150510867624005 1227675762028220787679501)
                    ·
                      rfl

theorem cell22_3586335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_3586335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586335 prefixEnd_3586335 := by exact prefixLift 3586335
  have htrace : WordTrace (prefixWord ++ tailWord_3586335) baseStart_3586335 baseEnd_3586335 := by
    simpa [prefixWord, tailWord_3586335, baseEnd_3586335] using wordTrace_append hprefix tailTrace_3586335
  have hstable : (prefixWord ++ tailWord_3586335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586335).length < 2 ^ (prefixWord ++ tailWord_3586335).sum := by decide
  have hdescent : baseEnd_3586335 < baseStart_3586335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586348 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 1, 5]
def baseStart_3586348 : Nat := 118140960795 + 3586348 * 2 ^ 59
def prefixEnd_3586348 : Nat := 4983230072969 + 3 ^ 40 * 3586348 * 2
def baseEnd_3586348 : Nat := 1227680212193893087104461

theorem tailTrace_3586348 : CollatzResearch.WordTrace tailWord_3586348 prefixEnd_3586348 1227680212193893087104461 := by
  unfold tailWord_3586348
  simp only [CollatzResearch.WordTrace]
  refine ⟨65402428805640585159967849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87203238407520780213290465 65402428805640585159967849)
  ·
    refine ⟨49051821604230438869975887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65402428805640585159967849 49051821604230438869975887)
    ·
      refine ⟨73577732406345658304963831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49051821604230438869975887 73577732406345658304963831)
      ·
        refine ⟨110366598609518487457445747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73577732406345658304963831 110366598609518487457445747)
        ·
          refine ⟨165549897914277731186168621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110366598609518487457445747 165549897914277731186168621)
          ·
            refine ⟨62081211717854149194813233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165549897914277731186168621 62081211717854149194813233)
            ·
              refine ⟨46560908788390611896109925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62081211717854149194813233 46560908788390611896109925)
              ·
                refine ⟨8730170397823239730520611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46560908788390611896109925 8730170397823239730520611)
                ·
                  refine ⟨13095255596734859595780917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730170397823239730520611 13095255596734859595780917)
                  ·
                    refine ⟨1227680212193893087104461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13095255596734859595780917 1227680212193893087104461)
                    ·
                      rfl

theorem cell22_3586348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_3586348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586348 prefixEnd_3586348 := by exact prefixLift 3586348
  have htrace : WordTrace (prefixWord ++ tailWord_3586348) baseStart_3586348 baseEnd_3586348 := by
    simpa [prefixWord, tailWord_3586348, baseEnd_3586348] using wordTrace_append hprefix tailTrace_3586348
  have hstable : (prefixWord ++ tailWord_3586348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586348).length < 2 ^ (prefixWord ++ tailWord_3586348).sum := by decide
  have hdescent : baseEnd_3586348 < baseStart_3586348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586367 : List Nat := [1, 1, 2, 2, 4, 1, 5, 2, 4]
def baseStart_3586367 : Nat := 118140960795 + 3586367 * 2 ^ 59
def prefixEnd_3586367 : Nat := 4983230072969 + 3 ^ 40 * 3586367 * 2
def baseEnd_3586367 : Nat := 409228905427394456959801

theorem tailTrace_3586367 : CollatzResearch.WordTrace tailWord_3586367 prefixEnd_3586367 409228905427394456959801 := by
  unfold tailWord_3586367
  simp only [CollatzResearch.WordTrace]
  refine ⟨130805550598212336564877355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87203700398808224376584903 130805550598212336564877355)
  ·
    refine ⟨196208325897318504847316033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130805550598212336564877355 196208325897318504847316033)
    ·
      refine ⟨147156244422988878635487025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196208325897318504847316033 147156244422988878635487025)
      ·
        refine ⟨110367183317241658976615269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147156244422988878635487025 110367183317241658976615269)
        ·
          refine ⟨20693846871982811058115363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110367183317241658976615269 20693846871982811058115363)
          ·
            refine ⟨31040770307974216587173045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20693846871982811058115363 31040770307974216587173045)
            ·
              refine ⟨2910072216372582805047473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31040770307974216587173045 2910072216372582805047473)
              ·
                refine ⟨2182554162279437103785605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910072216372582805047473 2182554162279437103785605)
                ·
                  refine ⟨409228905427394456959801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2182554162279437103785605 409228905427394456959801)
                  ·
                    rfl

theorem cell22_3586367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 4].length) (baseStart_3586367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586367 prefixEnd_3586367 := by exact prefixLift 3586367
  have htrace : WordTrace (prefixWord ++ tailWord_3586367) baseStart_3586367 baseEnd_3586367 := by
    simpa [prefixWord, tailWord_3586367, baseEnd_3586367] using wordTrace_append hprefix tailTrace_3586367
  have hstable : (prefixWord ++ tailWord_3586367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586367).length < 2 ^ (prefixWord ++ tailWord_3586367).sum := by decide
  have hdescent : baseEnd_3586367 < baseStart_3586367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586440 : List Nat := [2, 1, 3, 3, 1, 1, 1, 5, 5]
def baseStart_3586440 : Nat := 118140960795 + 3586440 * 2 ^ 59
def prefixEnd_3586440 : Nat := 4983230072969 + 3 ^ 40 * 3586440 * 2
def baseEnd_3586440 : Nat := 409237235224678504601393

theorem tailTrace_3586440 : CollatzResearch.WordTrace tailWord_3586440 prefixEnd_3586440 409237235224678504601393 := by
  unfold tailWord_3586440
  simp only [CollatzResearch.WordTrace]
  refine ⟨65404106563473935016142387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87205475417965246688189849 65404106563473935016142387)
  ·
    refine ⟨98106159845210902524213581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65404106563473935016142387 98106159845210902524213581)
    ·
      refine ⟨36789809941954088446580093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98106159845210902524213581 36789809941954088446580093)
      ·
        refine ⟨13796178728232783167467535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36789809941954088446580093 13796178728232783167467535)
        ·
          refine ⟨20694268092349174751201303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13796178728232783167467535 20694268092349174751201303)
          ·
            refine ⟨31041402138523762126801955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20694268092349174751201303 31041402138523762126801955)
            ·
              refine ⟨46562103207785643190202933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31041402138523762126801955 46562103207785643190202933)
              ·
                refine ⟨4365197175729904049081525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46562103207785643190202933 4365197175729904049081525)
                ·
                  refine ⟨409237235224678504601393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4365197175729904049081525 409237235224678504601393)
                  ·
                    rfl

theorem cell22_3586440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 5, 5].length) (baseStart_3586440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586440 prefixEnd_3586440 := by exact prefixLift 3586440
  have htrace : WordTrace (prefixWord ++ tailWord_3586440) baseStart_3586440 baseEnd_3586440 := by
    simpa [prefixWord, tailWord_3586440, baseEnd_3586440] using wordTrace_append hprefix tailTrace_3586440
  have hstable : (prefixWord ++ tailWord_3586440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586440).length < 2 ^ (prefixWord ++ tailWord_3586440).sum := by decide
  have hdescent : baseEnd_3586440 < baseStart_3586440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586461 : List Nat := [1, 4, 2, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3586461 : Nat := 118140960795 + 3586461 * 2 ^ 59
def prefixEnd_3586461 : Nat := 4983230072969 + 3 ^ 40 * 3586461 * 2
def baseEnd_3586461 : Nat := 1227718894403198459029115

theorem tailTrace_3586461 : CollatzResearch.WordTrace tailWord_3586461 prefixEnd_3586461 1227718894403198459029115 := by
  unfold tailWord_3586461
  simp only [CollatzResearch.WordTrace]
  refine ⟨130808979059871790618799237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87205986039914527079199491 130808979059871790618799237)
  ·
    refine ⟨24526683573725960741024857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130808979059871790618799237 24526683573725960741024857)
    ·
      refine ⟨18395012680294470555768643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24526683573725960741024857 18395012680294470555768643)
      ·
        refine ⟨27592519020441705833652965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18395012680294470555768643 27592519020441705833652965)
        ·
          refine ⟨5173597316332819843809931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27592519020441705833652965 5173597316332819843809931)
          ·
            refine ⟨7760395974499229765714897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5173597316332819843809931 7760395974499229765714897)
            ·
              refine ⟨5820296980874422324286173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760395974499229765714897 5820296980874422324286173)
              ·
                refine ⟨2182611367827908371607315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820296980874422324286173 2182611367827908371607315)
                ·
                  refine ⟨3273917051741862557410973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182611367827908371607315 3273917051741862557410973)
                  ·
                    refine ⟨1227718894403198459029115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273917051741862557410973 1227718894403198459029115)
                    ·
                      rfl

theorem cell22_3586461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3586461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586461 prefixEnd_3586461 := by exact prefixLift 3586461
  have htrace : WordTrace (prefixWord ++ tailWord_3586461) baseStart_3586461 baseEnd_3586461 := by
    simpa [prefixWord, tailWord_3586461, baseEnd_3586461] using wordTrace_append hprefix tailTrace_3586461
  have hstable : (prefixWord ++ tailWord_3586461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586461).length < 2 ^ (prefixWord ++ tailWord_3586461).sum := by decide
  have hdescent : baseEnd_3586461 < baseStart_3586461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586472 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3586472 : Nat := 118140960795 + 3586472 * 2 ^ 59
def prefixEnd_3586472 : Nat := 4983230072969 + 3 ^ 40 * 3586472 * 2
def baseEnd_3586472 : Nat := 1227722659927998097004081

theorem tailTrace_3586472 : CollatzResearch.WordTrace tailWord_3586472 prefixEnd_3586472 1227722659927998097004081 := by
  unfold tailWord_3586472
  simp only [CollatzResearch.WordTrace]
  refine ⟨65404690131415969748724835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87206253508554626331633113 65404690131415969748724835)
  ·
    refine ⟨98107035197123954623087253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65404690131415969748724835 98107035197123954623087253)
    ·
      refine ⟨4598767274865185372957215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98107035197123954623087253 4598767274865185372957215)
      ·
        refine ⟨6898150912297778059435823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4598767274865185372957215 6898150912297778059435823)
        ·
          refine ⟨10347226368446667089153735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6898150912297778059435823 10347226368446667089153735)
          ·
            refine ⟨15520839552670000633730603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10347226368446667089153735 15520839552670000633730603)
            ·
              refine ⟨23281259329005000950595905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15520839552670000633730603 23281259329005000950595905)
              ·
                refine ⟨17460944496753750712946929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23281259329005000950595905 17460944496753750712946929)
                ·
                  refine ⟨13095708372565313034710197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17460944496753750712946929 13095708372565313034710197)
                  ·
                    refine ⟨1227722659927998097004081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13095708372565313034710197 1227722659927998097004081)
                    ·
                      rfl

theorem cell22_3586472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3586472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586472 prefixEnd_3586472 := by exact prefixLift 3586472
  have htrace : WordTrace (prefixWord ++ tailWord_3586472) baseStart_3586472 baseEnd_3586472 := by
    simpa [prefixWord, tailWord_3586472, baseEnd_3586472] using wordTrace_append hprefix tailTrace_3586472
  have hstable : (prefixWord ++ tailWord_3586472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586472).length < 2 ^ (prefixWord ++ tailWord_3586472).sum := by decide
  have hdescent : baseEnd_3586472 < baseStart_3586472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586483 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 9]
def baseStart_3586483 : Nat := 118140960795 + 3586483 * 2 ^ 59
def prefixEnd_3586483 : Nat := 4983230072969 + 3 ^ 40 * 3586483 * 2
def baseEnd_3586483 : Nat := 1227726425452797734979047

theorem tailTrace_3586483 : CollatzResearch.WordTrace tailWord_3586483 prefixEnd_3586483 1227726425452797734979047 := by
  unfold tailWord_3586483
  simp only [CollatzResearch.WordTrace]
  refine ⟨130809781465792088376100103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87206520977194725584066735 130809781465792088376100103)
  ·
    refine ⟨196214672198688132564150155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130809781465792088376100103 196214672198688132564150155)
    ·
      refine ⟨294322008298032198846225233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196214672198688132564150155 294322008298032198846225233)
      ·
        refine ⟨220741506223524149134668925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294322008298032198846225233 220741506223524149134668925)
        ·
          refine ⟨82778064833821555925500847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220741506223524149134668925 82778064833821555925500847)
          ·
            refine ⟨124167097250732333888251271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82778064833821555925500847 124167097250732333888251271)
            ·
              refine ⟨186250645876098500832376907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124167097250732333888251271 186250645876098500832376907)
              ·
                refine ⟨279375968814147751248565361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186250645876098500832376907 279375968814147751248565361)
                ·
                  refine ⟨209531976610610813436424021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 279375968814147751248565361 209531976610610813436424021)
                  ·
                    refine ⟨1227726425452797734979047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 209531976610610813436424021 1227726425452797734979047)
                    ·
                      rfl

theorem cell22_3586483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_3586483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586483 prefixEnd_3586483 := by exact prefixLift 3586483
  have htrace : WordTrace (prefixWord ++ tailWord_3586483) baseStart_3586483 baseEnd_3586483 := by
    simpa [prefixWord, tailWord_3586483, baseEnd_3586483] using wordTrace_append hprefix tailTrace_3586483
  have hstable : (prefixWord ++ tailWord_3586483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586483).length < 2 ^ (prefixWord ++ tailWord_3586483).sum := by decide
  have hdescent : baseEnd_3586483 < baseStart_3586483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586517 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_3586517 : Nat := 118140960795 + 3586517 * 2 ^ 59
def prefixEnd_3586517 : Nat := 4983230072969 + 3 ^ 40 * 3586517 * 2
def baseEnd_3586517 : Nat := 1227738064347632979628943

theorem tailTrace_3586517 : CollatzResearch.WordTrace tailWord_3586517 prefixEnd_3586517 1227738064347632979628943 := by
  unfold tailWord_3586517
  simp only [CollatzResearch.WordTrace]
  refine ⟨130811021547668912182837805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87207347698445941455225203 130811021547668912182837805)
  ·
    refine ⟨49054133080375842068564177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130811021547668912182837805 49054133080375842068564177)
    ·
      refine ⟨36790599810281881551423133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49054133080375842068564177 36790599810281881551423133)
      ·
        refine ⟨13796474928855705581783675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36790599810281881551423133 13796474928855705581783675)
        ·
          refine ⟨20694712393283558372675513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13796474928855705581783675 20694712393283558372675513)
          ·
            refine ⟨15521034294962668779506635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20694712393283558372675513 15521034294962668779506635)
            ·
              refine ⟨23281551442444003169259953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15521034294962668779506635 23281551442444003169259953)
              ·
                refine ⟨17461163581833002376944965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23281551442444003169259953 17461163581833002376944965)
                ·
                  refine ⟨3273968171593687945677181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17461163581833002376944965 3273968171593687945677181)
                  ·
                    refine ⟨1227738064347632979628943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3273968171593687945677181 1227738064347632979628943)
                    ·
                      rfl

theorem cell22_3586517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_3586517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586517 prefixEnd_3586517 := by exact prefixLift 3586517
  have htrace : WordTrace (prefixWord ++ tailWord_3586517) baseStart_3586517 baseEnd_3586517 := by
    simpa [prefixWord, tailWord_3586517, baseEnd_3586517] using wordTrace_append hprefix tailTrace_3586517
  have hstable : (prefixWord ++ tailWord_3586517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586517).length < 2 ^ (prefixWord ++ tailWord_3586517).sum := by decide
  have hdescent : baseEnd_3586517 < baseStart_3586517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586579 : List Nat := [1, 1, 1, 2, 1, 5, 2, 5, 1, 3]
def baseStart_3586579 : Nat := 118140960795 + 3586579 * 2 ^ 59
def prefixEnd_3586579 : Nat := 4983230072969 + 3 ^ 40 * 3586579 * 2
def baseEnd_3586579 : Nat := 1227759288214685484578753

theorem tailTrace_3586579 : CollatzResearch.WordTrace tailWord_3586579 prefixEnd_3586579 1227759288214685484578753 := by
  unfold tailWord_3586579
  simp only [CollatzResearch.WordTrace]
  refine ⟨130813282873444296771594791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87208855248962864514396527 130813282873444296771594791)
  ·
    refine ⟨196219924310166445157392187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130813282873444296771594791 196219924310166445157392187)
    ·
      refine ⟨294329886465249667736088281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196219924310166445157392187 294329886465249667736088281)
      ·
        refine ⟨220747414848937250802066211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294329886465249667736088281 220747414848937250802066211)
        ·
          refine ⟨331121122273405876203099317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220747414848937250802066211 331121122273405876203099317)
          ·
            refine ⟨31042605213131800894040561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 331121122273405876203099317 31042605213131800894040561)
            ·
              refine ⟨23281953909848850670530421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31042605213131800894040561 23281953909848850670530421)
              ·
                refine ⟨2182683179048329750362227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23281953909848850670530421 2182683179048329750362227)
                ·
                  refine ⟨3274024768572494625543341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182683179048329750362227 3274024768572494625543341)
                  ·
                    refine ⟨1227759288214685484578753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274024768572494625543341 1227759288214685484578753)
                    ·
                      rfl

theorem cell22_3586579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 5, 1, 3].length) (baseStart_3586579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586579 prefixEnd_3586579 := by exact prefixLift 3586579
  have htrace : WordTrace (prefixWord ++ tailWord_3586579) baseStart_3586579 baseEnd_3586579 := by
    simpa [prefixWord, tailWord_3586579, baseEnd_3586579] using wordTrace_append hprefix tailTrace_3586579
  have hstable : (prefixWord ++ tailWord_3586579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586579).length < 2 ^ (prefixWord ++ tailWord_3586579).sum := by decide
  have hdescent : baseEnd_3586579 < baseStart_3586579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586630 : List Nat := [6, 1, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3586630 : Nat := 118140960795 + 3586630 * 2 ^ 59
def prefixEnd_3586630 : Nat := 4983230072969 + 3 ^ 40 * 3586630 * 2
def baseEnd_3586630 : Nat := 1227776746556938351553597

theorem tailTrace_3586630 : CollatzResearch.WordTrace tailWord_3586630 prefixEnd_3586630 1227776746556938351553597 := by
  unfold tailWord_3586630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4087973218633110390053167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87210095330839688321134229 4087973218633110390053167)
  ·
    refine ⟨6131959827949665585079751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4087973218633110390053167 6131959827949665585079751)
    ·
      refine ⟨9197939741924498377619627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6131959827949665585079751 9197939741924498377619627)
      ·
        refine ⟨13796909612886747566429441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9197939741924498377619627 13796909612886747566429441)
        ·
          refine ⟨10347682209665060674822081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13796909612886747566429441 10347682209665060674822081)
          ·
            refine ⟨7760761657248795506116561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10347682209665060674822081 7760761657248795506116561)
            ·
              refine ⟨5820571242936596629587421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7760761657248795506116561 5820571242936596629587421)
              ·
                refine ⟨2182714216101223736095283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5820571242936596629587421 2182714216101223736095283)
                ·
                  refine ⟨3274071324151835604142925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182714216101223736095283 3274071324151835604142925)
                  ·
                    refine ⟨1227776746556938351553597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274071324151835604142925 1227776746556938351553597)
                    ·
                      rfl

theorem cell22_3586630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3586630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586630 prefixEnd_3586630 := by exact prefixLift 3586630
  have htrace : WordTrace (prefixWord ++ tailWord_3586630) baseStart_3586630 baseEnd_3586630 := by
    simpa [prefixWord, tailWord_3586630, baseEnd_3586630] using wordTrace_append hprefix tailTrace_3586630
  have hstable : (prefixWord ++ tailWord_3586630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586630).length < 2 ^ (prefixWord ++ tailWord_3586630).sum := by decide
  have hdescent : baseEnd_3586630 < baseStart_3586630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586639 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 1, 4]
def baseStart_3586639 : Nat := 118140960795 + 3586639 * 2 ^ 59
def prefixEnd_3586639 : Nat := 4983230072969 + 3 ^ 40 * 3586639 * 2
def baseEnd_3586639 : Nat := 1227779827440865328078569

theorem tailTrace_3586639 : CollatzResearch.WordTrace tailWord_3586639 prefixEnd_3586639 1227779827440865328078569 := by
  unfold tailWord_3586639
  simp only [CollatzResearch.WordTrace]
  refine ⟨130815471253226927018778971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87210314168817951345852647 130815471253226927018778971)
  ·
    refine ⟨196223206879840390528168457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130815471253226927018778971 196223206879840390528168457)
    ·
      refine ⟨147167405159880292896126343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196223206879840390528168457 147167405159880292896126343)
      ·
        refine ⟨220751107739820439344189515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147167405159880292896126343 220751107739820439344189515)
        ·
          refine ⟨331126661609730659016284273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220751107739820439344189515 331126661609730659016284273)
          ·
            refine ⟨248344996207297994262213205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331126661609730659016284273 248344996207297994262213205)
            ·
              refine ⟨2910292924304273370260311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 248344996207297994262213205 2910292924304273370260311)
              ·
                refine ⟨4365439386456410055390467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910292924304273370260311 4365439386456410055390467)
                ·
                  refine ⟨6548159079684615083085701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4365439386456410055390467 6548159079684615083085701)
                  ·
                    refine ⟨1227779827440865328078569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6548159079684615083085701 1227779827440865328078569)
                    ·
                      rfl

theorem cell22_3586639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 4].length) (baseStart_3586639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586639 prefixEnd_3586639 := by exact prefixLift 3586639
  have htrace : WordTrace (prefixWord ++ tailWord_3586639) baseStart_3586639 baseEnd_3586639 := by
    simpa [prefixWord, tailWord_3586639, baseEnd_3586639] using wordTrace_append hprefix tailTrace_3586639
  have hstable : (prefixWord ++ tailWord_3586639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586639).length < 2 ^ (prefixWord ++ tailWord_3586639).sum := by decide
  have hdescent : baseEnd_3586639 < baseStart_3586639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586665 : List Nat := [1, 2, 1, 1, 1, 4, 1, 11]
def baseStart_3586665 : Nat := 118140960795 + 3586665 * 2 ^ 59
def prefixEnd_3586665 : Nat := 4983230072969 + 3 ^ 40 * 3586665 * 2
def baseEnd_3586665 : Nat := 136420969752467769658721

theorem tailTrace_3586665 : CollatzResearch.WordTrace tailWord_3586665 prefixEnd_3586665 136420969752467769658721 := by
  unfold tailWord_3586665
  simp only [CollatzResearch.WordTrace]
  refine ⟨130816419551132733459225449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87210946367421822306150299 130816419551132733459225449)
  ·
    refine ⟨98112314663349550094419087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130816419551132733459225449 98112314663349550094419087)
    ·
      refine ⟨147168471995024325141628631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98112314663349550094419087 147168471995024325141628631)
      ·
        refine ⟨220752707992536487712442947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147168471995024325141628631 220752707992536487712442947)
        ·
          refine ⟨331129061988804731568664421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220752707992536487712442947 331129061988804731568664421)
          ·
            refine ⟨62086699122900887169124579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331129061988804731568664421 62086699122900887169124579)
            ·
              refine ⟨93130048684351330753686869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62086699122900887169124579 93130048684351330753686869)
              ·
                refine ⟨136420969752467769658721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93130048684351330753686869 136420969752467769658721)
                ·
                  rfl

theorem cell22_3586665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 11].length) (baseStart_3586665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586665 prefixEnd_3586665 := by exact prefixLift 3586665
  have htrace : WordTrace (prefixWord ++ tailWord_3586665) baseStart_3586665 baseEnd_3586665 := by
    simpa [prefixWord, tailWord_3586665, baseEnd_3586665] using wordTrace_append hprefix tailTrace_3586665
  have hstable : (prefixWord ++ tailWord_3586665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586665).length < 2 ^ (prefixWord ++ tailWord_3586665).sum := by decide
  have hdescent : baseEnd_3586665 < baseStart_3586665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586669 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_3586669 : Nat := 118140960795 + 3586669 * 2 ^ 59
def prefixEnd_3586669 : Nat := 4983230072969 + 3 ^ 40 * 3586669 * 2
def baseEnd_3586669 : Nat := 1227790097053955249828477

theorem tailTrace_3586669 : CollatzResearch.WordTrace tailWord_3586669 prefixEnd_3586669 1227790097053955249828477 := by
  unfold tailWord_3586669
  simp only [CollatzResearch.WordTrace]
  refine ⟨130816565443118242142371061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87211043628745494761580707 130816565443118242142371061)
  ·
    refine ⟨12264053010292335200847287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130816565443118242142371061 12264053010292335200847287)
    ·
      refine ⟨18396079515438502801270931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12264053010292335200847287 18396079515438502801270931)
      ·
        refine ⟨27594119273157754201906397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18396079515438502801270931 27594119273157754201906397)
        ·
          refine ⟨10347794727434157825714899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27594119273157754201906397 10347794727434157825714899)
          ·
            refine ⟨15521692091151236738572349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10347794727434157825714899 15521692091151236738572349)
            ·
              refine ⟨5820634534181713776964631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15521692091151236738572349 5820634534181713776964631)
              ·
                refine ⟨8730951801272570665446947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5820634534181713776964631 8730951801272570665446947)
                ·
                  refine ⟨13096427701908855998170421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8730951801272570665446947 13096427701908855998170421)
                  ·
                    refine ⟨1227790097053955249828477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13096427701908855998170421 1227790097053955249828477)
                    ·
                      rfl

theorem cell22_3586669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_3586669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586669 prefixEnd_3586669 := by exact prefixLift 3586669
  have htrace : WordTrace (prefixWord ++ tailWord_3586669) baseStart_3586669 baseEnd_3586669 := by
    simpa [prefixWord, tailWord_3586669, baseEnd_3586669] using wordTrace_append hprefix tailTrace_3586669
  have hstable : (prefixWord ++ tailWord_3586669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586669).length < 2 ^ (prefixWord ++ tailWord_3586669).sum := by decide
  have hdescent : baseEnd_3586669 < baseStart_3586669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586712 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 2, 6]
def baseStart_3586712 : Nat := 118140960795 + 3586712 * 2 ^ 59
def prefixEnd_3586712 : Nat := 4983230072969 + 3 ^ 40 * 3586712 * 2
def baseEnd_3586712 : Nat := 1227804816832717471003345

theorem tailTrace_3586712 : CollatzResearch.WordTrace tailWord_3586712 prefixEnd_3586712 1227804816832717471003345 := by
  unfold tailWord_3586712
  simp only [CollatzResearch.WordTrace]
  refine ⟨65409066890981230243093195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87212089187974973657457593 65409066890981230243093195)
  ·
    refine ⟨98113600336471845364639793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65409066890981230243093195 98113600336471845364639793)
    ·
      refine ⟨73585200252353884023479845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98113600336471845364639793 73585200252353884023479845)
      ·
        refine ⟨13797225047316353254402471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73585200252353884023479845 13797225047316353254402471)
        ·
          refine ⟨20695837570974529881603707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13797225047316353254402471 20695837570974529881603707)
          ·
            refine ⟨31043756356461794822405561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20695837570974529881603707 31043756356461794822405561)
            ·
              refine ⟨23282817267346346116804171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31043756356461794822405561 23282817267346346116804171)
              ·
                refine ⟨34924225901019519175206257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23282817267346346116804171 34924225901019519175206257)
                ·
                  refine ⟨26193169425764639381404693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34924225901019519175206257 26193169425764639381404693)
                  ·
                    refine ⟨1227804816832717471003345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26193169425764639381404693 1227804816832717471003345)
                    ·
                      rfl

theorem cell22_3586712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_3586712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586712 prefixEnd_3586712 := by exact prefixLift 3586712
  have htrace : WordTrace (prefixWord ++ tailWord_3586712) baseStart_3586712 baseEnd_3586712 := by
    simpa [prefixWord, tailWord_3586712, baseEnd_3586712] using wordTrace_append hprefix tailTrace_3586712
  have hstable : (prefixWord ++ tailWord_3586712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586712).length < 2 ^ (prefixWord ++ tailWord_3586712).sum := by decide
  have hdescent : baseEnd_3586712 < baseStart_3586712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586720 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 2, 3]
def baseStart_3586720 : Nat := 118140960795 + 3586720 * 2 ^ 59
def prefixEnd_3586720 : Nat := 4983230072969 + 3 ^ 40 * 3586720 * 2
def baseEnd_3586720 : Nat := 1227807555396208116803321

theorem tailTrace_3586720 : CollatzResearch.WordTrace tailWord_3586720 prefixEnd_3586720 1227807555396208116803321 := by
  unfold tailWord_3586720
  simp only [CollatzResearch.WordTrace]
  refine ⟨65409212782966738926238807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87212283710622318568318409 65409212782966738926238807)
  ·
    refine ⟨98113819174450108389358211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65409212782966738926238807 98113819174450108389358211)
    ·
      refine ⟨147170728761675162584037317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98113819174450108389358211 147170728761675162584037317)
      ·
        refine ⟨27594511642814092984506997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147170728761675162584037317 27594511642814092984506997)
        ·
          refine ⟨2586985466513821217297531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27594511642814092984506997 2586985466513821217297531)
          ·
            refine ⟨3880478199770731825946297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2586985466513821217297531 3880478199770731825946297)
            ·
              refine ⟨2910358649828048869459723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880478199770731825946297 2910358649828048869459723)
              ·
                refine ⟨4365537974742073304189585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910358649828048869459723 4365537974742073304189585)
                ·
                  refine ⟨3274153481056554978142189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4365537974742073304189585 3274153481056554978142189)
                  ·
                    refine ⟨1227807555396208116803321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274153481056554978142189 1227807555396208116803321)
                    ·
                      rfl

theorem cell22_3586720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 3].length) (baseStart_3586720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586720 prefixEnd_3586720 := by exact prefixLift 3586720
  have htrace : WordTrace (prefixWord ++ tailWord_3586720) baseStart_3586720 baseEnd_3586720 := by
    simpa [prefixWord, tailWord_3586720, baseEnd_3586720] using wordTrace_append hprefix tailTrace_3586720
  have hstable : (prefixWord ++ tailWord_3586720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586720).length < 2 ^ (prefixWord ++ tailWord_3586720).sum := by decide
  have hdescent : baseEnd_3586720 < baseStart_3586720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586757 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_3586757 : Nat := 118140960795 + 3586757 * 2 ^ 59
def prefixEnd_3586757 : Nat := 4983230072969 + 3 ^ 40 * 3586757 * 2
def baseEnd_3586757 : Nat := 1227820221252352353628207

theorem tailTrace_3586757 : CollatzResearch.WordTrace tailWord_3586757 prefixEnd_3586757 1227820221252352353628207 := by
  unfold tailWord_3586757
  simp only [CollatzResearch.WordTrace]
  refine ⟨130819775066799433171574525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87213183377866288781049683 130819775066799433171574525)
  ·
    refine ⟨49057415650049787439340447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130819775066799433171574525 49057415650049787439340447)
    ·
      refine ⟨73586123475074681159010671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49057415650049787439340447 73586123475074681159010671)
      ·
        refine ⟨110379185212612021738516007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73586123475074681159010671 110379185212612021738516007)
        ·
          refine ⟨165568777818918032607774011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110379185212612021738516007 165568777818918032607774011)
          ·
            refine ⟨248353166728377048911661017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165568777818918032607774011 248353166728377048911661017)
            ·
              refine ⟨186264875046282786683745763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248353166728377048911661017 186264875046282786683745763)
              ·
                refine ⟨279397312569424180025618645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186264875046282786683745763 279397312569424180025618645)
                ·
                  refine ⟨6548374513345879219350437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 279397312569424180025618645 6548374513345879219350437)
                  ·
                    refine ⟨1227820221252352353628207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6548374513345879219350437 1227820221252352353628207)
                    ·
                      rfl

theorem cell22_3586757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_3586757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586757 prefixEnd_3586757 := by exact prefixLift 3586757
  have htrace : WordTrace (prefixWord ++ tailWord_3586757) baseStart_3586757 baseEnd_3586757 := by
    simpa [prefixWord, tailWord_3586757, baseEnd_3586757] using wordTrace_append hprefix tailTrace_3586757
  have hstable : (prefixWord ++ tailWord_3586757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586757).length < 2 ^ (prefixWord ++ tailWord_3586757).sum := by decide
  have hdescent : baseEnd_3586757 < baseStart_3586757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586789 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 6]
def baseStart_3586789 : Nat := 118140960795 + 3586789 * 2 ^ 59
def prefixEnd_3586789 : Nat := 4983230072969 + 3 ^ 40 * 3586789 * 2
def baseEnd_3586789 : Nat := 409277058502104978942703

theorem tailTrace_3586789 : CollatzResearch.WordTrace tailWord_3586789 prefixEnd_3586789 409277058502104978942703 := by
  unfold tailWord_3586789
  simp only [CollatzResearch.WordTrace]
  refine ⟨130820942202683502636739421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87213961468455668424492947 130820942202683502636739421)
  ·
    refine ⟨49057853326006313488777283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130820942202683502636739421 49057853326006313488777283)
    ·
      refine ⟨73586779989009470233165925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49057853326006313488777283 73586779989009470233165925)
      ·
        refine ⟨13797521247939275668718611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73586779989009470233165925 13797521247939275668718611)
        ·
          refine ⟨20696281871908913503077917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13797521247939275668718611 20696281871908913503077917)
          ·
            refine ⟨7761105701965842563654219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20696281871908913503077917 7761105701965842563654219)
            ·
              refine ⟨11641658552948763845481329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7761105701965842563654219 11641658552948763845481329)
              ·
                refine ⟨8731243914711572884110997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11641658552948763845481329 8731243914711572884110997)
                ·
                  refine ⟨409277058502104978942703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8731243914711572884110997 409277058502104978942703)
                  ·
                    rfl

theorem cell22_3586789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_3586789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586789 prefixEnd_3586789 := by exact prefixLift 3586789
  have htrace : WordTrace (prefixWord ++ tailWord_3586789) baseStart_3586789 baseEnd_3586789 := by
    simpa [prefixWord, tailWord_3586789, baseEnd_3586789] using wordTrace_append hprefix tailTrace_3586789
  have hstable : (prefixWord ++ tailWord_3586789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586789).length < 2 ^ (prefixWord ++ tailWord_3586789).sum := by decide
  have hdescent : baseEnd_3586789 < baseStart_3586789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586868 : List Nat := [2, 5, 1, 1, 4, 1, 8]
def baseStart_3586868 : Nat := 118140960795 + 3586868 * 2 ^ 59
def prefixEnd_3586868 : Nat := 4983230072969 + 3 ^ 40 * 3586868 * 2
def baseEnd_3586868 : Nat := 45476230326695743114921

theorem tailTrace_3586868 : CollatzResearch.WordTrace tailWord_3586868 prefixEnd_3586868 45476230326695743114921 := by
  unfold tailWord_3586868
  simp only [CollatzResearch.WordTrace]
  refine ⟨65411911784698649564432629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87215882379598199419243505 65411911784698649564432629)
  ·
    refine ⟨6132366729815498396665559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65411911784698649564432629 6132366729815498396665559)
    ·
      refine ⟨9198550094723247594998339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6132366729815498396665559 9198550094723247594998339)
      ·
        refine ⟨13797825142084871392497509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9198550094723247594998339 13797825142084871392497509)
        ·
          refine ⟨2587092214140913386093283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13797825142084871392497509 2587092214140913386093283)
          ·
            refine ⟨3880638321211370079139925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587092214140913386093283 3880638321211370079139925)
            ·
              refine ⟨45476230326695743114921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3880638321211370079139925 45476230326695743114921)
              ·
                rfl

theorem cell22_3586868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 8].length) (baseStart_3586868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586868 prefixEnd_3586868 := by exact prefixLift 3586868
  have htrace : WordTrace (prefixWord ++ tailWord_3586868) baseStart_3586868 baseEnd_3586868 := by
    simpa [prefixWord, tailWord_3586868, baseEnd_3586868] using wordTrace_append hprefix tailTrace_3586868
  have hstable : (prefixWord ++ tailWord_3586868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586868).length < 2 ^ (prefixWord ++ tailWord_3586868).sum := by decide
  have hdescent : baseEnd_3586868 < baseStart_3586868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586879 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 7]
def baseStart_3586879 : Nat := 118140960795 + 3586879 * 2 ^ 59
def prefixEnd_3586879 : Nat := 4983230072969 + 3 ^ 40 * 3586879 * 2
def baseEnd_3586879 : Nat := 409287328115194900692611

theorem tailTrace_3586879 : CollatzResearch.WordTrace tailWord_3586879 prefixEnd_3586879 409287328115194900692611 := by
  unfold tailWord_3586879
  simp only [CollatzResearch.WordTrace]
  refine ⟨130824224772357448007515691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87216149848238298671677127 130824224772357448007515691)
  ·
    refine ⟨196236337158536172011273537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130824224772357448007515691 196236337158536172011273537)
    ·
      refine ⟨147177252868902129008455153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196236337158536172011273537 147177252868902129008455153)
      ·
        refine ⟨110382939651676596756341365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147177252868902129008455153 110382939651676596756341365)
        ·
          refine ⟨10348400592344680945907003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110382939651676596756341365 10348400592344680945907003)
          ·
            refine ⟨15522600888517021418860505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10348400592344680945907003 15522600888517021418860505)
            ·
              refine ⟨11641950666387766064145379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15522600888517021418860505 11641950666387766064145379)
              ·
                refine ⟨17462925999581649096218069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11641950666387766064145379 17462925999581649096218069)
                ·
                  refine ⟨409287328115194900692611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17462925999581649096218069 409287328115194900692611)
                  ·
                    rfl

theorem cell22_3586879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 7].length) (baseStart_3586879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586879 prefixEnd_3586879 := by exact prefixLift 3586879
  have htrace : WordTrace (prefixWord ++ tailWord_3586879) baseStart_3586879 baseEnd_3586879 := by
    simpa [prefixWord, tailWord_3586879, baseEnd_3586879] using wordTrace_append hprefix tailTrace_3586879
  have hstable : (prefixWord ++ tailWord_3586879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586879).length < 2 ^ (prefixWord ++ tailWord_3586879).sum := by decide
  have hdescent : baseEnd_3586879 < baseStart_3586879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586894 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_3586894 : Nat := 118140960795 + 3586894 * 2 ^ 59
def prefixEnd_3586894 : Nat := 4983230072969 + 3 ^ 40 * 3586894 * 2
def baseEnd_3586894 : Nat := 1227867119152129662952787

theorem tailTrace_3586894 : CollatzResearch.WordTrace tailWord_3586894 prefixEnd_3586894 1227867119152129662952787 := by
  unfold tailWord_3586894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16353096483412888196163967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87216514578202070379541157 16353096483412888196163967)
  ·
    refine ⟨24529644725119332294245951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16353096483412888196163967 24529644725119332294245951)
    ·
      refine ⟨36794467087678998441368927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24529644725119332294245951 36794467087678998441368927)
      ·
        refine ⟨55191700631518497662053391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36794467087678998441368927 55191700631518497662053391)
        ·
          refine ⟨82787550947277746493080087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55191700631518497662053391 82787550947277746493080087)
          ·
            refine ⟨124181326420916619739620131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82787550947277746493080087 124181326420916619739620131)
            ·
              refine ⟨186271989631374929609430197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124181326420916619739620131 186271989631374929609430197)
              ·
                refine ⟨17462999027941399650884081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186271989631374929609430197 17462999027941399650884081)
                ·
                  refine ⟨13097249270956049738163061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17462999027941399650884081 13097249270956049738163061)
                  ·
                    refine ⟨1227867119152129662952787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13097249270956049738163061 1227867119152129662952787)
                    ·
                      rfl

theorem cell22_3586894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_3586894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586894 prefixEnd_3586894 := by exact prefixLift 3586894
  have htrace : WordTrace (prefixWord ++ tailWord_3586894) baseStart_3586894 baseEnd_3586894 := by
    simpa [prefixWord, tailWord_3586894, baseEnd_3586894] using wordTrace_append hprefix tailTrace_3586894
  have hstable : (prefixWord ++ tailWord_3586894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586894).length < 2 ^ (prefixWord ++ tailWord_3586894).sum := by decide
  have hdescent : baseEnd_3586894 < baseStart_3586894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586896 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 5]
def baseStart_3586896 : Nat := 118140960795 + 3586896 * 2 ^ 59
def prefixEnd_3586896 : Nat := 4983230072969 + 3 ^ 40 * 3586896 * 2
def baseEnd_3586896 : Nat := 409289267931000774800927

theorem tailTrace_3586896 : CollatzResearch.WordTrace tailWord_3586896 prefixEnd_3586896 409289267931000774800927 := by
  unfold tailWord_3586896
  simp only [CollatzResearch.WordTrace]
  refine ⟨65412422406647929955442271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87216563208863906607256361 65412422406647929955442271)
  ·
    refine ⟨98118633609971894933163407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65412422406647929955442271 98118633609971894933163407)
    ·
      refine ⟨147177950414957842399745111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98118633609971894933163407 147177950414957842399745111)
      ·
        refine ⟨220766925622436763599617667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147177950414957842399745111 220766925622436763599617667)
        ·
          refine ⟨331150388433655145399426501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220766925622436763599617667 331150388433655145399426501)
          ·
            refine ⟨62090697831310339762392469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331150388433655145399426501 62090697831310339762392469)
            ·
              refine ⟨2910501460842672176362147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62090697831310339762392469 2910501460842672176362147)
              ·
                refine ⟨4365752191264008264543221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910501460842672176362147 4365752191264008264543221)
                ·
                  refine ⟨409289267931000774800927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4365752191264008264543221 409289267931000774800927)
                  ·
                    rfl

theorem cell22_3586896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 5].length) (baseStart_3586896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586896 prefixEnd_3586896 := by exact prefixLift 3586896
  have htrace : WordTrace (prefixWord ++ tailWord_3586896) baseStart_3586896 baseEnd_3586896 := by
    simpa [prefixWord, tailWord_3586896, baseEnd_3586896] using wordTrace_append hprefix tailTrace_3586896
  have hstable : (prefixWord ++ tailWord_3586896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586896).length < 2 ^ (prefixWord ++ tailWord_3586896).sum := by decide
  have hdescent : baseEnd_3586896 < baseStart_3586896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586934 : List Nat := [5, 1, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_3586934 : Nat := 118140960795 + 3586934 * 2 ^ 59
def prefixEnd_3586934 : Nat := 4983230072969 + 3 ^ 40 * 3586934 * 2
def baseEnd_3586934 : Nat := 1227880811969582891952665

theorem tailTrace_3586934 : CollatzResearch.WordTrace tailWord_3586934 prefixEnd_3586934 1227880811969582891952665 := by
  unfold tailWord_3586934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8176639424197387025047991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87217487191438794933845237 8176639424197387025047991)
  ·
    refine ⟨12264959136296080537571987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8176639424197387025047991 12264959136296080537571987)
    ·
      refine ⟨18397438704444120806357981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12264959136296080537571987 18397438704444120806357981)
      ·
        refine ⟨6899039514166545302384243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18397438704444120806357981 6899039514166545302384243)
        ·
          refine ⟨10348559271249817953576365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899039514166545302384243 10348559271249817953576365)
          ·
            refine ⟨3880709726718681732591137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10348559271249817953576365 3880709726718681732591137)
            ·
              refine ⟨2910532295039011299443353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880709726718681732591137 2910532295039011299443353)
              ·
                refine ⟨2182899221279258474582515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2910532295039011299443353 2182899221279258474582515)
                ·
                  refine ⟨3274348831918887711873773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2182899221279258474582515 3274348831918887711873773)
                  ·
                    refine ⟨1227880811969582891952665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274348831918887711873773 1227880811969582891952665)
                    ·
                      rfl

theorem cell22_3586934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_3586934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586934 prefixEnd_3586934 := by exact prefixLift 3586934
  have htrace : WordTrace (prefixWord ++ tailWord_3586934) baseStart_3586934 baseEnd_3586934 := by
    simpa [prefixWord, tailWord_3586934, baseEnd_3586934] using wordTrace_append hprefix tailTrace_3586934
  have hstable : (prefixWord ++ tailWord_3586934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586934).length < 2 ^ (prefixWord ++ tailWord_3586934).sum := by decide
  have hdescent : baseEnd_3586934 < baseStart_3586934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3586999 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 8]
def baseStart_3586999 : Nat := 118140960795 + 3586999 * 2 ^ 59
def prefixEnd_3586999 : Nat := 4983230072969 + 3 ^ 40 * 3586999 * 2
def baseEnd_3586999 : Nat := 1227903062797944389077465

theorem tailTrace_3586999 : CollatzResearch.WordTrace tailWord_3586999 prefixEnd_3586999 1227903062797944389077465 := by
  unfold tailWord_3586999
  simp only [CollatzResearch.WordTrace]
  refine ⟨130828601531922708501884051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87219067687948472334589367 130828601531922708501884051)
  ·
    refine ⟨196242902297884062752826077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130828601531922708501884051 196242902297884062752826077)
    ·
      refine ⟨73591088361706523532309779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196242902297884062752826077 73591088361706523532309779)
      ·
        refine ⟨110386632542559785298464669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73591088361706523532309779 110386632542559785298464669)
        ·
          refine ⟨41394987203459919486924251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110386632542559785298464669 41394987203459919486924251)
          ·
            refine ⟨62092480805189879230386377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41394987203459919486924251 62092480805189879230386377)
            ·
              refine ⟨46569360603892409422789783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62092480805189879230386377 46569360603892409422789783)
              ·
                refine ⟨69854040905838614134184675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46569360603892409422789783 69854040905838614134184675)
                ·
                  refine ⟨104781061358757921201277013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69854040905838614134184675 104781061358757921201277013)
                  ·
                    refine ⟨1227903062797944389077465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104781061358757921201277013 1227903062797944389077465)
                    ·
                      rfl

theorem cell22_3586999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_3586999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3586999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3586999 prefixEnd_3586999 := by exact prefixLift 3586999
  have htrace : WordTrace (prefixWord ++ tailWord_3586999) baseStart_3586999 baseEnd_3586999 := by
    simpa [prefixWord, tailWord_3586999, baseEnd_3586999] using wordTrace_append hprefix tailTrace_3586999
  have hstable : (prefixWord ++ tailWord_3586999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3586999).length < 2 ^ (prefixWord ++ tailWord_3586999).sum := by decide
  have hdescent : baseEnd_3586999 < baseStart_3586999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3586999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587189 : List Nat := [1, 3, 4, 3, 2, 1, 2, 6]
def baseStart_3587189 : Nat := 118140960795 + 3587189 * 2 ^ 59
def prefixEnd_3587189 : Nat := 4983230072969 + 3 ^ 40 * 3587189 * 2
def baseEnd_3587189 : Nat := 136440900408983025202987

theorem tailTrace_3587189 : CollatzResearch.WordTrace tailWord_3587189 prefixEnd_3587189 136440900408983025202987 := by
  unfold tailWord_3587189
  simp only [CollatzResearch.WordTrace]
  refine ⟨130835531401234370951300621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87223687600822913967533747 130835531401234370951300621)
  ·
    refine ⟨49063324275462889106737733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130835531401234370951300621 49063324275462889106737733)
    ·
      refine ⟨9199373301649291707513325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49063324275462889106737733 9199373301649291707513325)
      ·
        refine ⟨3449764988118484390317497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9199373301649291707513325 3449764988118484390317497)
        ·
          refine ⟨2587323741088863292738123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3449764988118484390317497 2587323741088863292738123)
          ·
            refine ⟨3880985611633294939107185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2587323741088863292738123 3880985611633294939107185)
            ·
              refine ⟨2910739208724971204330389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3880985611633294939107185 2910739208724971204330389)
              ·
                refine ⟨136440900408983025202987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2910739208724971204330389 136440900408983025202987)
                ·
                  rfl

theorem cell22_3587189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 6].length) (baseStart_3587189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587189 prefixEnd_3587189 := by exact prefixLift 3587189
  have htrace : WordTrace (prefixWord ++ tailWord_3587189) baseStart_3587189 baseEnd_3587189 := by
    simpa [prefixWord, tailWord_3587189, baseEnd_3587189] using wordTrace_append hprefix tailTrace_3587189
  have hstable : (prefixWord ++ tailWord_3587189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587189).length < 2 ^ (prefixWord ++ tailWord_3587189).sum := by decide
  have hdescent : baseEnd_3587189 < baseStart_3587189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587204 : List Nat := [2, 3, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_3587204 : Nat := 118140960795 + 3587204 * 2 ^ 59
def prefixEnd_3587204 : Nat := 4983230072969 + 3 ^ 40 * 3587204 * 2
def baseEnd_3587204 : Nat := 1227973238487392187701837

theorem tailTrace_3587204 : CollatzResearch.WordTrace tailWord_3587204 prefixEnd_3587204 1227973238487392187701837 := by
  unfold tailWord_3587204
  simp only [CollatzResearch.WordTrace]
  refine ⟨65418039248090014256548333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87224052330786685675397777 65418039248090014256548333)
  ·
    refine ⟨24531764718033755346205625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65418039248090014256548333 24531764718033755346205625)
    ·
      refine ⟨18398823538525316509654219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24531764718033755346205625 18398823538525316509654219)
      ·
        refine ⟨27598235307787974764481329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18398823538525316509654219 27598235307787974764481329)
        ·
          refine ⟨20698676480840981073360997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27598235307787974764481329 20698676480840981073360997)
          ·
            refine ⟨3881001840157683951255187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20698676480840981073360997 3881001840157683951255187)
            ·
              refine ⟨5821502760236525926882781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881001840157683951255187 5821502760236525926882781)
              ·
                refine ⟨2183063535088697222581043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5821502760236525926882781 2183063535088697222581043)
                ·
                  refine ⟨3274595302633045833871565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183063535088697222581043 3274595302633045833871565)
                  ·
                    refine ⟨1227973238487392187701837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274595302633045833871565 1227973238487392187701837)
                    ·
                      rfl

theorem cell22_3587204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_3587204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587204 prefixEnd_3587204 := by exact prefixLift 3587204
  have htrace : WordTrace (prefixWord ++ tailWord_3587204) baseStart_3587204 baseEnd_3587204 := by
    simpa [prefixWord, tailWord_3587204, baseEnd_3587204] using wordTrace_append hprefix tailTrace_3587204
  have hstable : (prefixWord ++ tailWord_3587204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587204).length < 2 ^ (prefixWord ++ tailWord_3587204).sum := by decide
  have hdescent : baseEnd_3587204 < baseStart_3587204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587211 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 8]
def baseStart_3587211 : Nat := 118140960795 + 3587211 * 2 ^ 59
def prefixEnd_3587211 : Nat := 4983230072969 + 3 ^ 40 * 3587211 * 2
def baseEnd_3587211 : Nat := 409325211576815500925605

theorem tailTrace_3587211 : CollatzResearch.WordTrace tailWord_3587211 prefixEnd_3587211 409325211576815500925605 := by
  unfold tailWord_3587211
  simp only [CollatzResearch.WordTrace]
  refine ⟨130836333807154668708601487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87224222538103112472400991 130836333807154668708601487)
  ·
    refine ⟨196254500710732003062902231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130836333807154668708601487 196254500710732003062902231)
    ·
      refine ⟨294381751066098004594353347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196254500710732003062902231 294381751066098004594353347)
      ·
        refine ⟨441572626599147006891530021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294381751066098004594353347 441572626599147006891530021)
        ·
          refine ⟨82794867487340063792161879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441572626599147006891530021 82794867487340063792161879)
          ·
            refine ⟨124192301231010095688242819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82794867487340063792161879 124192301231010095688242819)
            ·
              refine ⟨186288451846515143532364229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124192301231010095688242819 186288451846515143532364229)
              ·
                refine ⟨34929084721221589412318293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186288451846515143532364229 34929084721221589412318293)
                ·
                  refine ⟨409325211576815500925605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34929084721221589412318293 409325211576815500925605)
                  ·
                    rfl

theorem cell22_3587211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 8].length) (baseStart_3587211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587211 prefixEnd_3587211 := by exact prefixLift 3587211
  have htrace : WordTrace (prefixWord ++ tailWord_3587211) baseStart_3587211 baseEnd_3587211 := by
    simpa [prefixWord, tailWord_3587211, baseEnd_3587211] using wordTrace_append hprefix tailTrace_3587211
  have hstable : (prefixWord ++ tailWord_3587211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587211).length < 2 ^ (prefixWord ++ tailWord_3587211).sum := by decide
  have hdescent : baseEnd_3587211 < baseStart_3587211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587234 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_3587234 : Nat := 118140960795 + 3587234 * 2 ^ 59
def prefixEnd_3587234 : Nat := 4983230072969 + 3 ^ 40 * 3587234 * 2
def baseEnd_3587234 : Nat := 409327836033494036483915

theorem tailTrace_3587234 : CollatzResearch.WordTrace tailWord_3587234 prefixEnd_3587234 409327836033494036483915 := by
  unfold tailWord_3587234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32709293171517835909172189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87224781790714229091125837 32709293171517835909172189)
  ·
    refine ⟨12265984939319188465939571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32709293171517835909172189 12265984939319188465939571)
    ·
      refine ⟨18398977408978782698909357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12265984939319188465939571 18398977408978782698909357)
      ·
        refine ⟨6899616528367043512091009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18398977408978782698909357 6899616528367043512091009)
        ·
          refine ⟨5174712396275282634068257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6899616528367043512091009 5174712396275282634068257)
          ·
            refine ⟨3881034297206461975551193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5174712396275282634068257 3881034297206461975551193)
            ·
              refine ⟨2910775722904846481663395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881034297206461975551193 2910775722904846481663395)
              ·
                refine ⟨4366163584357269722495093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910775722904846481663395 4366163584357269722495093)
                ·
                  refine ⟨409327836033494036483915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4366163584357269722495093 409327836033494036483915)
                  ·
                    rfl

theorem cell22_3587234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_3587234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587234 prefixEnd_3587234 := by exact prefixLift 3587234
  have htrace : WordTrace (prefixWord ++ tailWord_3587234) baseStart_3587234 baseEnd_3587234 := by
    simpa [prefixWord, tailWord_3587234, baseEnd_3587234] using wordTrace_append hprefix tailTrace_3587234
  have hstable : (prefixWord ++ tailWord_3587234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587234).length < 2 ^ (prefixWord ++ tailWord_3587234).sum := by decide
  have hdescent : baseEnd_3587234 < baseStart_3587234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587260 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 1, 5]
def baseStart_3587260 : Nat := 118140960795 + 3587260 * 2 ^ 59
def prefixEnd_3587260 : Nat := 4983230072969 + 3 ^ 40 * 3587260 * 2
def baseEnd_3587260 : Nat := 1227992408431826708301665

theorem tailTrace_3587260 : CollatzResearch.WordTrace tailWord_3587260 prefixEnd_3587260 1227992408431826708301665 := by
  unfold tailWord_3587260
  simp only [CollatzResearch.WordTrace]
  refine ⟨65419060491988575038567617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87225413989318100051423489 65419060491988575038567617)
  ·
    refine ⟨49064295368991431278925713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65419060491988575038567617 49064295368991431278925713)
    ·
      refine ⟨36798221526743573459194285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49064295368991431278925713 36798221526743573459194285)
      ·
        refine ⟨13799333072528840047197857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36798221526743573459194285 13799333072528840047197857)
        ·
          refine ⟨10349499804396630035398393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13799333072528840047197857 10349499804396630035398393)
          ·
            refine ⟨7762124853297472526548795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10349499804396630035398393 7762124853297472526548795)
            ·
              refine ⟨11643187279946208789823193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7762124853297472526548795 11643187279946208789823193)
              ·
                refine ⟨8732390459959656592367395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11643187279946208789823193 8732390459959656592367395)
                ·
                  refine ⟨13098585689939484888551093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8732390459959656592367395 13098585689939484888551093)
                  ·
                    refine ⟨1227992408431826708301665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13098585689939484888551093 1227992408431826708301665)
                    ·
                      rfl

theorem cell22_3587260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_3587260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587260 prefixEnd_3587260 := by exact prefixLift 3587260
  have htrace : WordTrace (prefixWord ++ tailWord_3587260) baseStart_3587260 baseEnd_3587260 := by
    simpa [prefixWord, tailWord_3587260, baseEnd_3587260] using wordTrace_append hprefix tailTrace_3587260
  have hstable : (prefixWord ++ tailWord_3587260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587260).length < 2 ^ (prefixWord ++ tailWord_3587260).sum := by decide
  have hdescent : baseEnd_3587260 < baseStart_3587260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587333 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_3587333 : Nat := 118140960795 + 3587333 * 2 ^ 59
def prefixEnd_3587333 : Nat := 4983230072969 + 3 ^ 40 * 3587333 * 2
def baseEnd_3587333 : Nat := 1228017397823678851226441

theorem tailTrace_3587333 : CollatzResearch.WordTrace tailWord_3587333 prefixEnd_3587333 1228017397823678851226441 := by
  unfold tailWord_3587333
  simp only [CollatzResearch.WordTrace]
  refine ⟨130840783512712683544542653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87227189008475122363028435 130840783512712683544542653)
  ·
    refine ⟨49065293817267256329203495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130840783512712683544542653 49065293817267256329203495)
    ·
      refine ⟨73597940725900884493805243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49065293817267256329203495 73597940725900884493805243)
      ·
        refine ⟨110396911088851326740707865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73597940725900884493805243 110396911088851326740707865)
        ·
          refine ⟨82797683316638495055530899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110396911088851326740707865 82797683316638495055530899)
          ·
            refine ⟨124196524974957742583296349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82797683316638495055530899 124196524974957742583296349)
            ·
              refine ⟨46573696865609153468736131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124196524974957742583296349 46573696865609153468736131)
              ·
                refine ⟨69860545298413730203104197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46573696865609153468736131 69860545298413730203104197)
                ·
                  refine ⟨13098852243452574413082037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69860545298413730203104197 13098852243452574413082037)
                  ·
                    refine ⟨1228017397823678851226441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13098852243452574413082037 1228017397823678851226441)
                    ·
                      rfl

theorem cell22_3587333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_3587333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587333 prefixEnd_3587333 := by exact prefixLift 3587333
  have htrace : WordTrace (prefixWord ++ tailWord_3587333) baseStart_3587333 baseEnd_3587333 := by
    simpa [prefixWord, tailWord_3587333, baseEnd_3587333] using wordTrace_append hprefix tailTrace_3587333
  have hstable : (prefixWord ++ tailWord_3587333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587333).length < 2 ^ (prefixWord ++ tailWord_3587333).sum := by decide
  have hdescent : baseEnd_3587333 < baseStart_3587333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587352 : List Nat := [2, 1, 2, 3, 1, 4, 3, 1, 5]
def baseStart_3587352 : Nat := 118140960795 + 3587352 * 2 ^ 59
def prefixEnd_3587352 : Nat := 4983230072969 + 3 ^ 40 * 3587352 * 2
def baseEnd_3587352 : Nat := 409341300637323045000461

theorem tailTrace_3587352 : CollatzResearch.WordTrace tailWord_3587352 prefixEnd_3587352 409341300637323045000461 := by
  unfold tailWord_3587352
  simp only [CollatzResearch.WordTrace]
  refine ⟨65420738249821924894742155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87227650999762566526322873 65420738249821924894742155)
  ·
    refine ⟨98131107374732887342113233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65420738249821924894742155 98131107374732887342113233)
    ·
      refine ⟨73598330531049665506584925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98131107374732887342113233 73598330531049665506584925)
      ·
        refine ⟨27599373949143624564969347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73598330531049665506584925 27599373949143624564969347)
        ·
          refine ⟨41399060923715436847454021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27599373949143624564969347 41399060923715436847454021)
          ·
            refine ⟨7762323923196644408897629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41399060923715436847454021 7762323923196644408897629)
            ·
              refine ⟨2910871471198741653336611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7762323923196644408897629 2910871471198741653336611)
              ·
                refine ⟨4366307206798112480004917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2910871471198741653336611 4366307206798112480004917)
                ·
                  refine ⟨409341300637323045000461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4366307206798112480004917 409341300637323045000461)
                  ·
                    rfl

theorem cell22_3587352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 3, 1, 5].length) (baseStart_3587352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587352 prefixEnd_3587352 := by exact prefixLift 3587352
  have htrace : WordTrace (prefixWord ++ tailWord_3587352) baseStart_3587352 baseEnd_3587352 := by
    simpa [prefixWord, tailWord_3587352, baseEnd_3587352] using wordTrace_append hprefix tailTrace_3587352
  have hstable : (prefixWord ++ tailWord_3587352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587352).length < 2 ^ (prefixWord ++ tailWord_3587352).sum := by decide
  have hdescent : baseEnd_3587352 < baseStart_3587352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587373 : List Nat := [1, 5, 3, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3587373 : Nat := 118140960795 + 3587373 * 2 ^ 59
def prefixEnd_3587373 : Nat := 4983230072969 + 3 ^ 40 * 3587373 * 2
def baseEnd_3587373 : Nat := 1228031090641132080226319

theorem tailTrace_3587373 : CollatzResearch.WordTrace tailWord_3587373 prefixEnd_3587373 1228031090641132080226319 := by
  unfold tailWord_3587373
  simp only [CollatzResearch.WordTrace]
  refine ⟨130842242432567770375998773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87228161621711846917332515 130842242432567770375998773)
  ·
    refine ⟨12266460228053228472749885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130842242432567770375998773 12266460228053228472749885)
    ·
      refine ⟨4599922585519960677281207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12266460228053228472749885 4599922585519960677281207)
      ·
        refine ⟨6899883878279941015921811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4599922585519960677281207 6899883878279941015921811)
        ·
          refine ⟨10349825817419911523882717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6899883878279941015921811 10349825817419911523882717)
          ·
            refine ⟨3881184681532466821456019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10349825817419911523882717 3881184681532466821456019)
            ·
              refine ⟨5821777022298700232184029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3881184681532466821456019 5821777022298700232184029)
              ·
                refine ⟨2183166383362012587069011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5821777022298700232184029 2183166383362012587069011)
                ·
                  refine ⟨3274749575043018880603517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183166383362012587069011 3274749575043018880603517)
                  ·
                    refine ⟨1228031090641132080226319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274749575043018880603517 1228031090641132080226319)
                    ·
                      rfl

theorem cell22_3587373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3587373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587373 prefixEnd_3587373 := by exact prefixLift 3587373
  have htrace : WordTrace (prefixWord ++ tailWord_3587373) baseStart_3587373 baseEnd_3587373 := by
    simpa [prefixWord, tailWord_3587373, baseEnd_3587373] using wordTrace_append hprefix tailTrace_3587373
  have hstable : (prefixWord ++ tailWord_3587373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587373).length < 2 ^ (prefixWord ++ tailWord_3587373).sum := by decide
  have hdescent : baseEnd_3587373 < baseStart_3587373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587410 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3587410 : Nat := 118140960795 + 3587410 * 2 ^ 59
def prefixEnd_3587410 : Nat := 4983230072969 + 3 ^ 40 * 3587410 * 2
def baseEnd_3587410 : Nat := 1228043756497276317051205

theorem tailTrace_3587410 : CollatzResearch.WordTrace tailWord_3587410 prefixEnd_3587410 1228043756497276317051205 := by
  unfold tailWord_3587410
  simp only [CollatzResearch.WordTrace]
  refine ⟨32710897983358431423773921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87229061288955817130063789 32710897983358431423773921)
  ·
    refine ⟨24533173487518823567830441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32710897983358431423773921 24533173487518823567830441)
    ·
      refine ⟨18399880115639117675872831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24533173487518823567830441 18399880115639117675872831)
      ·
        refine ⟨27599820173458676513809247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18399880115639117675872831 27599820173458676513809247)
        ·
          refine ⟨41399730260188014770713871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27599820173458676513809247 41399730260188014770713871)
          ·
            refine ⟨62099595390282022156070807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41399730260188014770713871 62099595390282022156070807)
            ·
              refine ⟨93149393085423033234106211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62099595390282022156070807 93149393085423033234106211)
              ·
                refine ⟨139724089628134549851159317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93149393085423033234106211 139724089628134549851159317)
                ·
                  refine ⟨6549566701318807024273093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139724089628134549851159317 6549566701318807024273093)
                  ·
                    refine ⟨1228043756497276317051205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549566701318807024273093 1228043756497276317051205)
                    ·
                      rfl

theorem cell22_3587410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3587410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587410 prefixEnd_3587410 := by exact prefixLift 3587410
  have htrace : WordTrace (prefixWord ++ tailWord_3587410) baseStart_3587410 baseEnd_3587410 := by
    simpa [prefixWord, tailWord_3587410, baseEnd_3587410] using wordTrace_append hprefix tailTrace_3587410
  have hstable : (prefixWord ++ tailWord_3587410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587410).length < 2 ^ (prefixWord ++ tailWord_3587410).sum := by decide
  have hdescent : baseEnd_3587410 < baseStart_3587410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587427 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 2, 4]
def baseStart_3587427 : Nat := 118140960795 + 3587427 * 2 ^ 59
def prefixEnd_3587427 : Nat := 4983230072969 + 3 ^ 40 * 3587427 * 2
def baseEnd_3587427 : Nat := 1228049575944693939376153

theorem tailTrace_3587427 : CollatzResearch.WordTrace tailWord_3587427 prefixEnd_3587427 1228049575944693939376153 := by
  unfold tailWord_3587427
  simp only [CollatzResearch.WordTrace]
  refine ⟨130844211974372137598464535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87229474649581425065643023 130844211974372137598464535)
  ·
    refine ⟨196266317961558206397696803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130844211974372137598464535 196266317961558206397696803)
    ·
      refine ⟨294399476942337309596545205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196266317961558206397696803 294399476942337309596545205)
      ·
        refine ⟨27599950963344122774676113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294399476942337309596545205 27599950963344122774676113)
        ·
          refine ⟨20699963222508092081007085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27599950963344122774676113 20699963222508092081007085)
          ·
            refine ⟨7762486208440534530377657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20699963222508092081007085 7762486208440534530377657)
            ·
              refine ⟨5821864656330400897783243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7762486208440534530377657 5821864656330400897783243)
              ·
                refine ⟨8732796984495601346674865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5821864656330400897783243 8732796984495601346674865)
                ·
                  refine ⟨6549597738371701010006149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8732796984495601346674865 6549597738371701010006149)
                  ·
                    refine ⟨1228049575944693939376153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6549597738371701010006149 1228049575944693939376153)
                    ·
                      rfl

theorem cell22_3587427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 4].length) (baseStart_3587427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587427 prefixEnd_3587427 := by exact prefixLift 3587427
  have htrace : WordTrace (prefixWord ++ tailWord_3587427) baseStart_3587427 baseEnd_3587427 := by
    simpa [prefixWord, tailWord_3587427, baseEnd_3587427] using wordTrace_append hprefix tailTrace_3587427
  have hstable : (prefixWord ++ tailWord_3587427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587427).length < 2 ^ (prefixWord ++ tailWord_3587427).sum := by decide
  have hdescent : baseEnd_3587427 < baseStart_3587427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587532 : List Nat := [2, 2, 1, 4, 2, 1, 2, 2, 6]
def baseStart_3587532 : Nat := 118140960795 + 3587532 * 2 ^ 59
def prefixEnd_3587532 : Nat := 4983230072969 + 3 ^ 40 * 3587532 * 2
def baseEnd_3587532 : Nat := 409361839863502888500277

theorem tailTrace_3587532 : CollatzResearch.WordTrace tailWord_3587532 prefixEnd_3587532 409361839863502888500277 := by
  unfold tailWord_3587532
  simp only [CollatzResearch.WordTrace]
  refine ⟨65424020819495870265518425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87232027759327827020691233 65424020819495870265518425)
  ·
    refine ⟨49068015614621902699138819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65424020819495870265518425 49068015614621902699138819)
    ·
      refine ⟨73602023421932854048708229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49068015614621902699138819 73602023421932854048708229)
      ·
        refine ⟨13800379391612410134132793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73602023421932854048708229 13800379391612410134132793)
        ·
          refine ⟨10350284543709307600599595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13800379391612410134132793 10350284543709307600599595)
          ·
            refine ⟨15525426815563961400899393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10350284543709307600599595 15525426815563961400899393)
            ·
              refine ⟨11644070111672971050674545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15525426815563961400899393 11644070111672971050674545)
              ·
                refine ⟨8733052583754728288005909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11644070111672971050674545 8733052583754728288005909)
                ·
                  refine ⟨409361839863502888500277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8733052583754728288005909 409361839863502888500277)
                  ·
                    rfl

theorem cell22_3587532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_3587532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587532 prefixEnd_3587532 := by exact prefixLift 3587532
  have htrace : WordTrace (prefixWord ++ tailWord_3587532) baseStart_3587532 baseEnd_3587532 := by
    simpa [prefixWord, tailWord_3587532, baseEnd_3587532] using wordTrace_append hprefix tailTrace_3587532
  have hstable : (prefixWord ++ tailWord_3587532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587532).length < 2 ^ (prefixWord ++ tailWord_3587532).sum := by decide
  have hdescent : baseEnd_3587532 < baseStart_3587532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587566 : List Nat := [4, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3587566 : Nat := 118140960795 + 3587566 * 2 ^ 59
def prefixEnd_3587566 : Nat := 4983230072969 + 3 ^ 40 * 3587566 * 2
def baseEnd_3587566 : Nat := 409365719495114636716909

theorem tailTrace_3587566 : CollatzResearch.WordTrace tailWord_3587566 prefixEnd_3587566 409365719495114636716909 := by
  unfold tailWord_3587566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16356160215108570542221819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87232854480579042891849701 16356160215108570542221819)
  ·
    refine ⟨24534240322662855813332729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16356160215108570542221819 24534240322662855813332729)
    ·
      refine ⟨18400680241997141859999547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24534240322662855813332729 18400680241997141859999547)
      ·
        refine ⟨27601020362995712789999321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18400680241997141859999547 27601020362995712789999321)
        ·
          refine ⟨20700765272246784592499491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27601020362995712789999321 20700765272246784592499491)
          ·
            refine ⟨31051147908370176888749237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20700765272246784592499491 31051147908370176888749237)
            ·
              refine ⟨2911045116409704083320241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31051147908370176888749237 2911045116409704083320241)
              ·
                refine ⟨2183283837307278062490181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911045116409704083320241 2183283837307278062490181)
                ·
                  refine ⟨409365719495114636716909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183283837307278062490181 409365719495114636716909)
                  ·
                    rfl

theorem cell22_3587566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3587566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587566 prefixEnd_3587566 := by exact prefixLift 3587566
  have htrace : WordTrace (prefixWord ++ tailWord_3587566) baseStart_3587566 baseEnd_3587566 := by
    simpa [prefixWord, tailWord_3587566, baseEnd_3587566] using wordTrace_append hprefix tailTrace_3587566
  have hstable : (prefixWord ++ tailWord_3587566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587566).length < 2 ^ (prefixWord ++ tailWord_3587566).sum := by decide
  have hdescent : baseEnd_3587566 < baseStart_3587566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587575 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 2, 7]
def baseStart_3587575 : Nat := 118140960795 + 3587575 * 2 ^ 59
def prefixEnd_3587575 : Nat := 4983230072969 + 3 ^ 40 * 3587575 * 2
def baseEnd_3587575 : Nat := 1228100239369270886675699

theorem tailTrace_3587575 : CollatzResearch.WordTrace tailWord_3587575 prefixEnd_3587575 1228100239369270886675699 := by
  unfold tailWord_3587575
  simp only [CollatzResearch.WordTrace]
  refine ⟨130849609977835958874852179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87233073318557305916568119 130849609977835958874852179)
  ·
    refine ⟨196274414966753938312278269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130849609977835958874852179 196274414966753938312278269)
    ·
      refine ⟨73602905612532726867104351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196274414966753938312278269 73602905612532726867104351)
      ·
        refine ⟨110404358418799090300656527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73602905612532726867104351 110404358418799090300656527)
        ·
          refine ⟨165606537628198635450984791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110404358418799090300656527 165606537628198635450984791)
          ·
            refine ⟨248409806442297953176477187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165606537628198635450984791 248409806442297953176477187)
            ·
              refine ⟨372614709663446929764715781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248409806442297953176477187 372614709663446929764715781)
              ·
                refine ⟨69865258061896299330884209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372614709663446929764715781 69865258061896299330884209)
                ·
                  refine ⟨52398943546422224498163157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69865258061896299330884209 52398943546422224498163157)
                  ·
                    refine ⟨1228100239369270886675699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52398943546422224498163157 1228100239369270886675699)
                    ·
                      rfl

theorem cell22_3587575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_3587575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587575 prefixEnd_3587575 := by exact prefixLift 3587575
  have htrace : WordTrace (prefixWord ++ tailWord_3587575) baseStart_3587575 baseEnd_3587575 := by
    simpa [prefixWord, tailWord_3587575, baseEnd_3587575] using wordTrace_append hprefix tailTrace_3587575
  have hstable : (prefixWord ++ tailWord_3587575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587575).length < 2 ^ (prefixWord ++ tailWord_3587575).sum := by decide
  have hdescent : baseEnd_3587575 < baseStart_3587575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587581 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 2, 3]
def baseStart_3587581 : Nat := 118140960795 + 3587581 * 2 ^ 59
def prefixEnd_3587581 : Nat := 4983230072969 + 3 ^ 40 * 3587581 * 2
def baseEnd_3587581 : Nat := 1228102293291888871025681

theorem tailTrace_3587581 : CollatzResearch.WordTrace tailWord_3587581 prefixEnd_3587581 1228102293291888871025681 := by
  unfold tailWord_3587581
  simp only [CollatzResearch.WordTrace]
  refine ⟨130849828815814221899570597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87233219210542814599713731 130849828815814221899570597)
  ·
    refine ⟨24534342902965166606169487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130849828815814221899570597 24534342902965166606169487)
    ·
      refine ⟨36801514354447749909254231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24534342902965166606169487 36801514354447749909254231)
      ·
        refine ⟨55202271531671624863881347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36801514354447749909254231 55202271531671624863881347)
        ·
          refine ⟨82803407297507437295822021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55202271531671624863881347 82803407297507437295822021)
          ·
            refine ⟨15525638868282644492966629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82803407297507437295822021 15525638868282644492966629)
            ·
              refine ⟨2911057287802995842431243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15525638868282644492966629 2911057287802995842431243)
              ·
                refine ⟨4366585931704493763646865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911057287802995842431243 4366585931704493763646865)
                ·
                  refine ⟨3274939448778370322735149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4366585931704493763646865 3274939448778370322735149)
                  ·
                    refine ⟨1228102293291888871025681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3274939448778370322735149 1228102293291888871025681)
                    ·
                      rfl

theorem cell22_3587581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_3587581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587581 prefixEnd_3587581 := by exact prefixLift 3587581
  have htrace : WordTrace (prefixWord ++ tailWord_3587581) baseStart_3587581 baseEnd_3587581 := by
    simpa [prefixWord, tailWord_3587581, baseEnd_3587581] using wordTrace_append hprefix tailTrace_3587581
  have hstable : (prefixWord ++ tailWord_3587581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587581).length < 2 ^ (prefixWord ++ tailWord_3587581).sum := by decide
  have hdescent : baseEnd_3587581 < baseStart_3587581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587637 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 1, 7]
def baseStart_3587637 : Nat := 118140960795 + 3587637 * 2 ^ 59
def prefixEnd_3587637 : Nat := 4983230072969 + 3 ^ 40 * 3587637 * 2
def baseEnd_3587637 : Nat := 1228121463236323391625509

theorem tailTrace_3587637 : CollatzResearch.WordTrace tailWord_3587637 prefixEnd_3587637 1228121463236323391625509 := by
  unfold tailWord_3587637
  simp only [CollatzResearch.WordTrace]
  refine ⟨130851871303611343463609165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87234580869074228975739443 130851871303611343463609165)
  ·
    refine ⟨49069451738854253798853437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130851871303611343463609165 49069451738854253798853437)
    ·
      refine ⟨18401044402070345174570039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49069451738854253798853437 18401044402070345174570039)
      ·
        refine ⟨27601566603105517761855059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18401044402070345174570039 27601566603105517761855059)
        ·
          refine ⟨41402349904658276642782589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27601566603105517761855059 41402349904658276642782589)
          ·
            refine ⟨15525881214246853741043471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41402349904658276642782589 15525881214246853741043471)
            ·
              refine ⟨23288821821370280611565207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15525881214246853741043471 23288821821370280611565207)
              ·
                refine ⟨34933232732055420917347811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23288821821370280611565207 34933232732055420917347811)
                ·
                  refine ⟨52399849098083131376021717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34933232732055420917347811 52399849098083131376021717)
                  ·
                    refine ⟨1228121463236323391625509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52399849098083131376021717 1228121463236323391625509)
                    ·
                      rfl

theorem cell22_3587637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_3587637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587637 prefixEnd_3587637 := by exact prefixLift 3587637
  have htrace : WordTrace (prefixWord ++ tailWord_3587637) baseStart_3587637 baseEnd_3587637 := by
    simpa [prefixWord, tailWord_3587637, baseEnd_3587637] using wordTrace_append hprefix tailTrace_3587637
  have hstable : (prefixWord ++ tailWord_3587637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587637).length < 2 ^ (prefixWord ++ tailWord_3587637).sum := by decide
  have hdescent : baseEnd_3587637 < baseStart_3587637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587684 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 6]
def baseStart_3587684 : Nat := 118140960795 + 3587684 * 2 ^ 59
def prefixEnd_3587684 : Nat := 4983230072969 + 3 ^ 40 * 3587684 * 2
def baseEnd_3587684 : Nat := 409379184098943645233455

theorem tailTrace_3587684 : CollatzResearch.WordTrace tailWord_3587684 prefixEnd_3587684 409379184098943645233455 := by
  unfold tailWord_3587684
  simp only [CollatzResearch.WordTrace]
  refine ⟨65426792767220535245285053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87235723689627380327046737 65426792767220535245285053)
  ·
    refine ⟨24535047287707700716981895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65426792767220535245285053 24535047287707700716981895)
    ·
      refine ⟨36802570931561551075472843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24535047287707700716981895 36802570931561551075472843)
      ·
        refine ⟨55203856397342326613209265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36802570931561551075472843 55203856397342326613209265)
        ·
          refine ⟨41402892298006744959906949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55203856397342326613209265 41402892298006744959906949)
          ·
            refine ⟨7763042305876264679982553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41402892298006744959906949 7763042305876264679982553)
            ·
              refine ⟨5822281729407198509986915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7763042305876264679982553 5822281729407198509986915)
              ·
                refine ⟨8733422594110797764980373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822281729407198509986915 8733422594110797764980373)
                ·
                  refine ⟨409379184098943645233455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8733422594110797764980373 409379184098943645233455)
                  ·
                    rfl

theorem cell22_3587684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_3587684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587684 prefixEnd_3587684 := by exact prefixLift 3587684
  have htrace : WordTrace (prefixWord ++ tailWord_3587684) baseStart_3587684 baseEnd_3587684 := by
    simpa [prefixWord, tailWord_3587684, baseEnd_3587684] using wordTrace_append hprefix tailTrace_3587684
  have hstable : (prefixWord ++ tailWord_3587684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587684).length < 2 ^ (prefixWord ++ tailWord_3587684).sum := by decide
  have hdescent : baseEnd_3587684 < baseStart_3587684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587712 : List Nat := [2, 1, 1, 2, 1, 4, 3, 8]
def baseStart_3587712 : Nat := 118140960795 + 3587712 * 2 ^ 59
def prefixEnd_3587712 : Nat := 4983230072969 + 3 ^ 40 * 3587712 * 2
def baseEnd_3587712 : Nat := 136460793029894244000031

theorem tailTrace_3587712 : CollatzResearch.WordTrace tailWord_3587712 prefixEnd_3587712 136460793029894244000031 := by
  unfold tailWord_3587712
  simp only [CollatzResearch.WordTrace]
  refine ⟨65427303389169815636294695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87236404518893087515059593 65427303389169815636294695)
  ·
    refine ⟨98140955083754723454442043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65427303389169815636294695 98140955083754723454442043)
    ·
      refine ⟨147211432625632085181663065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98140955083754723454442043 147211432625632085181663065)
      ·
        refine ⟨110408574469224063886247299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147211432625632085181663065 110408574469224063886247299)
        ·
          refine ⟨165612861703836095829370949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110408574469224063886247299 165612861703836095829370949)
          ·
            refine ⟨31052411569469267968007053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165612861703836095829370949 31052411569469267968007053)
            ·
              refine ⟨11644654338550975488002645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31052411569469267968007053 11644654338550975488002645)
              ·
                refine ⟨136460793029894244000031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11644654338550975488002645 136460793029894244000031)
                ·
                  rfl

theorem cell22_3587712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 8].length) (baseStart_3587712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587712 prefixEnd_3587712 := by exact prefixLift 3587712
  have htrace : WordTrace (prefixWord ++ tailWord_3587712) baseStart_3587712 baseEnd_3587712 := by
    simpa [prefixWord, tailWord_3587712, baseEnd_3587712] using wordTrace_append hprefix tailTrace_3587712
  have hstable : (prefixWord ++ tailWord_3587712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587712).length < 2 ^ (prefixWord ++ tailWord_3587712).sum := by decide
  have hdescent : baseEnd_3587712 < baseStart_3587712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587821 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3587821 : Nat := 118140960795 + 3587821 * 2 ^ 59
def prefixEnd_3587821 : Nat := 4983230072969 + 3 ^ 40 * 3587821 * 2
def baseEnd_3587821 : Nat := 1228184450196608245024945

theorem tailTrace_3587821 : CollatzResearch.WordTrace tailWord_3587821 prefixEnd_3587821 1228184450196608245024945 := by
  unfold tailWord_3587821
  simp only [CollatzResearch.WordTrace]
  refine ⟨130858582334944742888307317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87239054889963161925538211 130858582334944742888307317)
  ·
    refine ⟨12267992093901069645778811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130858582334944742888307317 12267992093901069645778811)
    ·
      refine ⟨18401988140851604468668217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12267992093901069645778811 18401988140851604468668217)
      ·
        refine ⟨13801491105638703351501163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18401988140851604468668217 13801491105638703351501163)
        ·
          refine ⟨20702236658458055027251745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13801491105638703351501163 20702236658458055027251745)
          ·
            refine ⟨15526677493843541270438809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20702236658458055027251745 15526677493843541270438809)
            ·
              refine ⟨11645008120382655952829107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15526677493843541270438809 11645008120382655952829107)
              ·
                refine ⟨17467512180573983929243661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645008120382655952829107 17467512180573983929243661)
                ·
                  refine ⟨6550317067715243973466373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17467512180573983929243661 6550317067715243973466373)
                  ·
                    refine ⟨1228184450196608245024945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550317067715243973466373 1228184450196608245024945)
                    ·
                      rfl

theorem cell22_3587821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3587821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587821 prefixEnd_3587821 := by exact prefixLift 3587821
  have htrace : WordTrace (prefixWord ++ tailWord_3587821) baseStart_3587821 baseEnd_3587821 := by
    simpa [prefixWord, tailWord_3587821, baseEnd_3587821] using wordTrace_append hprefix tailTrace_3587821
  have hstable : (prefixWord ++ tailWord_3587821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587821).length < 2 ^ (prefixWord ++ tailWord_3587821).sum := by decide
  have hdescent : baseEnd_3587821 < baseStart_3587821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587846 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_3587846 : Nat := 118140960795 + 3587846 * 2 ^ 59
def prefixEnd_3587846 : Nat := 4983230072969 + 3 ^ 40 * 3587846 * 2
def baseEnd_3587846 : Nat := 1228193008207516513149869

theorem tailTrace_3587846 : CollatzResearch.WordTrace tailWord_3587846 prefixEnd_3587846 1228193008207516513149869 := by
  unfold tailWord_3587846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4089359192495442879936481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87239662773236114771978261 4089359192495442879936481)
  ·
    refine ⟨3067019394371582159952361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4089359192495442879936481 3067019394371582159952361)
    ·
      refine ⟨2300264545778686619964271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3067019394371582159952361 2300264545778686619964271)
      ·
        refine ⟨3450396818668029929946407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2300264545778686619964271 3450396818668029929946407)
        ·
          refine ⟨5175595228002044894919611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3450396818668029929946407 5175595228002044894919611)
          ·
            refine ⟨7763392842003067342379417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5175595228002044894919611 7763392842003067342379417)
            ·
              refine ⟨5822544631502300506784563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7763392842003067342379417 5822544631502300506784563)
              ·
                refine ⟨8733816947253450760176845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5822544631502300506784563 8733816947253450760176845)
                ·
                  refine ⟨3275181355220044035066317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8733816947253450760176845 3275181355220044035066317)
                  ·
                    refine ⟨1228193008207516513149869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275181355220044035066317 1228193008207516513149869)
                    ·
                      rfl

theorem cell22_3587846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_3587846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587846 prefixEnd_3587846 := by exact prefixLift 3587846
  have htrace : WordTrace (prefixWord ++ tailWord_3587846) baseStart_3587846 baseEnd_3587846 := by
    simpa [prefixWord, tailWord_3587846, baseEnd_3587846] using wordTrace_append hprefix tailTrace_3587846
  have hstable : (prefixWord ++ tailWord_3587846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587846).length < 2 ^ (prefixWord ++ tailWord_3587846).sum := by decide
  have hdescent : baseEnd_3587846 < baseStart_3587846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587849 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 4, 4]
def baseStart_3587849 : Nat := 118140960795 + 3587849 * 2 ^ 59
def prefixEnd_3587849 : Nat := 4983230072969 + 3 ^ 40 * 3587849 * 2
def baseEnd_3587849 : Nat := 1228194035168825505324859

theorem tailTrace_3587849 : CollatzResearch.WordTrace tailWord_3587849 prefixEnd_3587849 1228194035168825505324859 := by
  unfold tailWord_3587849
  simp only [CollatzResearch.WordTrace]
  refine ⟨130859603578843303670326601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87239735719228869113551067 130859603578843303670326601)
  ·
    refine ⟨98144702684132477752744951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130859603578843303670326601 98144702684132477752744951)
    ·
      refine ⟨147217054026198716629117427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98144702684132477752744951 147217054026198716629117427)
      ·
        refine ⟨220825581039298074943676141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147217054026198716629117427 220825581039298074943676141)
        ·
          refine ⟨82809592889736778103878553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220825581039298074943676141 82809592889736778103878553)
          ·
            refine ⟨62107194667302583577908915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82809592889736778103878553 62107194667302583577908915)
            ·
              refine ⟨93160792000953875366863373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62107194667302583577908915 93160792000953875366863373)
              ·
                refine ⟨34935297000357703262573765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93160792000953875366863373 34935297000357703262573765)
                ·
                  refine ⟨6550368187567069361732581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34935297000357703262573765 6550368187567069361732581)
                  ·
                    refine ⟨1228194035168825505324859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550368187567069361732581 1228194035168825505324859)
                    ·
                      rfl

theorem cell22_3587849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 4].length) (baseStart_3587849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587849 prefixEnd_3587849 := by exact prefixLift 3587849
  have htrace : WordTrace (prefixWord ++ tailWord_3587849) baseStart_3587849 baseEnd_3587849 := by
    simpa [prefixWord, tailWord_3587849, baseEnd_3587849] using wordTrace_append hprefix tailTrace_3587849
  have hstable : (prefixWord ++ tailWord_3587849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587849).length < 2 ^ (prefixWord ++ tailWord_3587849).sum := by decide
  have hdescent : baseEnd_3587849 < baseStart_3587849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587909 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 7]
def baseStart_3587909 : Nat := 118140960795 + 3587909 * 2 ^ 59
def prefixEnd_3587909 : Nat := 4983230072969 + 3 ^ 40 * 3587909 * 2
def baseEnd_3587909 : Nat := 409404858131668449608225

theorem tailTrace_3587909 : CollatzResearch.WordTrace tailWord_3587909 prefixEnd_3587909 409404858131668449608225 := by
  unfold tailWord_3587909
  simp only [CollatzResearch.WordTrace]
  refine ⟨130861791958625933917510781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87241194639083955945007187 130861791958625933917510781)
  ·
    refine ⟨49073171984484725219066543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130861791958625933917510781 49073171984484725219066543)
    ·
      refine ⟨73609757976727087828599815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49073171984484725219066543 73609757976727087828599815)
      ·
        refine ⟨110414636965090631742899723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73609757976727087828599815 110414636965090631742899723)
        ·
          refine ⟨165621955447635947614349585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110414636965090631742899723 165621955447635947614349585)
          ·
            refine ⟨124216466585726960710762189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165621955447635947614349585 124216466585726960710762189)
            ·
              refine ⟨46581174969647610266535821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124216466585726960710762189 46581174969647610266535821)
              ·
                refine ⟨17467940613617853849950933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46581174969647610266535821 17467940613617853849950933)
                ·
                  refine ⟨409404858131668449608225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17467940613617853849950933 409404858131668449608225)
                  ·
                    rfl

theorem cell22_3587909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_3587909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587909 prefixEnd_3587909 := by exact prefixLift 3587909
  have htrace : WordTrace (prefixWord ++ tailWord_3587909) baseStart_3587909 baseEnd_3587909 := by
    simpa [prefixWord, tailWord_3587909, baseEnd_3587909] using wordTrace_append hprefix tailTrace_3587909
  have hstable : (prefixWord ++ tailWord_3587909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587909).length < 2 ^ (prefixWord ++ tailWord_3587909).sum := by decide
  have hdescent : baseEnd_3587909 < baseStart_3587909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3587988 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3587988 : Nat := 118140960795 + 3587988 * 2 ^ 59
def prefixEnd_3587988 : Nat := 4983230072969 + 3 ^ 40 * 3587988 * 2
def baseEnd_3587988 : Nat := 409413872569825158699811

theorem tailTrace_3587988 : CollatzResearch.WordTrace tailWord_3587988 prefixEnd_3587988 409413872569825158699811 := by
  unfold tailWord_3587988
  simp only [CollatzResearch.WordTrace]
  refine ⟨65432336662669865204818309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87243115550226486939757745 65432336662669865204818309)
  ·
    refine ⟨12268563124250599725903433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65432336662669865204818309 12268563124250599725903433)
    ·
      refine ⟨9201422343187949794427575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12268563124250599725903433 9201422343187949794427575)
      ·
        refine ⟨13802133514781924691641363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201422343187949794427575 13802133514781924691641363)
        ·
          refine ⟨20703200272172887037462045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13802133514781924691641363 20703200272172887037462045)
          ·
            refine ⟨7763700102064832639048267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20703200272172887037462045 7763700102064832639048267)
            ·
              refine ⟨11645550153097248958572401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7763700102064832639048267 11645550153097248958572401)
              ·
                refine ⟨8734162614822936718929301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11645550153097248958572401 8734162614822936718929301)
                ·
                  refine ⟨409413872569825158699811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8734162614822936718929301 409413872569825158699811)
                  ·
                    rfl

theorem cell22_3587988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3587988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3587988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3587988 prefixEnd_3587988 := by exact prefixLift 3587988
  have htrace : WordTrace (prefixWord ++ tailWord_3587988) baseStart_3587988 baseEnd_3587988 := by
    simpa [prefixWord, tailWord_3587988, baseEnd_3587988] using wordTrace_append hprefix tailTrace_3587988
  have hstable : (prefixWord ++ tailWord_3587988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3587988).length < 2 ^ (prefixWord ++ tailWord_3587988).sum := by decide
  have hdescent : baseEnd_3587988 < baseStart_3587988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3587988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588007 : List Nat := [1, 1, 6, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3588007 : Nat := 118140960795 + 3588007 * 2 ^ 59
def prefixEnd_3588007 : Nat := 4983230072969 + 3 ^ 40 * 3588007 * 2
def baseEnd_3588007 : Nat := 1228248121797765759874375

theorem tailTrace_3588007 : CollatzResearch.WordTrace tailWord_3588007 prefixEnd_3588007 1228248121797765759874375 := by
  unfold tailWord_3588007
  simp only [CollatzResearch.WordTrace]
  refine ⟨130865366312270896654578275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87243577541513931103052183 130865366312270896654578275)
  ·
    refine ⟨196298049468406344981867413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130865366312270896654578275 196298049468406344981867413)
    ·
      refine ⟨9201471068831547421025035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196298049468406344981867413 9201471068831547421025035)
      ·
        refine ⟨13802206603247321131537553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9201471068831547421025035 13802206603247321131537553)
        ·
          refine ⟨10351654952435490848653165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13802206603247321131537553 10351654952435490848653165)
          ·
            refine ⟨3881870607163309068244937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10351654952435490848653165 3881870607163309068244937)
            ·
              refine ⟨2911402955372481801183703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3881870607163309068244937 2911402955372481801183703)
              ·
                refine ⟨4367104433058722701775555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2911402955372481801183703 4367104433058722701775555)
                ·
                  refine ⟨6550656649588084052663333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367104433058722701775555 6550656649588084052663333)
                  ·
                    refine ⟨1228248121797765759874375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550656649588084052663333 1228248121797765759874375)
                    ·
                      rfl

theorem cell22_3588007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3588007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588007 prefixEnd_3588007 := by exact prefixLift 3588007
  have htrace : WordTrace (prefixWord ++ tailWord_3588007) baseStart_3588007 baseEnd_3588007 := by
    simpa [prefixWord, tailWord_3588007, baseEnd_3588007] using wordTrace_append hprefix tailTrace_3588007
  have hstable : (prefixWord ++ tailWord_3588007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588007).length < 2 ^ (prefixWord ++ tailWord_3588007).sum := by decide
  have hdescent : baseEnd_3588007 < baseStart_3588007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588048 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 3, 3]
def baseStart_3588048 : Nat := 118140960795 + 3588048 * 2 ^ 59
def prefixEnd_3588048 : Nat := 4983230072969 + 3 ^ 40 * 3588048 * 2
def baseEnd_3588048 : Nat := 1228262156935655319599249

theorem tailTrace_3588048 : CollatzResearch.WordTrace tailWord_3588048 prefixEnd_3588048 1228262156935655319599249 := by
  unfold tailWord_3588048
  simp only [CollatzResearch.WordTrace]
  refine ⟨65433430852561180328410399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87244574470081573771213865 65433430852561180328410399)
  ·
    refine ⟨98150146278841770492615599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65433430852561180328410399 98150146278841770492615599)
    ·
      refine ⟨147225219418262655738923399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98150146278841770492615599 147225219418262655738923399)
      ·
        refine ⟨220837829127393983608385099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147225219418262655738923399 220837829127393983608385099)
        ·
          refine ⟨331256743691090975412577649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220837829127393983608385099 331256743691090975412577649)
          ·
            refine ⟨248442557768318231559433237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331256743691090975412577649 248442557768318231559433237)
            ·
              refine ⟨11645744895389917104348433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248442557768318231559433237 11645744895389917104348433)
              ·
                refine ⟨8734308671542437828261325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11645744895389917104348433 8734308671542437828261325)
                ·
                  refine ⟨3275365751828414185597997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8734308671542437828261325 3275365751828414185597997)
                  ·
                    refine ⟨1228262156935655319599249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275365751828414185597997 1228262156935655319599249)
                    ·
                      rfl

theorem cell22_3588048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_3588048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588048 prefixEnd_3588048 := by exact prefixLift 3588048
  have htrace : WordTrace (prefixWord ++ tailWord_3588048) baseStart_3588048 baseEnd_3588048 := by
    simpa [prefixWord, tailWord_3588048, baseEnd_3588048] using wordTrace_append hprefix tailTrace_3588048
  have hstable : (prefixWord ++ tailWord_3588048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588048).length < 2 ^ (prefixWord ++ tailWord_3588048).sum := by decide
  have hdescent : baseEnd_3588048 < baseStart_3588048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588076 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 4, 5]
def baseStart_3588076 : Nat := 118140960795 + 3588076 * 2 ^ 59
def prefixEnd_3588076 : Nat := 4983230072969 + 3 ^ 40 * 3588076 * 2
def baseEnd_3588076 : Nat := 1228271741907872579899163

theorem tailTrace_3588076 : CollatzResearch.WordTrace tailWord_3588076 prefixEnd_3588076 1228271741907872579899163 := by
  unfold tailWord_3588076
  simp only [CollatzResearch.WordTrace]
  refine ⟨65433941474510460719420041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87245255299347280959226721 65433941474510460719420041)
  ·
    refine ⟨49075456105882845539565031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65433941474510460719420041 49075456105882845539565031)
    ·
      refine ⟨73613184158824268309347547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49075456105882845539565031 73613184158824268309347547)
      ·
        refine ⟨110419776238236402464021321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73613184158824268309347547 110419776238236402464021321)
        ·
          refine ⟨82814832178677301848015991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110419776238236402464021321 82814832178677301848015991)
          ·
            refine ⟨124222248268015952772023987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82814832178677301848015991 124222248268015952772023987)
            ·
              refine ⟨186333372402023929158035981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124222248268015952772023987 186333372402023929158035981)
              ·
                refine ⟨69875014650758973434263493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186333372402023929158035981 69875014650758973434263493)
                ·
                  refine ⟨13101565247017307518924405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69875014650758973434263493 13101565247017307518924405)
                  ·
                    refine ⟨1228271741907872579899163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13101565247017307518924405 1228271741907872579899163)
                    ·
                      rfl

theorem cell22_3588076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_3588076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588076 prefixEnd_3588076 := by exact prefixLift 3588076
  have htrace : WordTrace (prefixWord ++ tailWord_3588076) baseStart_3588076 baseEnd_3588076 := by
    simpa [prefixWord, tailWord_3588076, baseEnd_3588076] using wordTrace_append hprefix tailTrace_3588076
  have hstable : (prefixWord ++ tailWord_3588076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588076).length < 2 ^ (prefixWord ++ tailWord_3588076).sum := by decide
  have hdescent : baseEnd_3588076 < baseStart_3588076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588078 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 7]
def baseStart_3588078 : Nat := 118140960795 + 3588078 * 2 ^ 59
def prefixEnd_3588078 : Nat := 4983230072969 + 3 ^ 40 * 3588078 * 2
def baseEnd_3588078 : Nat := 409424142182915080449719

theorem tailTrace_3588078 : CollatzResearch.WordTrace tailWord_3588078 prefixEnd_3588078 409424142182915080449719 := by
  unfold tailWord_3588078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16358494486876709472551611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87245303930009117186941925 16358494486876709472551611)
  ·
    refine ⟨24537741730315064208827417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16358494486876709472551611 24537741730315064208827417)
    ·
      refine ⟨18403306297736298156620563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24537741730315064208827417 18403306297736298156620563)
      ·
        refine ⟨27604959446604447234930845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18403306297736298156620563 27604959446604447234930845)
        ·
          refine ⟨10351859792476667713099067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27604959446604447234930845 10351859792476667713099067)
          ·
            refine ⟨15527789688715001569648601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10351859792476667713099067 15527789688715001569648601)
            ·
              refine ⟨11645842266536251177236451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15527789688715001569648601 11645842266536251177236451)
              ·
                refine ⟨17468763399804376765854677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645842266536251177236451 17468763399804376765854677)
                ·
                  refine ⟨409424142182915080449719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17468763399804376765854677 409424142182915080449719)
                  ·
                    rfl

theorem cell22_3588078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_3588078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588078 prefixEnd_3588078 := by exact prefixLift 3588078
  have htrace : WordTrace (prefixWord ++ tailWord_3588078) baseStart_3588078 baseEnd_3588078 := by
    simpa [prefixWord, tailWord_3588078, baseEnd_3588078] using wordTrace_append hprefix tailTrace_3588078
  have hstable : (prefixWord ++ tailWord_3588078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588078).length < 2 ^ (prefixWord ++ tailWord_3588078).sum := by decide
  have hdescent : baseEnd_3588078 < baseStart_3588078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588108 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_3588108 : Nat := 118140960795 + 3588108 * 2 ^ 59
def prefixEnd_3588108 : Nat := 4983230072969 + 3 ^ 40 * 3588108 * 2
def baseEnd_3588108 : Nat := 1228282696161835163099065

theorem tailTrace_3588108 : CollatzResearch.WordTrace tailWord_3588108 prefixEnd_3588108 1228282696161835163099065 := by
  unfold tailWord_3588108
  simp only [CollatzResearch.WordTrace]
  refine ⟨65434525042452495452002489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87246033389936660602669985 65434525042452495452002489)
  ·
    refine ⟨49075893781839371589001867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65434525042452495452002489 49075893781839371589001867)
    ·
      refine ⟨73613840672759057383502801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49075893781839371589001867 73613840672759057383502801)
      ·
        refine ⟨55210380504569293037627101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73613840672759057383502801 55210380504569293037627101)
        ·
          refine ⟨20703892689213484889110163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55210380504569293037627101 20703892689213484889110163)
          ·
            refine ⟨31055839033820227333665245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20703892689213484889110163 31055839033820227333665245)
            ·
              refine ⟨11645939637682585250124467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31055839033820227333665245 11645939637682585250124467)
              ·
                refine ⟨17468909456523877875186701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11645939637682585250124467 17468909456523877875186701)
                ·
                  refine ⟨6550841046196454203195013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17468909456523877875186701 6550841046196454203195013)
                  ·
                    refine ⟨1228282696161835163099065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6550841046196454203195013 1228282696161835163099065)
                    ·
                      rfl

theorem cell22_3588108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_3588108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588108 prefixEnd_3588108 := by exact prefixLift 3588108
  have htrace : WordTrace (prefixWord ++ tailWord_3588108) baseStart_3588108 baseEnd_3588108 := by
    simpa [prefixWord, tailWord_3588108, baseEnd_3588108] using wordTrace_append hprefix tailTrace_3588108
  have hstable : (prefixWord ++ tailWord_3588108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588108).length < 2 ^ (prefixWord ++ tailWord_3588108).sum := by decide
  have hdescent : baseEnd_3588108 < baseStart_3588108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588189 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3588189 : Nat := 118140960795 + 3588189 * 2 ^ 59
def prefixEnd_3588189 : Nat := 4983230072969 + 3 ^ 40 * 3588189 * 2
def baseEnd_3588189 : Nat := 1228310424117177951823817

theorem tailTrace_3588189 : CollatzResearch.WordTrace tailWord_3588189 prefixEnd_3588189 1228310424117177951823817 := by
  unfold tailWord_3588189
  simp only [CollatzResearch.WordTrace]
  refine ⟨130872004397611541737703621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87248002931741027825135747 130872004397611541737703621)
  ·
    refine ⟨24538500824552164075819429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130872004397611541737703621 24538500824552164075819429)
    ·
      refine ⟨4600968904603530764216143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24538500824552164075819429 4600968904603530764216143)
      ·
        refine ⟨6901453356905296146324215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4600968904603530764216143 6901453356905296146324215)
        ·
          refine ⟨10352180035357944219486323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6901453356905296146324215 10352180035357944219486323)
          ·
            refine ⟨15528270053036916329229485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10352180035357944219486323 15528270053036916329229485)
            ·
              refine ⟨5823101269888843623461057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15528270053036916329229485 5823101269888843623461057)
              ·
                refine ⟨4367325952416632717595793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5823101269888843623461057 4367325952416632717595793)
                ·
                  refine ⟨3275494464312474538196845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4367325952416632717595793 3275494464312474538196845)
                  ·
                    refine ⟨1228310424117177951823817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275494464312474538196845 1228310424117177951823817)
                    ·
                      rfl

theorem cell22_3588189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3588189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588189 prefixEnd_3588189 := by exact prefixLift 3588189
  have htrace : WordTrace (prefixWord ++ tailWord_3588189) baseStart_3588189 baseEnd_3588189 := by
    simpa [prefixWord, tailWord_3588189, baseEnd_3588189] using wordTrace_append hprefix tailTrace_3588189
  have hstable : (prefixWord ++ tailWord_3588189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588189).length < 2 ^ (prefixWord ++ tailWord_3588189).sum := by decide
  have hdescent : baseEnd_3588189 < baseStart_3588189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588234 : List Nat := [3, 1, 2, 3, 1, 2, 3, 3, 1, 3]
def baseStart_3588234 : Nat := 118140960795 + 3588234 * 2 ^ 59
def prefixEnd_3588234 : Nat := 4983230072969 + 3 ^ 40 * 3588234 * 2
def baseEnd_3588234 : Nat := 1228325828536812834448679

theorem tailTrace_3588234 : CollatzResearch.WordTrace tailWord_3588234 prefixEnd_3588234 1228325828536812834448679 := by
  unfold tailWord_3588234
  simp only [CollatzResearch.WordTrace]
  refine ⟨32718411420612128605772939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87249097121632342948727837 32718411420612128605772939)
  ·
    refine ⟨49077617130918192908659409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32718411420612128605772939 49077617130918192908659409)
    ·
      refine ⟨36808212848188644681494557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49077617130918192908659409 36808212848188644681494557)
      ·
        refine ⟨13803079818070741755560459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36808212848188644681494557 13803079818070741755560459)
        ·
          refine ⟨20704619727106112633340689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13803079818070741755560459 20704619727106112633340689)
          ·
            refine ⟨15528464795329584475005517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20704619727106112633340689 15528464795329584475005517)
            ·
              refine ⟨5823174298248594178127069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15528464795329584475005517 5823174298248594178127069)
              ·
                refine ⟨2183690361843222816797651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5823174298248594178127069 2183690361843222816797651)
                ·
                  refine ⟨3275535542764834225196477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183690361843222816797651 3275535542764834225196477)
                  ·
                    refine ⟨1228325828536812834448679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275535542764834225196477 1228325828536812834448679)
                    ·
                      rfl

theorem cell22_3588234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_3588234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588234 prefixEnd_3588234 := by exact prefixLift 3588234
  have htrace : WordTrace (prefixWord ++ tailWord_3588234) baseStart_3588234 baseEnd_3588234 := by
    simpa [prefixWord, tailWord_3588234, baseEnd_3588234] using wordTrace_append hprefix tailTrace_3588234
  have hstable : (prefixWord ++ tailWord_3588234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588234).length < 2 ^ (prefixWord ++ tailWord_3588234).sum := by decide
  have hdescent : baseEnd_3588234 < baseStart_3588234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588243 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 5, 4]
def baseStart_3588243 : Nat := 118140960795 + 3588243 * 2 ^ 59
def prefixEnd_3588243 : Nat := 4983230072969 + 3 ^ 40 * 3588243 * 2
def baseEnd_3588243 : Nat := 1228328909420739810973651

theorem tailTrace_3588243 : CollatzResearch.WordTrace tailWord_3588243 prefixEnd_3588243 1228328909420739810973651 := by
  unfold tailWord_3588243
  simp only [CollatzResearch.WordTrace]
  refine ⟨130873973939415908960169383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87249315959610605973446255 130873973939415908960169383)
  ·
    refine ⟨196310960909123863440254075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130873973939415908960169383 196310960909123863440254075)
    ·
      refine ⟨294466441363685795160381113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196310960909123863440254075 294466441363685795160381113)
      ·
        refine ⟨220849831022764346370285835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294466441363685795160381113 220849831022764346370285835)
        ·
          refine ⟨331274746534146519555428753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220849831022764346370285835 331274746534146519555428753)
          ·
            refine ⟨248456059900609889666571565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331274746534146519555428753 248456059900609889666571565)
            ·
              refine ⟨93171022462728708624964337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248456059900609889666571565 93171022462728708624964337)
              ·
                refine ⟨69878266847046531468723253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93171022462728708624964337 69878266847046531468723253)
                ·
                  refine ⟨6551087516910612325192805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69878266847046531468723253 6551087516910612325192805)
                  ·
                    refine ⟨1228328909420739810973651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551087516910612325192805 1228328909420739810973651)
                    ·
                      rfl

theorem cell22_3588243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 4].length) (baseStart_3588243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588243 prefixEnd_3588243 := by exact prefixLift 3588243
  have htrace : WordTrace (prefixWord ++ tailWord_3588243) baseStart_3588243 baseEnd_3588243 := by
    simpa [prefixWord, tailWord_3588243, baseEnd_3588243] using wordTrace_append hprefix tailTrace_3588243
  have hstable : (prefixWord ++ tailWord_3588243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588243).length < 2 ^ (prefixWord ++ tailWord_3588243).sum := by decide
  have hdescent : baseEnd_3588243 < baseStart_3588243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588305 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 2, 4]
def baseStart_3588305 : Nat := 118140960795 + 3588305 * 2 ^ 59
def prefixEnd_3588305 : Nat := 4983230072969 + 3 ^ 40 * 3588305 * 2
def baseEnd_3588305 : Nat := 1228350133287792315923461

theorem tailTrace_3588305 : CollatzResearch.WordTrace tailWord_3588305 prefixEnd_3588305 1228350133287792315923461 := by
  unfold tailWord_3588305
  simp only [CollatzResearch.WordTrace]
  refine ⟨130876235265191293548926369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87250823510127529032617579 130876235265191293548926369)
  ·
    refine ⟨98157176448893470161694777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130876235265191293548926369 98157176448893470161694777)
    ·
      refine ⟨73617882336670102621271083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98157176448893470161694777 73617882336670102621271083)
      ·
        refine ⟨110426823505005153931906625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73617882336670102621271083 110426823505005153931906625)
        ·
          refine ⟨82820117628753865448929969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110426823505005153931906625 82820117628753865448929969)
          ·
            refine ⟨62115088221565399086697477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82820117628753865448929969 62115088221565399086697477)
            ·
              refine ⟨11646579041543512328755777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62115088221565399086697477 11646579041543512328755777)
              ·
                refine ⟨8734934281157634246566833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11646579041543512328755777 8734934281157634246566833)
                ·
                  refine ⟨6551200710868225684925125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8734934281157634246566833 6551200710868225684925125)
                  ·
                    refine ⟨1228350133287792315923461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551200710868225684925125 1228350133287792315923461)
                    ·
                      rfl

theorem cell22_3588305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_3588305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588305 prefixEnd_3588305 := by exact prefixLift 3588305
  have htrace : WordTrace (prefixWord ++ tailWord_3588305) baseStart_3588305 baseEnd_3588305 := by
    simpa [prefixWord, tailWord_3588305, baseEnd_3588305] using wordTrace_append hprefix tailTrace_3588305
  have hstable : (prefixWord ++ tailWord_3588305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588305).length < 2 ^ (prefixWord ++ tailWord_3588305).sum := by decide
  have hdescent : baseEnd_3588305 < baseStart_3588305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588309 : List Nat := [1, 3, 2, 4, 2, 1, 1, 4, 4]
def baseStart_3588309 : Nat := 118140960795 + 3588309 * 2 ^ 59
def prefixEnd_3588309 : Nat := 4983230072969 + 3 ^ 40 * 3588309 * 2
def baseEnd_3588309 : Nat := 409450500856512546274483

theorem tailTrace_3588309 : CollatzResearch.WordTrace tailWord_3588309 prefixEnd_3588309 409450500856512546274483 := by
  unfold tailWord_3588309
  simp only [CollatzResearch.WordTrace]
  refine ⟨130876381157176802232071981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87250920771451201488047987 130876381157176802232071981)
  ·
    refine ⟨49078642933941300837026993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130876381157176802232071981 49078642933941300837026993)
    ·
      refine ⟨36808982200455975627770245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49078642933941300837026993 36808982200455975627770245)
      ·
        refine ⟨6901684162585495430206921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36808982200455975627770245 6901684162585495430206921)
        ·
          refine ⟨5176263121939121572655191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6901684162585495430206921 5176263121939121572655191)
          ·
            refine ⟨7764394682908682358982787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176263121939121572655191 7764394682908682358982787)
            ·
              refine ⟨11646592024363023538474181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7764394682908682358982787 11646592024363023538474181)
              ·
                refine ⟨2183736004568066913463909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11646592024363023538474181 2183736004568066913463909)
                ·
                  refine ⟨409450500856512546274483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183736004568066913463909 409450500856512546274483)
                  ·
                    rfl

theorem cell22_3588309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_3588309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588309 prefixEnd_3588309 := by exact prefixLift 3588309
  have htrace : WordTrace (prefixWord ++ tailWord_3588309) baseStart_3588309 baseEnd_3588309 := by
    simpa [prefixWord, tailWord_3588309, baseEnd_3588309] using wordTrace_append hprefix tailTrace_3588309
  have hstable : (prefixWord ++ tailWord_3588309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588309).length < 2 ^ (prefixWord ++ tailWord_3588309).sum := by decide
  have hdescent : baseEnd_3588309 < baseStart_3588309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588369 : List Nat := [1, 2, 2, 1, 1, 5, 2, 4, 1, 3]
def baseStart_3588369 : Nat := 118140960795 + 3588369 * 2 ^ 59
def prefixEnd_3588369 : Nat := 4983230072969 + 3 ^ 40 * 3588369 * 2
def baseEnd_3588369 : Nat := 1228372041795717482323265

theorem tailTrace_3588369 : CollatzResearch.WordTrace tailWord_3588369 prefixEnd_3588369 1228372041795717482323265 := by
  unfold tailWord_3588369
  simp only [CollatzResearch.WordTrace]
  refine ⟨130878569536959432479256161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87252379691306288319504107 130878569536959432479256161)
  ·
    refine ⟨98158927152719574359442121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130878569536959432479256161 98158927152719574359442121)
    ·
      refine ⟨73619195364539680769581591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98158927152719574359442121 73619195364539680769581591)
      ·
        refine ⟨110428793046809521154372387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73619195364539680769581591 110428793046809521154372387)
        ·
          refine ⟨165643189570214281731558581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110428793046809521154372387 165643189570214281731558581)
          ·
            refine ⟨15529049022207588912333617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165643189570214281731558581 15529049022207588912333617)
            ·
              refine ⟨11646786766655691684250213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15529049022207588912333617 11646786766655691684250213)
              ·
                refine ⟨2183772518747942190796915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11646786766655691684250213 2183772518747942190796915)
                ·
                  refine ⟨3275658778121913286195373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183772518747942190796915 3275658778121913286195373)
                  ·
                    refine ⟨1228372041795717482323265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275658778121913286195373 1228372041795717482323265)
                    ·
                      rfl

theorem cell22_3588369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 3].length) (baseStart_3588369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588369 prefixEnd_3588369 := by exact prefixLift 3588369
  have htrace : WordTrace (prefixWord ++ tailWord_3588369) baseStart_3588369 baseEnd_3588369 := by
    simpa [prefixWord, tailWord_3588369, baseEnd_3588369] using wordTrace_append hprefix tailTrace_3588369
  have hstable : (prefixWord ++ tailWord_3588369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588369).length < 2 ^ (prefixWord ++ tailWord_3588369).sum := by decide
  have hdescent : baseEnd_3588369 < baseStart_3588369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588412 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 1, 4]
def baseStart_3588412 : Nat := 118140960795 + 3588412 * 2 ^ 59
def prefixEnd_3588412 : Nat := 4983230072969 + 3 ^ 40 * 3588412 * 2
def baseEnd_3588412 : Nat := 1228386761574479703498133

theorem tailTrace_3588412 : CollatzResearch.WordTrace tailWord_3588412 prefixEnd_3588412 1228386761574479703498133 := by
  unfold tailWord_3588412
  simp only [CollatzResearch.WordTrace]
  refine ⟨65440068937901825411535745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87253425250535767215380993 65440068937901825411535745)
  ·
    refine ⟨49080051703426369058651809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65440068937901825411535745 49080051703426369058651809)
    ·
      refine ⟨36810038777569776793988857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49080051703426369058651809 36810038777569776793988857)
      ·
        refine ⟨27607529083177332595491643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36810038777569776793988857 27607529083177332595491643)
        ·
          refine ⟨41411293624765998893237465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27607529083177332595491643 41411293624765998893237465)
          ·
            refine ⟨31058470218574499169928099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41411293624765998893237465 31058470218574499169928099)
            ·
              refine ⟨46587705327861748754892149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31058470218574499169928099 46587705327861748754892149)
              ·
                refine ⟨4367597374487038945771139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46587705327861748754892149 4367597374487038945771139)
                ·
                  refine ⟨6551396061730558418656709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367597374487038945771139 6551396061730558418656709)
                  ·
                    refine ⟨1228386761574479703498133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551396061730558418656709 1228386761574479703498133)
                    ·
                      rfl

theorem cell22_3588412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_3588412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588412 prefixEnd_3588412 := by exact prefixLift 3588412
  have htrace : WordTrace (prefixWord ++ tailWord_3588412) baseStart_3588412 baseEnd_3588412 := by
    simpa [prefixWord, tailWord_3588412, baseEnd_3588412] using wordTrace_append hprefix tailTrace_3588412
  have hstable : (prefixWord ++ tailWord_3588412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588412).length < 2 ^ (prefixWord ++ tailWord_3588412).sum := by decide
  have hdescent : baseEnd_3588412 < baseStart_3588412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588420 : List Nat := [2, 3, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3588420 : Nat := 118140960795 + 3588420 * 2 ^ 59
def prefixEnd_3588420 : Nat := 4983230072969 + 3 ^ 40 * 3588420 * 2
def baseEnd_3588420 : Nat := 1228389500137970349298109

theorem tailTrace_3588420 : CollatzResearch.WordTrace tailWord_3588420 prefixEnd_3588420 1228389500137970349298109 := by
  unfold tailWord_3588420
  simp only [CollatzResearch.WordTrace]
  refine ⟨65440214829887334094681357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87253619773183112126241809 65440214829887334094681357)
  ·
    refine ⟨24540080561207750285505509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65440214829887334094681357 24540080561207750285505509)
    ·
      refine ⟨4601265105226453178532283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24540080561207750285505509 4601265105226453178532283)
      ·
        refine ⟨6901897657839679767798425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4601265105226453178532283 6901897657839679767798425)
        ·
          refine ⟨5176423243379759825848819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6901897657839679767798425 5176423243379759825848819)
          ·
            refine ⟨7764634865069639738773229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176423243379759825848819 7764634865069639738773229)
            ·
              refine ⟨2911738074401114902039961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7764634865069639738773229 2911738074401114902039961)
              ·
                refine ⟨2183803555800836176529971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911738074401114902039961 2183803555800836176529971)
                ·
                  refine ⟨3275705333701254264794957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2183803555800836176529971 3275705333701254264794957)
                  ·
                    refine ⟨1228389500137970349298109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275705333701254264794957 1228389500137970349298109)
                    ·
                      rfl

theorem cell22_3588420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3588420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588420 prefixEnd_3588420 := by exact prefixLift 3588420
  have htrace : WordTrace (prefixWord ++ tailWord_3588420) baseStart_3588420 baseEnd_3588420 := by
    simpa [prefixWord, tailWord_3588420, baseEnd_3588420] using wordTrace_append hprefix tailTrace_3588420
  have hstable : (prefixWord ++ tailWord_3588420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588420).length < 2 ^ (prefixWord ++ tailWord_3588420).sum := by decide
  have hdescent : baseEnd_3588420 < baseStart_3588420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588440 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 1, 6]
def baseStart_3588440 : Nat := 118140960795 + 3588440 * 2 ^ 59
def prefixEnd_3588440 : Nat := 4983230072969 + 3 ^ 40 * 3588440 * 2
def baseEnd_3588440 : Nat := 1228396346546696963798047

theorem tailTrace_3588440 : CollatzResearch.WordTrace tailWord_3588440 prefixEnd_3588440 1228396346546696963798047 := by
  unfold tailWord_3588440
  simp only [CollatzResearch.WordTrace]
  refine ⟨65440579559851105802545387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87254106079801474403393849 65440579559851105802545387)
  ·
    refine ⟨98160869339776658703818081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65440579559851105802545387 98160869339776658703818081)
    ·
      refine ⟨73620652004832494027863561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98160869339776658703818081 73620652004832494027863561)
      ·
        refine ⟨55215489003624370520897671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73620652004832494027863561 55215489003624370520897671)
        ·
          refine ⟨82823233505436555781346507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55215489003624370520897671 82823233505436555781346507)
          ·
            refine ⟨124234850258154833672019761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82823233505436555781346507 124234850258154833672019761)
            ·
              refine ⟨93176137693616125254014821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124234850258154833672019761 93176137693616125254014821)
              ·
                refine ⟨17470525817553023485127779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93176137693616125254014821 17470525817553023485127779)
                ·
                  refine ⟨26205788726329535227691669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17470525817553023485127779 26205788726329535227691669)
                  ·
                    refine ⟨1228396346546696963798047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26205788726329535227691669 1228396346546696963798047)
                    ·
                      rfl

theorem cell22_3588440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_3588440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588440 prefixEnd_3588440 := by exact prefixLift 3588440
  have htrace : WordTrace (prefixWord ++ tailWord_3588440) baseStart_3588440 baseEnd_3588440 := by
    simpa [prefixWord, tailWord_3588440, baseEnd_3588440] using wordTrace_append hprefix tailTrace_3588440
  have hstable : (prefixWord ++ tailWord_3588440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588440).length < 2 ^ (prefixWord ++ tailWord_3588440).sum := by decide
  have hdescent : baseEnd_3588440 < baseStart_3588440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588457 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 2, 4]
def baseStart_3588457 : Nat := 118140960795 + 3588457 * 2 ^ 59
def prefixEnd_3588457 : Nat := 4983230072969 + 3 ^ 40 * 3588457 * 2
def baseEnd_3588457 : Nat := 1228402165994114586122995

theorem tailTrace_3588457 : CollatzResearch.WordTrace tailWord_3588457 prefixEnd_3588457 1228402165994114586122995 := by
  unfold tailWord_3588457
  simp only [CollatzResearch.WordTrace]
  refine ⟨130881779160640623508459625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87254519440427082338973083 130881779160640623508459625)
  ·
    refine ⟨98161334370480467631344719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130881779160640623508459625 98161334370480467631344719)
    ·
      refine ⟨147242001555720701447017079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98161334370480467631344719 147242001555720701447017079)
      ·
        refine ⟨220863002333581052170525619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147242001555720701447017079 220863002333581052170525619)
        ·
          refine ⟨331294503500371578255788429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220863002333581052170525619 331294503500371578255788429)
          ·
            refine ⟨124235438812639341845920661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331294503500371578255788429 124235438812639341845920661)
            ·
              refine ⟨5823536194342469149027531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124235438812639341845920661 5823536194342469149027531)
              ·
                refine ⟨8735304291513703723541297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5823536194342469149027531 8735304291513703723541297)
                ·
                  refine ⟨6551478218635277792655973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8735304291513703723541297 6551478218635277792655973)
                  ·
                    refine ⟨1228402165994114586122995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551478218635277792655973 1228402165994114586122995)
                    ·
                      rfl

theorem cell22_3588457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 4].length) (baseStart_3588457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588457 prefixEnd_3588457 := by exact prefixLift 3588457
  have htrace : WordTrace (prefixWord ++ tailWord_3588457) baseStart_3588457 baseEnd_3588457 := by
    simpa [prefixWord, tailWord_3588457, baseEnd_3588457] using wordTrace_append hprefix tailTrace_3588457
  have hstable : (prefixWord ++ tailWord_3588457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588457).length < 2 ^ (prefixWord ++ tailWord_3588457).sum := by decide
  have hdescent : baseEnd_3588457 < baseStart_3588457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588504 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 5, 3]
def baseStart_3588504 : Nat := 118140960795 + 3588504 * 2 ^ 59
def prefixEnd_3588504 : Nat := 4983230072969 + 3 ^ 40 * 3588504 * 2
def baseEnd_3588504 : Nat := 1228418255054622130197851

theorem tailTrace_3588504 : CollatzResearch.WordTrace tailWord_3588504 prefixEnd_3588504 1228418255054622130197851 := by
  unfold tailWord_3588504
  simp only [CollatzResearch.WordTrace]
  refine ⟨65441746695735175267710283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87255662260980233690280377 65441746695735175267710283)
  ·
    refine ⟨98162620043602762901565425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65441746695735175267710283 98162620043602762901565425)
    ·
      refine ⟨73621965032702072176174069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98162620043602762901565425 73621965032702072176174069)
      ·
        refine ⟨6902059221815819266516319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73621965032702072176174069 6902059221815819266516319)
        ·
          refine ⟨10353088832723728899774479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6902059221815819266516319 10353088832723728899774479)
          ·
            refine ⟨15529633249085593349661719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10353088832723728899774479 15529633249085593349661719)
            ·
              refine ⟨23294449873628390024492579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15529633249085593349661719 23294449873628390024492579)
              ·
                refine ⟨34941674810442585036738869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23294449873628390024492579 34941674810442585036738869)
                ·
                  refine ⟨3275782013478992347194269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34941674810442585036738869 3275782013478992347194269)
                  ·
                    refine ⟨1228418255054622130197851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3275782013478992347194269 1228418255054622130197851)
                    ·
                      rfl

theorem cell22_3588504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_3588504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588504 prefixEnd_3588504 := by exact prefixLift 3588504
  have htrace : WordTrace (prefixWord ++ tailWord_3588504) baseStart_3588504 baseEnd_3588504 := by
    simpa [prefixWord, tailWord_3588504, baseEnd_3588504] using wordTrace_append hprefix tailTrace_3588504
  have hstable : (prefixWord ++ tailWord_3588504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588504).length < 2 ^ (prefixWord ++ tailWord_3588504).sum := by decide
  have hdescent : baseEnd_3588504 < baseStart_3588504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588577 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3588577 : Nat := 118140960795 + 3588577 * 2 ^ 59
def prefixEnd_3588577 : Nat := 4983230072969 + 3 ^ 40 * 3588577 * 2
def baseEnd_3588577 : Nat := 1228443244446474273122627

theorem tailTrace_3588577 : CollatzResearch.WordTrace tailWord_3588577 prefixEnd_3588577 1228443244446474273122627 := by
  unfold tailWord_3588577
  simp only [CollatzResearch.WordTrace]
  refine ⟨130886155920205884002827985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87257437280137256001885323 130886155920205884002827985)
  ·
    refine ⟨98164616940154413002120989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130886155920205884002827985 98164616940154413002120989)
    ·
      refine ⟨36811731352557904875795371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98164616940154413002120989 36811731352557904875795371)
      ·
        refine ⟨55217597028836857313693057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36811731352557904875795371 55217597028836857313693057)
        ·
          refine ⟨41413197771627642985269793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55217597028836857313693057 41413197771627642985269793)
          ·
            refine ⟨31059898328720732238952345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41413197771627642985269793 31059898328720732238952345)
            ·
              refine ⟨23294923746540549179214259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31059898328720732238952345 23294923746540549179214259)
              ·
                refine ⟨34942385619810823768821389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23294923746540549179214259 34942385619810823768821389)
                ·
                  refine ⟨13103394607429058913308021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34942385619810823768821389 13103394607429058913308021)
                  ·
                    refine ⟨1228443244446474273122627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13103394607429058913308021 1228443244446474273122627)
                    ·
                      rfl

theorem cell22_3588577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3588577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588577 prefixEnd_3588577 := by exact prefixLift 3588577
  have htrace : WordTrace (prefixWord ++ tailWord_3588577) baseStart_3588577 baseEnd_3588577 := by
    simpa [prefixWord, tailWord_3588577, baseEnd_3588577] using wordTrace_append hprefix tailTrace_3588577
  have hstable : (prefixWord ++ tailWord_3588577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588577).length < 2 ^ (prefixWord ++ tailWord_3588577).sum := by decide
  have hdescent : baseEnd_3588577 < baseStart_3588577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588607 : List Nat := [1, 1, 2, 2, 1, 2, 6, 7]
def baseStart_3588607 : Nat := 118140960795 + 3588607 * 2 ^ 59
def prefixEnd_3588607 : Nat := 4983230072969 + 3 ^ 40 * 3588607 * 2
def baseEnd_3588607 : Nat := 136494834895507132763615

theorem tailTrace_3588607 : CollatzResearch.WordTrace tailWord_3588607 prefixEnd_3588607 136494834895507132763615 := by
  unfold tailWord_3588607
  simp only [CollatzResearch.WordTrace]
  refine ⟨130887250110097199126420075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87258166740064799417613383 130887250110097199126420075)
  ·
    refine ⟨196330875165145798689630113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130887250110097199126420075 196330875165145798689630113)
    ·
      refine ⟨147248156373859349017222585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196330875165145798689630113 147248156373859349017222585)
      ·
        refine ⟨110436117280394511762916939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147248156373859349017222585 110436117280394511762916939)
        ·
          refine ⟨165654175920591767644375409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110436117280394511762916939 165654175920591767644375409)
          ·
            refine ⟨124240631940443825733281557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165654175920591767644375409 124240631940443825733281557)
            ·
              refine ⟨5823779622208304331247573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124240631940443825733281557 5823779622208304331247573)
              ·
                refine ⟨136494834895507132763615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5823779622208304331247573 136494834895507132763615)
                ·
                  rfl

theorem cell22_3588607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 7].length) (baseStart_3588607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588607 prefixEnd_3588607 := by exact prefixLift 3588607
  have htrace : WordTrace (prefixWord ++ tailWord_3588607) baseStart_3588607 baseEnd_3588607 := by
    simpa [prefixWord, tailWord_3588607, baseEnd_3588607] using wordTrace_append hprefix tailTrace_3588607
  have hstable : (prefixWord ++ tailWord_3588607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588607).length < 2 ^ (prefixWord ++ tailWord_3588607).sum := by decide
  have hdescent : baseEnd_3588607 < baseStart_3588607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588647 : List Nat := [1, 1, 7, 2, 1, 2, 2, 2, 4]
def baseStart_3588647 : Nat := 118140960795 + 3588647 * 2 ^ 59
def prefixEnd_3588647 : Nat := 4983230072969 + 3 ^ 40 * 3588647 * 2
def baseEnd_3588647 : Nat := 409489068959005807957471

theorem tailTrace_3588647 : CollatzResearch.WordTrace tailWord_3588647 prefixEnd_3588647 409489068959005807957471 := by
  unfold tailWord_3588647
  simp only [CollatzResearch.WordTrace]
  refine ⟨130888709029952285957876195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87259139353301523971917463 130888709029952285957876195)
  ·
    refine ⟨196333063544928428936814293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130888709029952285957876195 196333063544928428936814293)
    ·
      refine ⟨4601556176834260053206585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 196333063544928428936814293 4601556176834260053206585)
      ·
        refine ⟨3451167132625695039904939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4601556176834260053206585 3451167132625695039904939)
        ·
          refine ⟨5176750698938542559857409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451167132625695039904939 5176750698938542559857409)
          ·
            refine ⟨3882563024203906919893057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5176750698938542559857409 3882563024203906919893057)
            ·
              refine ⟨2911922268152930189919793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3882563024203906919893057 2911922268152930189919793)
              ·
                refine ⟨2183941701114697642439845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2911922268152930189919793 2183941701114697642439845)
                ·
                  refine ⟨409489068959005807957471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2183941701114697642439845 409489068959005807957471)
                  ·
                    rfl

theorem cell22_3588647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 4].length) (baseStart_3588647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588647 prefixEnd_3588647 := by exact prefixLift 3588647
  have htrace : WordTrace (prefixWord ++ tailWord_3588647) baseStart_3588647 baseEnd_3588647 := by
    simpa [prefixWord, tailWord_3588647, baseEnd_3588647] using wordTrace_append hprefix tailTrace_3588647
  have hstable : (prefixWord ++ tailWord_3588647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588647).length < 2 ^ (prefixWord ++ tailWord_3588647).sum := by decide
  have hdescent : baseEnd_3588647 < baseStart_3588647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588652 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 7]
def baseStart_3588652 : Nat := 118140960795 + 3588652 * 2 ^ 59
def prefixEnd_3588652 : Nat := 4983230072969 + 3 ^ 40 * 3588652 * 2
def baseEnd_3588652 : Nat := 409489639493066359165799

theorem tailTrace_3588652 : CollatzResearch.WordTrace tailWord_3588652 prefixEnd_3588652 409489639493066359165799 := by
  unfold tailWord_3588652
  simp only [CollatzResearch.WordTrace]
  refine ⟨65444445697467085905904105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87259260929956114541205473 65444445697467085905904105)
  ·
    refine ⟨49083334273100314429428079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65444445697467085905904105 49083334273100314429428079)
    ·
      refine ⟨73625001409650471644142119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49083334273100314429428079 73625001409650471644142119)
      ·
        refine ⟨110437502114475707466213179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73625001409650471644142119 110437502114475707466213179)
        ·
          refine ⟨165656253171713561199319769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110437502114475707466213179 165656253171713561199319769)
          ·
            refine ⟨124242189878785170899489827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165656253171713561199319769 124242189878785170899489827)
            ·
              refine ⟨186363284818177756349234741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124242189878785170899489827 186363284818177756349234741)
              ·
                refine ⟨17471557951704164657740757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186363284818177756349234741 17471557951704164657740757)
                ·
                  refine ⟨409489639493066359165799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17471557951704164657740757 409489639493066359165799)
                  ·
                    rfl

theorem cell22_3588652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_3588652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588652 prefixEnd_3588652 := by exact prefixLift 3588652
  have htrace : WordTrace (prefixWord ++ tailWord_3588652) baseStart_3588652 baseEnd_3588652 := by
    simpa [prefixWord, tailWord_3588652, baseEnd_3588652] using wordTrace_append hprefix tailTrace_3588652
  have hstable : (prefixWord ++ tailWord_3588652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588652).length < 2 ^ (prefixWord ++ tailWord_3588652).sum := by decide
  have hdescent : baseEnd_3588652 < baseStart_3588652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588733 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 1, 4]
def baseStart_3588733 : Nat := 118140960795 + 3588733 * 2 ^ 59
def prefixEnd_3588733 : Nat := 4983230072969 + 3 ^ 40 * 3588733 * 2
def baseEnd_3588733 : Nat := 1228496646434541866222149

theorem tailTrace_3588733 : CollatzResearch.WordTrace tailWord_3588733 prefixEnd_3588733 1228496646434541866222149 := by
  unfold tailWord_3588733
  simp only [CollatzResearch.WordTrace]
  refine ⟨130891845707640722645506853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87261230471760481763671235 130891845707640722645506853)
  ·
    refine ⟨24542221070182635496032535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130891845707640722645506853 24542221070182635496032535)
    ·
      refine ⟨36813331605273953244048803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24542221070182635496032535 36813331605273953244048803)
      ·
        refine ⟨55219997407910929866073205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36813331605273953244048803 55219997407910929866073205)
        ·
          refine ⟨5176874756991649674944363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55219997407910929866073205 5176874756991649674944363)
          ·
            refine ⟨7765312135487474512416545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5176874756991649674944363 7765312135487474512416545)
            ·
              refine ⟨5823984101615605884312409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7765312135487474512416545 5823984101615605884312409)
              ·
                refine ⟨4367988076211704413234307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5823984101615605884312409 4367988076211704413234307)
                ·
                  refine ⟨6551982114317556619851461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4367988076211704413234307 6551982114317556619851461)
                  ·
                    refine ⟨1228496646434541866222149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6551982114317556619851461 1228496646434541866222149)
                    ·
                      rfl

theorem cell22_3588733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_3588733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588733 prefixEnd_3588733 := by exact prefixLift 3588733
  have htrace : WordTrace (prefixWord ++ tailWord_3588733) baseStart_3588733 baseEnd_3588733 := by
    simpa [prefixWord, tailWord_3588733, baseEnd_3588733] using wordTrace_append hprefix tailTrace_3588733
  have hstable : (prefixWord ++ tailWord_3588733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588733).length < 2 ^ (prefixWord ++ tailWord_3588733).sum := by decide
  have hdescent : baseEnd_3588733 < baseStart_3588733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588836 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_3588836 : Nat := 118140960795 + 3588836 * 2 ^ 59
def prefixEnd_3588836 : Nat := 4983230072969 + 3 ^ 40 * 3588836 * 2
def baseEnd_3588836 : Nat := 1228531905439483930896833

theorem tailTrace_3588836 : CollatzResearch.WordTrace tailWord_3588836 prefixEnd_3588836 1228531905439483930896833 := by
  unfold tailWord_3588836
  simp only [CollatzResearch.WordTrace]
  refine ⟨65447801213133785618253181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87263734950845047491004241 65447801213133785618253181)
  ·
    refine ⟨24542925454925169606844943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65447801213133785618253181 24542925454925169606844943)
    ·
      refine ⟨36814388182387754410267415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24542925454925169606844943 36814388182387754410267415)
      ·
        refine ⟨55221582273581631615401123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36814388182387754410267415 55221582273581631615401123)
        ·
          refine ⟨82832373410372447423101685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55221582273581631615401123 82832373410372447423101685)
          ·
            refine ⟨7765535007222416945915783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82832373410372447423101685 7765535007222416945915783)
            ·
              refine ⟨11648302510833625418873675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7765535007222416945915783 11648302510833625418873675)
              ·
                refine ⟨17472453766250438128310513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11648302510833625418873675 17472453766250438128310513)
                ·
                  refine ⟨13104340324687828596232885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17472453766250438128310513 13104340324687828596232885)
                  ·
                    refine ⟨1228531905439483930896833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13104340324687828596232885 1228531905439483930896833)
                    ·
                      rfl

theorem cell22_3588836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_3588836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588836 prefixEnd_3588836 := by exact prefixLift 3588836
  have htrace : WordTrace (prefixWord ++ tailWord_3588836) baseStart_3588836 baseEnd_3588836 := by
    simpa [prefixWord, tailWord_3588836, baseEnd_3588836] using wordTrace_append hprefix tailTrace_3588836
  have hstable : (prefixWord ++ tailWord_3588836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588836).length < 2 ^ (prefixWord ++ tailWord_3588836).sum := by decide
  have hdescent : baseEnd_3588836 < baseStart_3588836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588851 : List Nat := [1, 1, 1, 2, 2, 3, 1, 6, 1, 4]
def baseStart_3588851 : Nat := 118140960795 + 3588851 * 2 ^ 59
def prefixEnd_3588851 : Nat := 4983230072969 + 3 ^ 40 * 3588851 * 2
def baseEnd_3588851 : Nat := 1228537040246028891771787

theorem tailTrace_3588851 : CollatzResearch.WordTrace tailWord_3588851 prefixEnd_3588851 1228537040246028891771787 := by
  unfold tailWord_3588851
  simp only [CollatzResearch.WordTrace]
  refine ⟨130896149521213228798302407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87264099680808819198868271 130896149521213228798302407)
  ·
    refine ⟨196344224281819843197453611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130896149521213228798302407 196344224281819843197453611)
    ·
      refine ⟨294516336422729764796180417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196344224281819843197453611 294516336422729764796180417)
      ·
        refine ⟨220887252317047323597135313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294516336422729764796180417 220887252317047323597135313)
        ·
          refine ⟨165665439237785492697851485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220887252317047323597135313 165665439237785492697851485)
          ·
            refine ⟨62124539714169559761694307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165665439237785492697851485 62124539714169559761694307)
            ·
              refine ⟨93186809571254339642541461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62124539714169559761694307 93186809571254339642541461)
              ·
                refine ⟨4368131698652547170744131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 93186809571254339642541461 4368131698652547170744131)
                ·
                  refine ⟨6552197547978820756116197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368131698652547170744131 6552197547978820756116197)
                  ·
                    refine ⟨1228537040246028891771787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552197547978820756116197 1228537040246028891771787)
                    ·
                      rfl

theorem cell22_3588851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 1, 4].length) (baseStart_3588851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588851 prefixEnd_3588851 := by exact prefixLift 3588851
  have htrace : WordTrace (prefixWord ++ tailWord_3588851) baseStart_3588851 baseEnd_3588851 := by
    simpa [prefixWord, tailWord_3588851, baseEnd_3588851] using wordTrace_append hprefix tailTrace_3588851
  have hstable : (prefixWord ++ tailWord_3588851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588851).length < 2 ^ (prefixWord ++ tailWord_3588851).sum := by decide
  have hdescent : baseEnd_3588851 < baseStart_3588851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588868 : List Nat := [2, 3, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3588868 : Nat := 118140960795 + 3588868 * 2 ^ 59
def prefixEnd_3588868 : Nat := 4983230072969 + 3 ^ 40 * 3588868 * 2
def baseEnd_3588868 : Nat := 1228542859693446514096735

theorem tailTrace_3588868 : CollatzResearch.WordTrace tailWord_3588868 prefixEnd_3588868 1228542859693446514096735 := by
  unfold tailWord_3588868
  simp only [CollatzResearch.WordTrace]
  refine ⟨65448384781075820350835629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87264513041434427134447505 65448384781075820350835629)
  ·
    refine ⟨24543144292903432631563361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65448384781075820350835629 24543144292903432631563361)
    ·
      refine ⟨18407358219677574473672521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24543144292903432631563361 18407358219677574473672521)
      ·
        refine ⟨13805518664758180855254391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18407358219677574473672521 13805518664758180855254391)
        ·
          refine ⟨20708277997137271282881587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13805518664758180855254391 20708277997137271282881587)
          ·
            refine ⟨31062416995705906924322381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20708277997137271282881587 31062416995705906924322381)
            ·
              refine ⟨11648406373389715096620893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31062416995705906924322381 11648406373389715096620893)
              ·
                refine ⟨4368152390021143161232835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11648406373389715096620893 4368152390021143161232835)
                ·
                  refine ⟨6552228585031714741849253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368152390021143161232835 6552228585031714741849253)
                  ·
                    refine ⟨1228542859693446514096735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552228585031714741849253 1228542859693446514096735)
                    ·
                      rfl

theorem cell22_3588868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3588868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588868 prefixEnd_3588868 := by exact prefixLift 3588868
  have htrace : WordTrace (prefixWord ++ tailWord_3588868) baseStart_3588868 baseEnd_3588868 := by
    simpa [prefixWord, tailWord_3588868, baseEnd_3588868] using wordTrace_append hprefix tailTrace_3588868
  have hstable : (prefixWord ++ tailWord_3588868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588868).length < 2 ^ (prefixWord ++ tailWord_3588868).sum := by decide
  have hdescent : baseEnd_3588868 < baseStart_3588868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588896 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 1, 6]
def baseStart_3588896 : Nat := 118140960795 + 3588896 * 2 ^ 59
def prefixEnd_3588896 : Nat := 4983230072969 + 3 ^ 40 * 3588896 * 2
def baseEnd_3588896 : Nat := 1228552444665663774396649

theorem tailTrace_3588896 : CollatzResearch.WordTrace tailWord_3588896 prefixEnd_3588896 1228552444665663774396649 := by
  unfold tailWord_3588896
  simp only [CollatzResearch.WordTrace]
  refine ⟨65448895403025100741845271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87265193870700134322460361 65448895403025100741845271)
  ·
    refine ⟨98173343104537651112767907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65448895403025100741845271 98173343104537651112767907)
    ·
      refine ⟨147260014656806476669151861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98173343104537651112767907 147260014656806476669151861)
      ·
        refine ⟨13805626374075607187732987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147260014656806476669151861 13805626374075607187732987)
        ·
          refine ⟨20708439561113410781599481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13805626374075607187732987 20708439561113410781599481)
          ·
            refine ⟨15531329670835058086199611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20708439561113410781599481 15531329670835058086199611)
            ·
              refine ⟨23296994506252587129299417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15531329670835058086199611 23296994506252587129299417)
              ·
                refine ⟨17472745879689440346974563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23296994506252587129299417 17472745879689440346974563)
                ·
                  refine ⟨26209118819534160520461845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17472745879689440346974563 26209118819534160520461845)
                  ·
                    refine ⟨1228552444665663774396649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26209118819534160520461845 1228552444665663774396649)
                    ·
                      rfl

theorem cell22_3588896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_3588896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588896 prefixEnd_3588896 := by exact prefixLift 3588896
  have htrace : WordTrace (prefixWord ++ tailWord_3588896) baseStart_3588896 baseEnd_3588896 := by
    simpa [prefixWord, tailWord_3588896, baseEnd_3588896] using wordTrace_append hprefix tailTrace_3588896
  have hstable : (prefixWord ++ tailWord_3588896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588896).length < 2 ^ (prefixWord ++ tailWord_3588896).sum := by decide
  have hdescent : baseEnd_3588896 < baseStart_3588896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588898 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3588898 : Nat := 118140960795 + 3588898 * 2 ^ 59
def prefixEnd_3588898 : Nat := 4983230072969 + 3 ^ 40 * 3588898 * 2
def baseEnd_3588898 : Nat := 1228553129306536435846643

theorem tailTrace_3588898 : CollatzResearch.WordTrace tailWord_3588898 prefixEnd_3588898 1228553129306536435846643 := by
  unfold tailWord_3588898
  simp only [CollatzResearch.WordTrace]
  refine ⟨32724465938010738956315837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87265242501361970550175565 32724465938010738956315837)
  ·
    refine ⟨12271674726754027108618439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32724465938010738956315837 12271674726754027108618439)
    ·
      refine ⟨18407512090131040662927659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12271674726754027108618439 18407512090131040662927659)
      ·
        refine ⟨27611268135196560994391489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18407512090131040662927659 27611268135196560994391489)
        ·
          refine ⟨20708451101397420745793617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27611268135196560994391489 20708451101397420745793617)
          ·
            refine ⟨15531338326048065559345213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20708451101397420745793617 15531338326048065559345213)
            ·
              refine ⟨5824251872268024584754455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15531338326048065559345213 5824251872268024584754455)
              ·
                refine ⟨8736377808402036877131683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824251872268024584754455 8736377808402036877131683)
                ·
                  refine ⟨13104566712603055315697525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8736377808402036877131683 13104566712603055315697525)
                  ·
                    refine ⟨1228553129306536435846643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13104566712603055315697525 1228553129306536435846643)
                    ·
                      rfl

theorem cell22_3588898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3588898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588898 prefixEnd_3588898 := by exact prefixLift 3588898
  have htrace : WordTrace (prefixWord ++ tailWord_3588898) baseStart_3588898 baseEnd_3588898 := by
    simpa [prefixWord, tailWord_3588898, baseEnd_3588898] using wordTrace_append hprefix tailTrace_3588898
  have hstable : (prefixWord ++ tailWord_3588898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588898).length < 2 ^ (prefixWord ++ tailWord_3588898).sum := by decide
  have hdescent : baseEnd_3588898 < baseStart_3588898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3588934 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3588934 : Nat := 118140960795 + 3588934 * 2 ^ 59
def prefixEnd_3588934 : Nat := 4983230072969 + 3 ^ 40 * 3588934 * 2
def baseEnd_3588934 : Nat := 409521817614081447315511

theorem tailTrace_3588934 : CollatzResearch.WordTrace tailWord_3588934 prefixEnd_3588934 409521817614081447315511 := by
  unfold tailWord_3588934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090599274372266686674183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87266117853275022649049237 4090599274372266686674183)
  ·
    refine ⟨6135898911558400030011275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4090599274372266686674183 6135898911558400030011275)
    ·
      refine ⟨9203848367337600045016913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6135898911558400030011275 9203848367337600045016913)
      ·
        refine ⟨6902886275503200033762685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9203848367337600045016913 6902886275503200033762685)
        ·
          refine ⟨2588582353313700012661007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6902886275503200033762685 2588582353313700012661007)
          ·
            refine ⟨3882873529970550018991511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588582353313700012661007 3882873529970550018991511)
            ·
              refine ⟨5824310294955825028487267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3882873529970550018991511 5824310294955825028487267)
              ·
                refine ⟨8736465442433737542730901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5824310294955825028487267 8736465442433737542730901)
                ·
                  refine ⟨409521817614081447315511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8736465442433737542730901 409521817614081447315511)
                  ·
                    rfl

theorem cell22_3588934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3588934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3588934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3588934 prefixEnd_3588934 := by exact prefixLift 3588934
  have htrace : WordTrace (prefixWord ++ tailWord_3588934) baseStart_3588934 baseEnd_3588934 := by
    simpa [prefixWord, tailWord_3588934, baseEnd_3588934] using wordTrace_append hprefix tailTrace_3588934
  have hstable : (prefixWord ++ tailWord_3588934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3588934).length < 2 ^ (prefixWord ++ tailWord_3588934).sum := by decide
  have hdescent : baseEnd_3588934 < baseStart_3588934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3588934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589033 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 4, 3]
def baseStart_3589033 : Nat := 118140960795 + 3589033 * 2 ^ 59
def prefixEnd_3589033 : Nat := 4983230072969 + 3 ^ 40 * 3589033 * 2
def baseEnd_3589033 : Nat := 1228599342565441083721229

theorem tailTrace_3589033 : CollatzResearch.WordTrace tailWord_3589033 prefixEnd_3589033 1228599342565441083721229 := by
  unfold tailWord_3589033
  simp only [CollatzResearch.WordTrace]
  refine ⟨130902787606553873881427753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87268525071035915920951835 130902787606553873881427753)
  ·
    refine ⟨98177090704915405411070815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130902787606553873881427753 98177090704915405411070815)
    ·
      refine ⟨147265636057373108116606223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98177090704915405411070815 147265636057373108116606223)
      ·
        refine ⟨220898454086059662174909335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147265636057373108116606223 220898454086059662174909335)
        ·
          refine ⟨331347681129089493262364003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220898454086059662174909335 331347681129089493262364003)
          ·
            refine ⟨497021521693634239893546005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331347681129089493262364003 497021521693634239893546005)
            ·
              refine ⟨23297883829389104995009969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 497021521693634239893546005 23297883829389104995009969)
              ·
                refine ⟨17473412872041828746257477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23297883829389104995009969 17473412872041828746257477)
                ·
                  refine ⟨3276264913507842889923277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17473412872041828746257477 3276264913507842889923277)
                  ·
                    refine ⟨1228599342565441083721229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276264913507842889923277 1228599342565441083721229)
                    ·
                      rfl

theorem cell22_3589033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 3].length) (baseStart_3589033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589033 prefixEnd_3589033 := by exact prefixLift 3589033
  have htrace : WordTrace (prefixWord ++ tailWord_3589033) baseStart_3589033 baseEnd_3589033 := by
    simpa [prefixWord, tailWord_3589033, baseEnd_3589033] using wordTrace_append hprefix tailTrace_3589033
  have hstable : (prefixWord ++ tailWord_3589033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589033).length < 2 ^ (prefixWord ++ tailWord_3589033).sum := by decide
  have hdescent : baseEnd_3589033 < baseStart_3589033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589067 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 2, 3]
def baseStart_3589067 : Nat := 118140960795 + 3589067 * 2 ^ 59
def prefixEnd_3589067 : Nat := 4983230072969 + 3 ^ 40 * 3589067 * 2
def baseEnd_3589067 : Nat := 1228610981460276328371125

theorem tailTrace_3589067 : CollatzResearch.WordTrace tailWord_3589067 prefixEnd_3589067 1228610981460276328371125 := by
  unfold tailWord_3589067
  simp only [CollatzResearch.WordTrace]
  refine ⟨130904027688430697688165455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87269351792287131792110303 130904027688430697688165455)
  ·
    refine ⟨196356041532646046532248183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130904027688430697688165455 196356041532646046532248183)
    ·
      refine ⟨294534062298969069798372275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196356041532646046532248183 294534062298969069798372275)
      ·
        refine ⟨441801093448453604697558413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294534062298969069798372275 441801093448453604697558413)
        ·
          refine ⟨165675410043170101761584405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441801093448453604697558413 165675410043170101761584405)
          ·
            refine ⟨7766034845773598520074269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165675410043170101761584405 7766034845773598520074269)
            ·
              refine ⟨2912263067165099445027851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7766034845773598520074269 2912263067165099445027851)
              ·
                refine ⟨4368394600747649167541777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912263067165099445027851 4368394600747649167541777)
                ·
                  refine ⟨3276295950560736875656333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4368394600747649167541777 3276295950560736875656333)
                  ·
                    refine ⟨1228610981460276328371125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276295950560736875656333 1228610981460276328371125)
                    ·
                      rfl

theorem cell22_3589067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 3].length) (baseStart_3589067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589067 prefixEnd_3589067 := by exact prefixLift 3589067
  have htrace : WordTrace (prefixWord ++ tailWord_3589067) baseStart_3589067 baseEnd_3589067 := by
    simpa [prefixWord, tailWord_3589067, baseEnd_3589067] using wordTrace_append hprefix tailTrace_3589067
  have hstable : (prefixWord ++ tailWord_3589067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589067).length < 2 ^ (prefixWord ++ tailWord_3589067).sum := by decide
  have hdescent : baseEnd_3589067 < baseStart_3589067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589080 : List Nat := [2, 1, 2, 2, 2, 5, 2, 6]
def baseStart_3589080 : Nat := 118140960795 + 3589080 * 2 ^ 59
def prefixEnd_3589080 : Nat := 4983230072969 + 3 ^ 40 * 3589080 * 2
def baseEnd_3589080 : Nat := 136512825736216514199565

theorem tailTrace_3589080 : CollatzResearch.WordTrace tailWord_3589080 prefixEnd_3589080 136512825736216514199565 := by
  unfold tailWord_3589080
  simp only [CollatzResearch.WordTrace]
  refine ⟨65452250918691800454194347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87269667891589067272259129 65452250918691800454194347)
  ·
    refine ⟨98178376378037700681291521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65452250918691800454194347 98178376378037700681291521)
    ·
      refine ⟨73633782283528275510968641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98178376378037700681291521 73633782283528275510968641)
      ·
        refine ⟨55225336712646206633226481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73633782283528275510968641 55225336712646206633226481)
        ·
          refine ⟨41419002534484654974919861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55225336712646206633226481 41419002534484654974919861)
          ·
            refine ⟨3883031487607936403898737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41419002534484654974919861 3883031487607936403898737)
            ·
              refine ⟨2912273615705952302924053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883031487607936403898737 2912273615705952302924053)
              ·
                refine ⟨136512825736216514199565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2912273615705952302924053 136512825736216514199565)
                ·
                  rfl

theorem cell22_3589080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 6].length) (baseStart_3589080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589080 prefixEnd_3589080 := by exact prefixLift 3589080
  have htrace : WordTrace (prefixWord ++ tailWord_3589080) baseStart_3589080 baseEnd_3589080 := by
    simpa [prefixWord, tailWord_3589080, baseEnd_3589080] using wordTrace_append hprefix tailTrace_3589080
  have hstable : (prefixWord ++ tailWord_3589080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589080).length < 2 ^ (prefixWord ++ tailWord_3589080).sum := by decide
  have hdescent : baseEnd_3589080 < baseStart_3589080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589118 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3589118 : Nat := 118140960795 + 3589118 * 2 ^ 59
def prefixEnd_3589118 : Nat := 4983230072969 + 3 ^ 40 * 3589118 * 2
def baseEnd_3589118 : Nat := 1228628439802529195345969

theorem tailTrace_3589118 : CollatzResearch.WordTrace tailWord_3589118 prefixEnd_3589118 1228628439802529195345969 := by
  unfold tailWord_3589118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16363235976405741674784001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87270591874163955598848005 16363235976405741674784001)
  ·
    refine ⟨12272426982304306256088001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16363235976405741674784001 12272426982304306256088001)
    ·
      refine ⟨9204320236728229692066001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12272426982304306256088001 9204320236728229692066001)
      ·
        refine ⟨6903240177546172269049501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9204320236728229692066001 6903240177546172269049501)
        ·
          refine ⟨2588715066579814600893563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6903240177546172269049501 2588715066579814600893563)
          ·
            refine ⟨3883072599869721901340345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588715066579814600893563 3883072599869721901340345)
            ·
              refine ⟨2912304449902291426005259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883072599869721901340345 2912304449902291426005259)
              ·
                refine ⟨4368456674853437139007889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912304449902291426005259 4368456674853437139007889)
                ·
                  refine ⟨3276342506140077854255917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4368456674853437139007889 3276342506140077854255917)
                  ·
                    refine ⟨1228628439802529195345969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276342506140077854255917 1228628439802529195345969)
                    ·
                      rfl

theorem cell22_3589118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3589118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589118 prefixEnd_3589118 := by exact prefixLift 3589118
  have htrace : WordTrace (prefixWord ++ tailWord_3589118) baseStart_3589118 baseEnd_3589118 := by
    simpa [prefixWord, tailWord_3589118, baseEnd_3589118] using wordTrace_append hprefix tailTrace_3589118
  have hstable : (prefixWord ++ tailWord_3589118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589118).length < 2 ^ (prefixWord ++ tailWord_3589118).sum := by decide
  have hdescent : baseEnd_3589118 < baseStart_3589118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589168 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 3, 5]
def baseStart_3589168 : Nat := 118140960795 + 3589168 * 2 ^ 59
def prefixEnd_3589168 : Nat := 4983230072969 + 3 ^ 40 * 3589168 * 2
def baseEnd_3589168 : Nat := 1228645555824345731595815

theorem tailTrace_3589168 : CollatzResearch.WordTrace tailWord_3589168 prefixEnd_3589168 1228645555824345731595815 := by
  unfold tailWord_3589168
  simp only [CollatzResearch.WordTrace]
  refine ⟨65453855730532395968796079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87271807640709861291728105 65453855730532395968796079)
  ·
    refine ⟨98180783595798593953194119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65453855730532395968796079 98180783595798593953194119)
    ·
      refine ⟨147271175393697890929791179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98180783595798593953194119 147271175393697890929791179)
      ·
        refine ⟨220906763090546836394686769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147271175393697890929791179 220906763090546836394686769)
        ·
          refine ⟨165680072317910127296015077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220906763090546836394686769 165680072317910127296015077)
          ·
            refine ⟨31065013559608148868002827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165680072317910127296015077 31065013559608148868002827)
            ·
              refine ⟨46597520339412223302004241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31065013559608148868002827 46597520339412223302004241)
              ·
                refine ⟨34948140254559167476503181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46597520339412223302004241 34948140254559167476503181)
                ·
                  refine ⟨13105552595459687803688693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34948140254559167476503181 13105552595459687803688693)
                  ·
                    refine ⟨1228645555824345731595815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13105552595459687803688693 1228645555824345731595815)
                    ·
                      rfl

theorem cell22_3589168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_3589168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589168 prefixEnd_3589168 := by exact prefixLift 3589168
  have htrace : WordTrace (prefixWord ++ tailWord_3589168) baseStart_3589168 baseEnd_3589168 := by
    simpa [prefixWord, tailWord_3589168, baseEnd_3589168] using wordTrace_append hprefix tailTrace_3589168
  have hstable : (prefixWord ++ tailWord_3589168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589168).length < 2 ^ (prefixWord ++ tailWord_3589168).sum := by decide
  have hdescent : baseEnd_3589168 < baseStart_3589168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589172 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3589172 : Nat := 118140960795 + 3589172 * 2 ^ 59
def prefixEnd_3589172 : Nat := 4983230072969 + 3 ^ 40 * 3589172 * 2
def baseEnd_3589172 : Nat := 1228646925106091054495803

theorem tailTrace_3589172 : CollatzResearch.WordTrace tailWord_3589172 prefixEnd_3589172 1228646925106091054495803 := by
  unfold tailWord_3589172
  simp only [CollatzResearch.WordTrace]
  refine ⟨65453928676525150310368885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87271904902033533747158513 65453928676525150310368885)
  ·
    refine ⟨6136305813424232841597083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65453928676525150310368885 6136305813424232841597083)
    ·
      refine ⟨9204458720136349262395625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6136305813424232841597083 9204458720136349262395625)
      ·
        refine ⟨6903344040102261946796719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9204458720136349262395625 6903344040102261946796719)
        ·
          refine ⟨10355016060153392920195079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6903344040102261946796719 10355016060153392920195079)
          ·
            refine ⟨15532524090230089380292619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10355016060153392920195079 15532524090230089380292619)
            ·
              refine ⟨23298786135345134070438929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15532524090230089380292619 23298786135345134070438929)
              ·
                refine ⟨17474089601508850552829197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23298786135345134070438929 17474089601508850552829197)
                ·
                  refine ⟨6552783600565818957310949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17474089601508850552829197 6552783600565818957310949)
                  ·
                    refine ⟨1228646925106091054495803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552783600565818957310949 1228646925106091054495803)
                    ·
                      rfl

theorem cell22_3589172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3589172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589172 prefixEnd_3589172 := by exact prefixLift 3589172
  have htrace : WordTrace (prefixWord ++ tailWord_3589172) baseStart_3589172 baseEnd_3589172 := by
    simpa [prefixWord, tailWord_3589172, baseEnd_3589172] using wordTrace_append hprefix tailTrace_3589172
  have hstable : (prefixWord ++ tailWord_3589172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589172).length < 2 ^ (prefixWord ++ tailWord_3589172).sum := by decide
  have hdescent : baseEnd_3589172 < baseStart_3589172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589183 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 1, 6]
def baseStart_3589183 : Nat := 118140960795 + 3589183 * 2 ^ 59
def prefixEnd_3589183 : Nat := 4983230072969 + 3 ^ 40 * 3589183 * 2
def baseEnd_3589183 : Nat := 1228650690630890692470769

theorem tailTrace_3589183 : CollatzResearch.WordTrace tailWord_3589183 prefixEnd_3589183 1228650690630890692470769 := by
  unfold tailWord_3589183
  simp only [CollatzResearch.WordTrace]
  refine ⟨130908258556010449499388203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87272172370673632999592135 130908258556010449499388203)
  ·
    refine ⟨196362387834015674249082305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130908258556010449499388203 196362387834015674249082305)
    ·
      refine ⟨147271790875511755686811729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196362387834015674249082305 147271790875511755686811729)
      ·
        refine ⟨110453843156633816765108797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147271790875511755686811729 110453843156633816765108797)
        ·
          refine ⟨41420191183737681286915799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110453843156633816765108797 41420191183737681286915799)
          ·
            refine ⟨62130286775606521930373699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41420191183737681286915799 62130286775606521930373699)
            ·
              refine ⟨93195430163409782895560549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62130286775606521930373699 93195430163409782895560549)
              ·
                refine ⟨17474143155639334292917603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93195430163409782895560549 17474143155639334292917603)
                ·
                  refine ⟨26211214733459001439376405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17474143155639334292917603 26211214733459001439376405)
                  ·
                    refine ⟨1228650690630890692470769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26211214733459001439376405 1228650690630890692470769)
                    ·
                      rfl

theorem cell22_3589183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_3589183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589183 prefixEnd_3589183 := by exact prefixLift 3589183
  have htrace : WordTrace (prefixWord ++ tailWord_3589183) baseStart_3589183 baseEnd_3589183 := by
    simpa [prefixWord, tailWord_3589183, baseEnd_3589183] using wordTrace_append hprefix tailTrace_3589183
  have hstable : (prefixWord ++ tailWord_3589183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589183).length < 2 ^ (prefixWord ++ tailWord_3589183).sum := by decide
  have hdescent : baseEnd_3589183 < baseStart_3589183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589206 : List Nat := [5, 2, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3589206 : Nat := 118140960795 + 3589206 * 2 ^ 59
def prefixEnd_3589206 : Nat := 4983230072969 + 3 ^ 40 * 3589206 * 2
def baseEnd_3589206 : Nat := 1228658564000926299145699

theorem tailTrace_3589206 : CollatzResearch.WordTrace tailWord_3589206 prefixEnd_3589206 1228658564000926299145699 := by
  unfold tailWord_3589206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8181818589682945276717217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87272731623284749618316981 8181818589682945276717217)
  ·
    refine ⟨6136363942262208957537913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8181818589682945276717217 6136363942262208957537913)
    ·
      refine ⟨4602272956696656718153435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6136363942262208957537913 4602272956696656718153435)
      ·
        refine ⟨6903409435044985077230153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602272956696656718153435 6903409435044985077230153)
        ·
          refine ⟨5177557076283738807922615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6903409435044985077230153 5177557076283738807922615)
          ·
            refine ⟨7766335614425608211883923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177557076283738807922615 7766335614425608211883923)
            ·
              refine ⟨11649503421638412317825885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7766335614425608211883923 11649503421638412317825885)
              ·
                refine ⟨4368563783114404619184707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11649503421638412317825885 4368563783114404619184707)
                ·
                  refine ⟨6552845674671606928777061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368563783114404619184707 6552845674671606928777061)
                  ·
                    refine ⟨1228658564000926299145699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6552845674671606928777061 1228658564000926299145699)
                    ·
                      rfl

theorem cell22_3589206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3589206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589206 prefixEnd_3589206 := by exact prefixLift 3589206
  have htrace : WordTrace (prefixWord ++ tailWord_3589206) baseStart_3589206 baseEnd_3589206 := by
    simpa [prefixWord, tailWord_3589206, baseEnd_3589206] using wordTrace_append hprefix tailTrace_3589206
  have hstable : (prefixWord ++ tailWord_3589206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589206).length < 2 ^ (prefixWord ++ tailWord_3589206).sum := by decide
  have hdescent : baseEnd_3589206 < baseStart_3589206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589281 : List Nat := [1, 2, 3, 3, 1, 1, 5, 2, 1, 3]
def baseStart_3589281 : Nat := 118140960795 + 3589281 * 2 ^ 59
def prefixEnd_3589281 : Nat := 4983230072969 + 3 ^ 40 * 3589281 * 2
def baseEnd_3589281 : Nat := 1228684238033651103520469

theorem tailTrace_3589281 : CollatzResearch.WordTrace tailWord_3589281 prefixEnd_3589281 1228684238033651103520469 := by
  unfold tailWord_3589281
  simp only [CollatzResearch.WordTrace]
  refine ⟨130911832909655412236455697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87274555273103608157637131 130911832909655412236455697)
  ·
    refine ⟨98183874682241559177341773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130911832909655412236455697 98183874682241559177341773)
    ·
      refine ⟨36818953005840584691503165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98183874682241559177341773 36818953005840584691503165)
      ·
        refine ⟨13807107377190219259313687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36818953005840584691503165 13807107377190219259313687)
        ·
          refine ⟨20710661065785328888970531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807107377190219259313687 20710661065785328888970531)
          ·
            refine ⟨31065991598677993333455797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20710661065785328888970531 31065991598677993333455797)
            ·
              refine ⟨2912436712376061875011481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31065991598677993333455797 2912436712376061875011481)
              ·
                refine ⟨2184327534282046406258611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912436712376061875011481 2184327534282046406258611)
                ·
                  refine ⟨3276491301423069609387917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184327534282046406258611 3276491301423069609387917)
                  ·
                    refine ⟨1228684238033651103520469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276491301423069609387917 1228684238033651103520469)
                    ·
                      rfl

theorem cell22_3589281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_3589281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589281 prefixEnd_3589281 := by exact prefixLift 3589281
  have htrace : WordTrace (prefixWord ++ tailWord_3589281) baseStart_3589281 baseEnd_3589281 := by
    simpa [prefixWord, tailWord_3589281, baseEnd_3589281] using wordTrace_append hprefix tailTrace_3589281
  have hstable : (prefixWord ++ tailWord_3589281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589281).length < 2 ^ (prefixWord ++ tailWord_3589281).sum := by decide
  have hdescent : baseEnd_3589281 < baseStart_3589281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589320 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 3, 5]
def baseStart_3589320 : Nat := 118140960795 + 3589320 * 2 ^ 59
def prefixEnd_3589320 : Nat := 4983230072969 + 3 ^ 40 * 3589320 * 2
def baseEnd_3589320 : Nat := 1228697588530668001795349

theorem tailTrace_3589320 : CollatzResearch.WordTrace tailWord_3589320 prefixEnd_3589320 1228697588530668001795349 := by
  unfold tailWord_3589320
  simp only [CollatzResearch.WordTrace]
  refine ⟨65456627678257060948562707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87275503571009414598083609 65456627678257060948562707)
  ·
    refine ⟨98184941517385591422844061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65456627678257060948562707 98184941517385591422844061)
    ·
      refine ⟨36819353069019596783566523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98184941517385591422844061 36819353069019596783566523)
      ·
        refine ⟨55229029603529395175349785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36819353069019596783566523 55229029603529395175349785)
        ·
          refine ⟨41421772202647046381512339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55229029603529395175349785 41421772202647046381512339)
          ·
            refine ⟨62132658303970569572268509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41421772202647046381512339 62132658303970569572268509)
            ·
              refine ⟨23299746863988963589600691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62132658303970569572268509 23299746863988963589600691)
              ·
                refine ⟨34949620295983445384401037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23299746863988963589600691 34949620295983445384401037)
                ·
                  refine ⟨13106107610993792019150389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34949620295983445384401037 13106107610993792019150389)
                  ·
                    refine ⟨1228697588530668001795349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13106107610993792019150389 1228697588530668001795349)
                    ·
                      rfl

theorem cell22_3589320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_3589320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589320 prefixEnd_3589320 := by exact prefixLift 3589320
  have htrace : WordTrace (prefixWord ++ tailWord_3589320) baseStart_3589320 baseEnd_3589320 := by
    simpa [prefixWord, tailWord_3589320, baseEnd_3589320] using wordTrace_append hprefix tailTrace_3589320
  have hstable : (prefixWord ++ tailWord_3589320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589320).length < 2 ^ (prefixWord ++ tailWord_3589320).sum := by decide
  have hdescent : baseEnd_3589320 < baseStart_3589320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589332 : List Nat := [2, 4, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_3589332 : Nat := 118140960795 + 3589332 * 2 ^ 59
def prefixEnd_3589332 : Nat := 4983230072969 + 3 ^ 40 * 3589332 * 2
def baseEnd_3589332 : Nat := 1228701696375903970495313

theorem tailTrace_3589332 : CollatzResearch.WordTrace tailWord_3589332 prefixEnd_3589332 1228701696375903970495313 := by
  unfold tailWord_3589332
  simp only [CollatzResearch.WordTrace]
  refine ⟨65456846516235323973281125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87275795354980431964374833 65456846516235323973281125)
  ·
    refine ⟨12273158721794123244990211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65456846516235323973281125 12273158721794123244990211)
    ·
      refine ⟨18409738082691184867485317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12273158721794123244990211 18409738082691184867485317)
      ·
        refine ⟨3451825890504597162653497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18409738082691184867485317 3451825890504597162653497)
        ·
          refine ⟨2588869417878447871990123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3451825890504597162653497 2588869417878447871990123)
          ·
            refine ⟨3883304126817671807985185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2588869417878447871990123 3883304126817671807985185)
            ·
              refine ⟨2912478095113253855988889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883304126817671807985185 2912478095113253855988889)
              ·
                refine ⟨2184358571334940391991667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912478095113253855988889 2184358571334940391991667)
                ·
                  refine ⟨3276537857002410587987501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184358571334940391991667 3276537857002410587987501)
                  ·
                    refine ⟨1228701696375903970495313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276537857002410587987501 1228701696375903970495313)
                    ·
                      rfl

theorem cell22_3589332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_3589332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589332 prefixEnd_3589332 := by exact prefixLift 3589332
  have htrace : WordTrace (prefixWord ++ tailWord_3589332) baseStart_3589332 baseEnd_3589332 := by
    simpa [prefixWord, tailWord_3589332, baseEnd_3589332] using wordTrace_append hprefix tailTrace_3589332
  have hstable : (prefixWord ++ tailWord_3589332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589332).length < 2 ^ (prefixWord ++ tailWord_3589332).sum := by decide
  have hdescent : baseEnd_3589332 < baseStart_3589332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589354 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 2, 3]
def baseStart_3589354 : Nat := 118140960795 + 3589354 * 2 ^ 59
def prefixEnd_3589354 : Nat := 4983230072969 + 3 ^ 40 * 3589354 * 2
def baseEnd_3589354 : Nat := 1228709227425503246445245

theorem tailTrace_3589354 : CollatzResearch.WordTrace tailWord_3589354 prefixEnd_3589354 1228709227425503246445245 := by
  unfold tailWord_3589354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32728623859597736425965779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87276330292260630469242077 32728623859597736425965779)
  ·
    refine ⟨49092935789396604638948669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32728623859597736425965779 49092935789396604638948669)
    ·
      refine ⟨18409850921023726739605751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49092935789396604638948669 18409850921023726739605751)
      ·
        refine ⟨27614776381535590109408627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18409850921023726739605751 27614776381535590109408627)
        ·
          refine ⟨41422164572303385164112941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27614776381535590109408627 41422164572303385164112941)
          ·
            refine ⟨15533311714613769436542353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41422164572303385164112941 15533311714613769436542353)
            ·
              refine ⟨11649983785960327077406765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15533311714613769436542353 11649983785960327077406765)
              ·
                refine ⟨4368743919735122654027537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11649983785960327077406765 4368743919735122654027537)
                ·
                  refine ⟨3276557939801341990520653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4368743919735122654027537 3276557939801341990520653)
                  ·
                    refine ⟨1228709227425503246445245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276557939801341990520653 1228709227425503246445245)
                    ·
                      rfl

theorem cell22_3589354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_3589354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589354 prefixEnd_3589354 := by exact prefixLift 3589354
  have htrace : WordTrace (prefixWord ++ tailWord_3589354) baseStart_3589354 baseEnd_3589354 := by
    simpa [prefixWord, tailWord_3589354, baseEnd_3589354] using wordTrace_append hprefix tailTrace_3589354
  have hstable : (prefixWord ++ tailWord_3589354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589354).length < 2 ^ (prefixWord ++ tailWord_3589354).sum := by decide
  have hdescent : baseEnd_3589354 < baseStart_3589354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589399 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 3, 3]
def baseStart_3589399 : Nat := 118140960795 + 3589399 * 2 ^ 59
def prefixEnd_3589399 : Nat := 4983230072969 + 3 ^ 40 * 3589399 * 2
def baseEnd_3589399 : Nat := 1228724631845138129070107

theorem tailTrace_3589399 : CollatzResearch.WordTrace tailWord_3589399 prefixEnd_3589399 1228724631845138129070107 := by
  unfold tailWord_3589399
  simp only [CollatzResearch.WordTrace]
  refine ⟨130916136723227918389251251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87277424482151945592834167 130916136723227918389251251)
  ·
    refine ⟨196374205084841877583876877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130916136723227918389251251 196374205084841877583876877)
    ·
      refine ⟨73640326906815704093953829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196374205084841877583876877 73640326906815704093953829)
      ·
        refine ⟨13807561295027944517616343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73640326906815704093953829 13807561295027944517616343)
        ·
          refine ⟨20711341942541916776424515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13807561295027944517616343 20711341942541916776424515)
          ·
            refine ⟨31067012913812875164636773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20711341942541916776424515 31067012913812875164636773)
            ·
              refine ⟨5825064921339914093369395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31067012913812875164636773 5825064921339914093369395)
              ·
                refine ⟨8737597382009871140054093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5825064921339914093369395 8737597382009871140054093)
                ·
                  refine ⟨3276599018253701677520285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8737597382009871140054093 3276599018253701677520285)
                  ·
                    refine ⟨1228724631845138129070107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276599018253701677520285 1228724631845138129070107)
                    ·
                      rfl

theorem cell22_3589399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_3589399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589399 prefixEnd_3589399 := by exact prefixLift 3589399
  have htrace : WordTrace (prefixWord ++ tailWord_3589399) baseStart_3589399 baseEnd_3589399 := by
    simpa [prefixWord, tailWord_3589399, baseEnd_3589399] using wordTrace_append hprefix tailTrace_3589399
  have hstable : (prefixWord ++ tailWord_3589399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589399).length < 2 ^ (prefixWord ++ tailWord_3589399).sum := by decide
  have hdescent : baseEnd_3589399 < baseStart_3589399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589476 : List Nat := [2, 3, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_3589476 : Nat := 118140960795 + 3589476 * 2 ^ 59
def prefixEnd_3589476 : Nat := 4983230072969 + 3 ^ 40 * 3589476 * 2
def baseEnd_3589476 : Nat := 1228750990518735594894871

theorem tailTrace_3589476 : CollatzResearch.WordTrace tailWord_3589476 prefixEnd_3589476 1228750990518735594894871 := by
  unfold tailWord_3589476
  simp only [CollatzResearch.WordTrace]
  refine ⟨65459472571974480269902141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87279296762632640359869521 65459472571974480269902141)
  ·
    refine ⟨24547302214490430101213303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65459472571974480269902141 24547302214490430101213303)
    ·
      refine ⟨36820953321735645151819955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24547302214490430101213303 36820953321735645151819955)
      ·
        refine ⟨55231429982603467727729933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36820953321735645151819955 55231429982603467727729933)
        ·
          refine ⟨20711786243476300397898725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55231429982603467727729933 20711786243476300397898725)
          ·
            refine ⟨3883459920651806324606011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20711786243476300397898725 3883459920651806324606011)
            ·
              refine ⟨5825189880977709486909017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883459920651806324606011 5825189880977709486909017)
              ·
                refine ⟨4368892410733282115181763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5825189880977709486909017 4368892410733282115181763)
                ·
                  refine ⟨6553338616099923172772645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368892410733282115181763 6553338616099923172772645)
                  ·
                    refine ⟨1228750990518735594894871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553338616099923172772645 1228750990518735594894871)
                    ·
                      rfl

theorem cell22_3589476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_3589476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589476 prefixEnd_3589476 := by exact prefixLift 3589476
  have htrace : WordTrace (prefixWord ++ tailWord_3589476) baseStart_3589476 baseEnd_3589476 := by
    simpa [prefixWord, tailWord_3589476, baseEnd_3589476] using wordTrace_append hprefix tailTrace_3589476
  have hstable : (prefixWord ++ tailWord_3589476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589476).length < 2 ^ (prefixWord ++ tailWord_3589476).sum := by decide
  have hdescent : baseEnd_3589476 < baseStart_3589476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589493 : List Nat := [1, 3, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_3589493 : Nat := 118140960795 + 3589493 * 2 ^ 59
def prefixEnd_3589493 : Nat := 4983230072969 + 3 ^ 40 * 3589493 * 2
def baseEnd_3589493 : Nat := 1228756809966153217219819

theorem tailTrace_3589493 : CollatzResearch.WordTrace tailWord_3589493 prefixEnd_3589493 1228756809966153217219819 := by
  unfold tailWord_3589493
  simp only [CollatzResearch.WordTrace]
  refine ⟨130919565184887372443173133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87279710123258248295448755 130919565184887372443173133)
  ·
    refine ⟨49094836944332764666189925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130919565184887372443173133 49094836944332764666189925)
    ·
      refine ⟨9205281927062393374910611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49094836944332764666189925 9205281927062393374910611)
      ·
        refine ⟨13807922890593590062365917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9205281927062393374910611 13807922890593590062365917)
        ·
          refine ⟨5177971083972596273387219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13807922890593590062365917 5177971083972596273387219)
          ·
            refine ⟨7766956625958894410080829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177971083972596273387219 7766956625958894410080829)
            ·
              refine ⟨2912608734734585403780311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7766956625958894410080829 2912608734734585403780311)
              ·
                refine ⟨4368913102101878105670467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912608734734585403780311 4368913102101878105670467)
                ·
                  refine ⟨6553369653152817158505701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4368913102101878105670467 6553369653152817158505701)
                  ·
                    refine ⟨1228756809966153217219819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553369653152817158505701 1228756809966153217219819)
                    ·
                      rfl

theorem cell22_3589493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_3589493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589493 prefixEnd_3589493 := by exact prefixLift 3589493
  have htrace : WordTrace (prefixWord ++ tailWord_3589493) baseStart_3589493 baseEnd_3589493 := by
    simpa [prefixWord, tailWord_3589493, baseEnd_3589493] using wordTrace_append hprefix tailTrace_3589493
  have hstable : (prefixWord ++ tailWord_3589493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589493).length < 2 ^ (prefixWord ++ tailWord_3589493).sum := by decide
  have hdescent : baseEnd_3589493 < baseStart_3589493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589508 : List Nat := [2, 3, 2, 1, 1, 5, 2, 2, 4]
def baseStart_3589508 : Nat := 118140960795 + 3589508 * 2 ^ 59
def prefixEnd_3589508 : Nat := 4983230072969 + 3 ^ 40 * 3589508 * 2
def baseEnd_3589508 : Nat := 409587314924232726031591

theorem tailTrace_3589508 : CollatzResearch.WordTrace tailWord_3589508 prefixEnd_3589508 409587314924232726031591 := by
  unfold tailWord_3589508
  simp only [CollatzResearch.WordTrace]
  refine ⟨65460056139916515002484589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87280074853222020003312785 65460056139916515002484589)
  ·
    refine ⟨24547521052468693125931721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65460056139916515002484589 24547521052468693125931721)
    ·
      refine ⟨18410640789351519844448791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24547521052468693125931721 18410640789351519844448791)
      ·
        refine ⟨27615961184027279766673187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18410640789351519844448791 27615961184027279766673187)
        ·
          refine ⟨41423941776040919650009781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27615961184027279766673187 41423941776040919650009781)
          ·
            refine ⟨3883494541503836217188417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41423941776040919650009781 3883494541503836217188417)
            ·
              refine ⟨2912620906127877162891313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883494541503836217188417 2912620906127877162891313)
              ·
                refine ⟨2184465679595907872168485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912620906127877162891313 2184465679595907872168485)
                ·
                  refine ⟨409587314924232726031591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184465679595907872168485 409587314924232726031591)
                  ·
                    rfl

theorem cell22_3589508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_3589508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589508 prefixEnd_3589508 := by exact prefixLift 3589508
  have htrace : WordTrace (prefixWord ++ tailWord_3589508) baseStart_3589508 baseEnd_3589508 := by
    simpa [prefixWord, tailWord_3589508, baseEnd_3589508] using wordTrace_append hprefix tailTrace_3589508
  have hstable : (prefixWord ++ tailWord_3589508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589508).length < 2 ^ (prefixWord ++ tailWord_3589508).sum := by decide
  have hdescent : baseEnd_3589508 < baseStart_3589508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589641 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 2, 3]
def baseStart_3589641 : Nat := 118140960795 + 3589641 * 2 ^ 59
def prefixEnd_3589641 : Nat := 4983230072969 + 3 ^ 40 * 3589641 * 2
def baseEnd_3589641 : Nat := 1228807473390730164519365

theorem tailTrace_3589641 : CollatzResearch.WordTrace tailWord_3589641 prefixEnd_3589641 1228807473390730164519365 := by
  unfold tailWord_3589641
  simp only [CollatzResearch.WordTrace]
  refine ⟨130924963188351193719560777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87283308792234129146373851 130924963188351193719560777)
  ·
    refine ⟨98193722391263395289670583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130924963188351193719560777 98193722391263395289670583)
    ·
      refine ⟨147290583586895092934505875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98193722391263395289670583 147290583586895092934505875)
      ·
        refine ⟨220935875380342639401758813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147290583586895092934505875 220935875380342639401758813)
        ·
          refine ⟨82850953267628489775659555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220935875380342639401758813 82850953267628489775659555)
          ·
            refine ⟨124276429901442734663489333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82850953267628489775659555 124276429901442734663489333)
            ·
              refine ⟨11650915303260256374702125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124276429901442734663489333 11650915303260256374702125)
              ·
                refine ⟨4369093238722596140513297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11650915303260256374702125 4369093238722596140513297)
                ·
                  refine ⟨3276819929041947105384973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4369093238722596140513297 3276819929041947105384973)
                  ·
                    refine ⟨1228807473390730164519365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276819929041947105384973 1228807473390730164519365)
                    ·
                      rfl

theorem cell22_3589641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 3].length) (baseStart_3589641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589641 prefixEnd_3589641 := by exact prefixLift 3589641
  have htrace : WordTrace (prefixWord ++ tailWord_3589641) baseStart_3589641 baseEnd_3589641 := by
    simpa [prefixWord, tailWord_3589641, baseEnd_3589641] using wordTrace_append hprefix tailTrace_3589641
  have hstable : (prefixWord ++ tailWord_3589641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589641).length < 2 ^ (prefixWord ++ tailWord_3589641).sum := by decide
  have hdescent : baseEnd_3589641 < baseStart_3589641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589645 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3589645 : Nat := 118140960795 + 3589645 * 2 ^ 59
def prefixEnd_3589645 : Nat := 4983230072969 + 3 ^ 40 * 3589645 * 2
def baseEnd_3589645 : Nat := 1228808842672475487419353

theorem tailTrace_3589645 : CollatzResearch.WordTrace tailWord_3589645 prefixEnd_3589645 1228808842672475487419353 := by
  unfold tailWord_3589645
  simp only [CollatzResearch.WordTrace]
  refine ⟨130925109080336702402706389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87283406053557801601804259 130925109080336702402706389)
  ·
    refine ⟨3068557244070391462563431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 130925109080336702402706389 3068557244070391462563431)
    ·
      refine ⟨4602835866105587193845147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3068557244070391462563431 4602835866105587193845147)
      ·
        refine ⟨6904253799158380790767721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4602835866105587193845147 6904253799158380790767721)
        ·
          refine ⟨5178190349368785593075791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6904253799158380790767721 5178190349368785593075791)
          ·
            refine ⟨7767285524053178389613687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178190349368785593075791 7767285524053178389613687)
            ·
              refine ⟨11650928286079767584420531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767285524053178389613687 11650928286079767584420531)
              ·
                refine ⟨17476392429119651376630797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11650928286079767584420531 17476392429119651376630797)
                ·
                  refine ⟨6553647160919869266236549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17476392429119651376630797 6553647160919869266236549)
                  ·
                    refine ⟨1228808842672475487419353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6553647160919869266236549 1228808842672475487419353)
                    ·
                      rfl

theorem cell22_3589645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3589645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589645 prefixEnd_3589645 := by exact prefixLift 3589645
  have htrace : WordTrace (prefixWord ++ tailWord_3589645) baseStart_3589645 baseEnd_3589645 := by
    simpa [prefixWord, tailWord_3589645, baseEnd_3589645] using wordTrace_append hprefix tailTrace_3589645
  have hstable : (prefixWord ++ tailWord_3589645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589645).length < 2 ^ (prefixWord ++ tailWord_3589645).sum := by decide
  have hdescent : baseEnd_3589645 < baseStart_3589645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589703 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 3, 3]
def baseStart_3589703 : Nat := 118140960795 + 3589703 * 2 ^ 59
def prefixEnd_3589703 : Nat := 4983230072969 + 3 ^ 40 * 3589703 * 2
def baseEnd_3589703 : Nat := 1228828697257782669469175

theorem tailTrace_3589703 : CollatzResearch.WordTrace tailWord_3589703 prefixEnd_3589703 1228828697257782669469175 := by
  unfold tailWord_3589703
  simp only [CollatzResearch.WordTrace]
  refine ⟨130927224514126578308317763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87284816342751052205545175 130927224514126578308317763)
  ·
    refine ⟨196390836771189867462476645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130927224514126578308317763 196390836771189867462476645)
    ·
      refine ⟨36823281894598100149214371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196390836771189867462476645 36823281894598100149214371)
      ·
        refine ⟨55234922841897150223821557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36823281894598100149214371 55234922841897150223821557)
        ·
          refine ⟨5178274016427857833483271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55234922841897150223821557 5178274016427857833483271)
          ·
            refine ⟨7767411024641786750224907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178274016427857833483271 7767411024641786750224907)
            ·
              refine ⟨11651116536962680125337361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7767411024641786750224907 11651116536962680125337361)
              ·
                refine ⟨8738337402722010094003021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11651116536962680125337361 8738337402722010094003021)
                ·
                  refine ⟨3276876526020753785251133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8738337402722010094003021 3276876526020753785251133)
                  ·
                    refine ⟨1228828697257782669469175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276876526020753785251133 1228828697257782669469175)
                    ·
                      rfl

theorem cell22_3589703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_3589703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589703 prefixEnd_3589703 := by exact prefixLift 3589703
  have htrace : WordTrace (prefixWord ++ tailWord_3589703) baseStart_3589703 baseEnd_3589703 := by
    simpa [prefixWord, tailWord_3589703, baseEnd_3589703] using wordTrace_append hprefix tailTrace_3589703
  have hstable : (prefixWord ++ tailWord_3589703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589703).length < 2 ^ (prefixWord ++ tailWord_3589703).sum := by decide
  have hdescent : baseEnd_3589703 < baseStart_3589703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589733 : List Nat := [1, 3, 1, 3, 3, 3, 1, 2, 5]
def baseStart_3589733 : Nat := 118140960795 + 3589733 * 2 ^ 59
def prefixEnd_3589733 : Nat := 4983230072969 + 3 ^ 40 * 3589733 * 2
def baseEnd_3589733 : Nat := 409612988956957530406361

theorem tailTrace_3589733 : CollatzResearch.WordTrace tailWord_3589733 prefixEnd_3589733 409612988956957530406361 := by
  unfold tailWord_3589733
  simp only [CollatzResearch.WordTrace]
  refine ⟨130928318704017893431909853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87285545802678595621273235 130928318704017893431909853)
  ·
    refine ⟨49098119514006710036966195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130928318704017893431909853 49098119514006710036966195)
    ·
      refine ⟨73647179271010065055449293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49098119514006710036966195 73647179271010065055449293)
      ·
        refine ⟨27617692226628774395793485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73647179271010065055449293 27617692226628774395793485)
        ·
          refine ⟨10356634584985790398422557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27617692226628774395793485 10356634584985790398422557)
          ·
            refine ⟨3883737969369671399408459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10356634584985790398422557 3883737969369671399408459)
            ·
              refine ⟨5825606954054507099112689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3883737969369671399408459 5825606954054507099112689)
              ·
                refine ⟨4369205215540880324334517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5825606954054507099112689 4369205215540880324334517)
                ·
                  refine ⟨409612988956957530406361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4369205215540880324334517 409612988956957530406361)
                  ·
                    rfl

theorem cell22_3589733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_3589733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589733 prefixEnd_3589733 := by exact prefixLift 3589733
  have htrace : WordTrace (prefixWord ++ tailWord_3589733) baseStart_3589733 baseEnd_3589733 := by
    simpa [prefixWord, tailWord_3589733, baseEnd_3589733] using wordTrace_append hprefix tailTrace_3589733
  have hstable : (prefixWord ++ tailWord_3589733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589733).length < 2 ^ (prefixWord ++ tailWord_3589733).sum := by decide
  have hdescent : baseEnd_3589733 < baseStart_3589733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589750 : List Nat := [5, 1, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3589750 : Nat := 118140960795 + 3589750 * 2 ^ 59
def prefixEnd_3589750 : Nat := 4983230072969 + 3 ^ 40 * 3589750 * 2
def baseEnd_3589750 : Nat := 409614928772763404514677

theorem tailTrace_3589750 : CollatzResearch.WordTrace tailWord_3589750 prefixEnd_3589750 409614928772763404514677 := by
  unfold tailWord_3589750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8183058671559769083454919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87285959163304203556852469 8183058671559769083454919)
  ·
    refine ⟨12274588007339653625182379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8183058671559769083454919 12274588007339653625182379)
    ·
      refine ⟨18411882011009480437773569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12274588007339653625182379 18411882011009480437773569)
      ·
        refine ⟨13808911508257110328330177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18411882011009480437773569 13808911508257110328330177)
        ·
          refine ⟨10356683631192832746247633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13808911508257110328330177 10356683631192832746247633)
          ·
            refine ⟨7767512723394624559685725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10356683631192832746247633 7767512723394624559685725)
            ·
              refine ⟨2912817271272984209882147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7767512723394624559685725 2912817271272984209882147)
              ·
                refine ⟨4369225906909476314823221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912817271272984209882147 4369225906909476314823221)
                ·
                  refine ⟨409614928772763404514677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4369225906909476314823221 409614928772763404514677)
                  ·
                    rfl

theorem cell22_3589750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3589750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589750 prefixEnd_3589750 := by exact prefixLift 3589750
  have htrace : WordTrace (prefixWord ++ tailWord_3589750) baseStart_3589750 baseEnd_3589750 := by
    simpa [prefixWord, tailWord_3589750, baseEnd_3589750] using wordTrace_append hprefix tailTrace_3589750
  have hstable : (prefixWord ++ tailWord_3589750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589750).length < 2 ^ (prefixWord ++ tailWord_3589750).sum := by decide
  have hdescent : baseEnd_3589750 < baseStart_3589750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589761 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 6]
def baseStart_3589761 : Nat := 118140960795 + 3589761 * 2 ^ 59
def prefixEnd_3589761 : Nat := 4983230072969 + 3 ^ 40 * 3589761 * 2
def baseEnd_3589761 : Nat := 409616183947696617172999

theorem tailTrace_3589761 : CollatzResearch.WordTrace tailWord_3589761 prefixEnd_3589761 409616183947696617172999 := by
  unfold tailWord_3589761
  simp only [CollatzResearch.WordTrace]
  refine ⟨130929339947916454213929137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87286226631944302809286091 130929339947916454213929137)
  ·
    refine ⟨98197004960937340660446853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130929339947916454213929137 98197004960937340660446853)
    ·
      refine ⟨18411938430175751373833785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98197004960937340660446853 18411938430175751373833785)
      ·
        refine ⟨13808953822631813530375339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18411938430175751373833785 13808953822631813530375339)
        ·
          refine ⟨20713430733947720295563009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13808953822631813530375339 20713430733947720295563009)
          ·
            refine ⟨15535073050460790221672257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20713430733947720295563009 15535073050460790221672257)
            ·
              refine ⟨11651304787845592666254193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15535073050460790221672257 11651304787845592666254193)
              ·
                refine ⟨8738478590884194499690645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11651304787845592666254193 8738478590884194499690645)
                ·
                  refine ⟨409616183947696617172999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8738478590884194499690645 409616183947696617172999)
                  ·
                    rfl

theorem cell22_3589761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_3589761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589761 prefixEnd_3589761 := by exact prefixLift 3589761
  have htrace : WordTrace (prefixWord ++ tailWord_3589761) baseStart_3589761 baseEnd_3589761 := by
    simpa [prefixWord, tailWord_3589761, baseEnd_3589761] using wordTrace_append hprefix tailTrace_3589761
  have hstable : (prefixWord ++ tailWord_3589761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589761).length < 2 ^ (prefixWord ++ tailWord_3589761).sum := by decide
  have hdescent : baseEnd_3589761 < baseStart_3589761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589793 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 4, 3]
def baseStart_3589793 : Nat := 118140960795 + 3589793 * 2 ^ 59
def prefixEnd_3589793 : Nat := 4983230072969 + 3 ^ 40 * 3589793 * 2
def baseEnd_3589793 : Nat := 1228859506097052434718899

theorem tailTrace_3589793 : CollatzResearch.WordTrace tailWord_3589793 prefixEnd_3589793 1228859506097052434718899 := by
  unfold tailWord_3589793
  simp only [CollatzResearch.WordTrace]
  refine ⟨130930507083800523679094033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87287004722533682452729355 130930507083800523679094033)
  ·
    refine ⟨98197880312850392759320525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130930507083800523679094033 98197880312850392759320525)
    ·
      refine ⟨36824205117318897284745197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98197880312850392759320525 36824205117318897284745197)
      ·
        refine ⟨13809076918994586481779449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36824205117318897284745197 13809076918994586481779449)
        ·
          refine ⟨10356807689245939861334587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13809076918994586481779449 10356807689245939861334587)
          ·
            refine ⟨15535211533868909792001881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10356807689245939861334587 15535211533868909792001881)
            ·
              refine ⟨11651408650401682344001411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15535211533868909792001881 11651408650401682344001411)
              ·
                refine ⟨17477112975602523516002117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11651408650401682344001411 17477112975602523516002117)
                ·
                  refine ⟨3276958682925473159250397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17477112975602523516002117 3276958682925473159250397)
                  ·
                    refine ⟨1228859506097052434718899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276958682925473159250397 1228859506097052434718899)
                    ·
                      rfl

theorem cell22_3589793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 4, 3].length) (baseStart_3589793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589793 prefixEnd_3589793 := by exact prefixLift 3589793
  have htrace : WordTrace (prefixWord ++ tailWord_3589793) baseStart_3589793 baseEnd_3589793 := by
    simpa [prefixWord, tailWord_3589793, baseEnd_3589793] using wordTrace_append hprefix tailTrace_3589793
  have hstable : (prefixWord ++ tailWord_3589793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589793).length < 2 ^ (prefixWord ++ tailWord_3589793).sum := by decide
  have hdescent : baseEnd_3589793 < baseStart_3589793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589810 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 2, 3]
def baseStart_3589810 : Nat := 118140960795 + 3589810 * 2 ^ 59
def prefixEnd_3589810 : Nat := 4983230072969 + 3 ^ 40 * 3589810 * 2
def baseEnd_3589810 : Nat := 1228865325544470057043847

theorem tailTrace_3589810 : CollatzResearch.WordTrace tailWord_3589810 prefixEnd_3589810 1228865325544470057043847 := by
  unfold tailWord_3589810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32732781781184733895615721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87287418083159290388308589 32732781781184733895615721)
  ·
    refine ⟨24549586335888550421711791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32732781781184733895615721 24549586335888550421711791)
    ·
      refine ⟨36824379503832825632567687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24549586335888550421711791 36824379503832825632567687)
      ·
        refine ⟨55236569255749238448851531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36824379503832825632567687 55236569255749238448851531)
        ·
          refine ⟨82854853883623857673277297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55236569255749238448851531 82854853883623857673277297)
          ·
            refine ⟨62141140412717893254957973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82854853883623857673277297 62141140412717893254957973)
            ·
              refine ⟨2912865956846151246326155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62141140412717893254957973 2912865956846151246326155)
              ·
                refine ⟨4369298935269226869489233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2912865956846151246326155 4369298935269226869489233)
                ·
                  refine ⟨3276974201451920152116925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4369298935269226869489233 3276974201451920152116925)
                  ·
                    refine ⟨1228865325544470057043847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3276974201451920152116925 1228865325544470057043847)
                    ·
                      rfl

theorem cell22_3589810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_3589810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589810 prefixEnd_3589810 := by exact prefixLift 3589810
  have htrace : WordTrace (prefixWord ++ tailWord_3589810) baseStart_3589810 baseEnd_3589810 := by
    simpa [prefixWord, tailWord_3589810, baseEnd_3589810] using wordTrace_append hprefix tailTrace_3589810
  have hstable : (prefixWord ++ tailWord_3589810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589810).length < 2 ^ (prefixWord ++ tailWord_3589810).sum := by decide
  have hdescent : baseEnd_3589810 < baseStart_3589810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589846 : List Nat := [5, 2, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3589846 : Nat := 118140960795 + 3589846 * 2 ^ 59
def prefixEnd_3589846 : Nat := 4983230072969 + 3 ^ 40 * 3589846 * 2
def baseEnd_3589846 : Nat := 409625883026725987714579

theorem tailTrace_3589846 : CollatzResearch.WordTrace tailWord_3589846 prefixEnd_3589846 409625883026725987714579 := by
  unfold tailWord_3589846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8183277509538032108173337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87288293435072342487182261 8183277509538032108173337)
  ·
    refine ⟨6137458132153524081130003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8183277509538032108173337 6137458132153524081130003)
    ·
      refine ⟨9206187198230286121695005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6137458132153524081130003 9206187198230286121695005)
      ·
        refine ⟨3452320199336357295635627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9206187198230286121695005 3452320199336357295635627)
        ·
          refine ⟨5178480299004535943453441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452320199336357295635627 5178480299004535943453441)
          ·
            refine ⟨3883860224253401957590081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5178480299004535943453441 3883860224253401957590081)
            ·
              refine ⟨2912895168190051468192561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3883860224253401957590081 2912895168190051468192561)
              ·
                refine ⟨2184671376142538601144421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2912895168190051468192561 2184671376142538601144421)
                ·
                  refine ⟨409625883026725987714579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184671376142538601144421 409625883026725987714579)
                  ·
                    rfl

theorem cell22_3589846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3589846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589846 prefixEnd_3589846 := by exact prefixLift 3589846
  have htrace : WordTrace (prefixWord ++ tailWord_3589846) baseStart_3589846 baseEnd_3589846 := by
    simpa [prefixWord, tailWord_3589846, baseEnd_3589846] using wordTrace_append hprefix tailTrace_3589846
  have hstable : (prefixWord ++ tailWord_3589846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589846).length < 2 ^ (prefixWord ++ tailWord_3589846).sum := by decide
  have hdescent : baseEnd_3589846 < baseStart_3589846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589855 : List Nat := [1, 1, 2, 3, 2, 2, 3, 4, 1, 3]
def baseStart_3589855 : Nat := 118140960795 + 3589855 * 2 ^ 59
def prefixEnd_3589855 : Nat := 4983230072969 + 3 ^ 40 * 3589855 * 2
def baseEnd_3589855 : Nat := 1228880729964104939668709

theorem tailTrace_3589855 : CollatzResearch.WordTrace tailWord_3589855 prefixEnd_3589855 1228880729964104939668709 := by
  unfold tailWord_3589855
  simp only [CollatzResearch.WordTrace]
  refine ⟨130932768409575908267851019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87288512273050605511900679 130932768409575908267851019)
  ·
    refine ⟨196399152614363862401776529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130932768409575908267851019 196399152614363862401776529)
    ·
      refine ⟨147299364460772896801332397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196399152614363862401776529 147299364460772896801332397)
      ·
        refine ⟨55237261672789836300499649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147299364460772896801332397 55237261672789836300499649)
        ·
          refine ⟨41427946254592377225374737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55237261672789836300499649 41427946254592377225374737)
          ·
            refine ⟨31070959690944282919031053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41427946254592377225374737 31070959690944282919031053)
            ·
              refine ⟨11651609884104106094636645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31070959690944282919031053 11651609884104106094636645)
              ·
                refine ⟨2184676853269519892744371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11651609884104106094636645 2184676853269519892744371)
                ·
                  refine ⟨3277015279904279839116557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184676853269519892744371 3277015279904279839116557)
                  ·
                    refine ⟨1228880729964104939668709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277015279904279839116557 1228880729964104939668709)
                    ·
                      rfl

theorem cell22_3589855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 3].length) (baseStart_3589855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589855 prefixEnd_3589855 := by exact prefixLift 3589855
  have htrace : WordTrace (prefixWord ++ tailWord_3589855) baseStart_3589855 baseEnd_3589855 := by
    simpa [prefixWord, tailWord_3589855, baseEnd_3589855] using wordTrace_append hprefix tailTrace_3589855
  have hstable : (prefixWord ++ tailWord_3589855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589855).length < 2 ^ (prefixWord ++ tailWord_3589855).sum := by decide
  have hdescent : baseEnd_3589855 < baseStart_3589855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589866 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3589866 : Nat := 118140960795 + 3589866 * 2 ^ 59
def prefixEnd_3589866 : Nat := 4983230072969 + 3 ^ 40 * 3589866 * 2
def baseEnd_3589866 : Nat := 1228884495488904577643675

theorem tailTrace_3589866 : CollatzResearch.WordTrace tailWord_3589866 prefixEnd_3589866 1228884495488904577643675 := by
  unfold tailWord_3589866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32733292403134014286625363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87288779741690704764334301 32733292403134014286625363)
  ·
    refine ⟨49099938604701021429938045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32733292403134014286625363 49099938604701021429938045)
    ·
      refine ⟨18412476976762883036226767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49099938604701021429938045 18412476976762883036226767)
      ·
        refine ⟨27618715465144324554340151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18412476976762883036226767 27618715465144324554340151)
        ·
          refine ⟨41428073197716486831510227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27618715465144324554340151 41428073197716486831510227)
          ·
            refine ⟨62142109796574730247265341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41428073197716486831510227 62142109796574730247265341)
            ·
              refine ⟨23303291173715523842724503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62142109796574730247265341 23303291173715523842724503)
              ·
                refine ⟨34954936760573285764086755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23303291173715523842724503 34954936760573285764086755)
                ·
                  refine ⟨52432405140859928646130133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34954936760573285764086755 52432405140859928646130133)
                  ·
                    refine ⟨1228884495488904577643675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52432405140859928646130133 1228884495488904577643675)
                    ·
                      rfl

theorem cell22_3589866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3589866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589866 prefixEnd_3589866 := by exact prefixLift 3589866
  have htrace : WordTrace (prefixWord ++ tailWord_3589866) baseStart_3589866 baseEnd_3589866 := by
    simpa [prefixWord, tailWord_3589866, baseEnd_3589866] using wordTrace_append hprefix tailTrace_3589866
  have hstable : (prefixWord ++ tailWord_3589866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589866).length < 2 ^ (prefixWord ++ tailWord_3589866).sum := by decide
  have hdescent : baseEnd_3589866 < baseStart_3589866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3589896 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 8]
def baseStart_3589896 : Nat := 118140960795 + 3589896 * 2 ^ 59
def prefixEnd_3589896 : Nat := 4983230072969 + 3 ^ 40 * 3589896 * 2
def baseEnd_3589896 : Nat := 409631588367331499797861

theorem tailTrace_3589896 : CollatzResearch.WordTrace tailWord_3589896 prefixEnd_3589896 409631588367331499797861 := by
  unfold tailWord_3589896
  simp only [CollatzResearch.WordTrace]
  refine ⟨65467131901213686135046771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87289509201618248180062361 65467131901213686135046771)
  ·
    refine ⟨98200697851820529202570157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65467131901213686135046771 98200697851820529202570157)
    ·
      refine ⟨36825261694432698450963809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98200697851820529202570157 36825261694432698450963809)
      ·
        refine ⟨27618946270824523838222857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36825261694432698450963809 27618946270824523838222857)
        ·
          refine ⟨20714209703118392878667143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27618946270824523838222857 20714209703118392878667143)
          ·
            refine ⟨31071314554677589318000715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20714209703118392878667143 31071314554677589318000715)
            ·
              refine ⟨46606971832016383977001073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31071314554677589318000715 46606971832016383977001073)
              ·
                refine ⟨34955228874012287982750805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46606971832016383977001073 34955228874012287982750805)
                ·
                  refine ⟨409631588367331499797861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34955228874012287982750805 409631588367331499797861)
                  ·
                    rfl

theorem cell22_3589896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 8].length) (baseStart_3589896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3589896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3589896 prefixEnd_3589896 := by exact prefixLift 3589896
  have htrace : WordTrace (prefixWord ++ tailWord_3589896) baseStart_3589896 baseEnd_3589896 := by
    simpa [prefixWord, tailWord_3589896, baseEnd_3589896] using wordTrace_append hprefix tailTrace_3589896
  have hstable : (prefixWord ++ tailWord_3589896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3589896).length < 2 ^ (prefixWord ++ tailWord_3589896).sum := by decide
  have hdescent : baseEnd_3589896 < baseStart_3589896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3589896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590024 : List Nat := [2, 1, 3, 3, 3, 1, 1, 4, 1, 3]
def baseStart_3590024 : Nat := 118140960795 + 3590024 * 2 ^ 59
def prefixEnd_3590024 : Nat := 4983230072969 + 3 ^ 40 * 3590024 * 2
def baseEnd_3590024 : Nat := 1228938582117844832193191

theorem tailTrace_3590024 : CollatzResearch.WordTrace tailWord_3590024 prefixEnd_3590024 1228938582117844832193191 := by
  unfold tailWord_3590024
  simp only [CollatzResearch.WordTrace]
  refine ⟨65469466172981825065376563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87292621563975766753835417 65469466172981825065376563)
  ·
    refine ⟨98204199259472737598064845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65469466172981825065376563 98204199259472737598064845)
    ·
      refine ⟨36826574722302276599274317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98204199259472737598064845 36826574722302276599274317)
      ·
        refine ⟨13809965520863353724727869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36826574722302276599274317 13809965520863353724727869)
        ·
          refine ⟨5178737070323757646772951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13809965520863353724727869 5178737070323757646772951)
          ·
            refine ⟨7768105605485636470159427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5178737070323757646772951 7768105605485636470159427)
            ·
              refine ⟨11652158408228454705239141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7768105605485636470159427 11652158408228454705239141)
              ·
                refine ⟨2184779701542835257232339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11652158408228454705239141 2184779701542835257232339)
                ·
                  refine ⟨3277169552314252885848509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2184779701542835257232339 3277169552314252885848509)
                  ·
                    refine ⟨1228938582117844832193191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277169552314252885848509 1228938582117844832193191)
                    ·
                      rfl

theorem cell22_3590024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_3590024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590024 prefixEnd_3590024 := by exact prefixLift 3590024
  have htrace : WordTrace (prefixWord ++ tailWord_3590024) baseStart_3590024 baseEnd_3590024 := by
    simpa [prefixWord, tailWord_3590024, baseEnd_3590024] using wordTrace_append hprefix tailTrace_3590024
  have hstable : (prefixWord ++ tailWord_3590024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590024).length < 2 ^ (prefixWord ++ tailWord_3590024).sum := by decide
  have hdescent : baseEnd_3590024 < baseStart_3590024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590033 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_3590033 : Nat := 118140960795 + 3590033 * 2 ^ 59
def prefixEnd_3590033 : Nat := 4983230072969 + 3 ^ 40 * 3590033 * 2
def baseEnd_3590033 : Nat := 1228941663001771808718163

theorem tailTrace_3590033 : CollatzResearch.WordTrace tailWord_3590033 prefixEnd_3590033 1228941663001771808718163 := by
  unfold tailWord_3590033
  simp only [CollatzResearch.WordTrace]
  refine ⟨130939260602931044667830753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87292840401954029778553835 130939260602931044667830753)
  ·
    refine ⟨98204445452198283500873065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130939260602931044667830753 98204445452198283500873065)
    ·
      refine ⟨73653334089148712625654799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98204445452198283500873065 73653334089148712625654799)
      ·
        refine ⟨110480001133723068938482199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73653334089148712625654799 110480001133723068938482199)
        ·
          refine ⟨165720001700584603407723299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110480001133723068938482199 165720001700584603407723299)
          ·
            refine ⟨248580002550876905111584949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165720001700584603407723299 248580002550876905111584949)
            ·
              refine ⟨23304375239144709854211089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248580002550876905111584949 23304375239144709854211089)
              ·
                refine ⟨17478281429358532390658317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23304375239144709854211089 17478281429358532390658317)
                ·
                  refine ⟨6554355536009449646496869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17478281429358532390658317 6554355536009449646496869)
                  ·
                    refine ⟨1228941663001771808718163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6554355536009449646496869 1228941663001771808718163)
                    ·
                      rfl

theorem cell22_3590033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_3590033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590033 prefixEnd_3590033 := by exact prefixLift 3590033
  have htrace : WordTrace (prefixWord ++ tailWord_3590033) baseStart_3590033 baseEnd_3590033 := by
    simpa [prefixWord, tailWord_3590033, baseEnd_3590033] using wordTrace_append hprefix tailTrace_3590033
  have hstable : (prefixWord ++ tailWord_3590033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590033).length < 2 ^ (prefixWord ++ tailWord_3590033).sum := by decide
  have hdescent : baseEnd_3590033 < baseStart_3590033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590063 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 1, 5]
def baseStart_3590063 : Nat := 118140960795 + 3590063 * 2 ^ 59
def prefixEnd_3590063 : Nat := 4983230072969 + 3 ^ 40 * 3590063 * 2
def baseEnd_3590063 : Nat := 1228951932614861730468071

theorem tailTrace_3590063 : CollatzResearch.WordTrace tailWord_3590063 prefixEnd_3590063 1228951932614861730468071 := by
  unfold tailWord_3590063
  simp only [CollatzResearch.WordTrace]
  refine ⟨130940354792822359791422843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87293569861881573194281895 130940354792822359791422843)
  ·
    refine ⟨196410532189233539687134265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130940354792822359791422843 196410532189233539687134265)
    ·
      refine ⟨147307899141925154765350699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196410532189233539687134265 147307899141925154765350699)
      ·
        refine ⟨220961848712887732148026049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147307899141925154765350699 220961848712887732148026049)
        ·
          refine ⟨165721386534665799111019537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220961848712887732148026049 165721386534665799111019537)
          ·
            refine ⟨124291039900999349333264653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165721386534665799111019537 124291039900999349333264653)
            ·
              refine ⟨46609139962874755999974245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124291039900999349333264653 46609139962874755999974245)
              ·
                refine ⟨8739213743039016749995171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46609139962874755999974245 8739213743039016749995171)
                ·
                  refine ⟨13108820614558525124992757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8739213743039016749995171 13108820614558525124992757)
                  ·
                    refine ⟨1228951932614861730468071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13108820614558525124992757 1228951932614861730468071)
                    ·
                      rfl

theorem cell22_3590063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 5].length) (baseStart_3590063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590063 prefixEnd_3590063 := by exact prefixLift 3590063
  have htrace : WordTrace (prefixWord ++ tailWord_3590063) baseStart_3590063 baseEnd_3590063 := by
    simpa [prefixWord, tailWord_3590063, baseEnd_3590063] using wordTrace_append hprefix tailTrace_3590063
  have hstable : (prefixWord ++ tailWord_3590063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590063).length < 2 ^ (prefixWord ++ tailWord_3590063).sum := by decide
  have hdescent : baseEnd_3590063 < baseStart_3590063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590080 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 4, 3]
def baseStart_3590080 : Nat := 118140960795 + 3590080 * 2 ^ 59
def prefixEnd_3590080 : Nat := 4983230072969 + 3 ^ 40 * 3590080 * 2
def baseEnd_3590080 : Nat := 1228957752062279352793019

theorem tailTrace_3590080 : CollatzResearch.WordTrace tailWord_3590080 prefixEnd_3590080 1228957752062279352793019 := by
  unfold tailWord_3590080
  simp only [CollatzResearch.WordTrace]
  refine ⟨65470487416880385847395847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87293983222507181129861129 65470487416880385847395847)
  ·
    refine ⟨98205731125320578771093771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65470487416880385847395847 98205731125320578771093771)
    ·
      refine ⟨147308596687980868156640657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98205731125320578771093771 147308596687980868156640657)
      ·
        refine ⟨110481447515985651117480493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147308596687980868156640657 110481447515985651117480493)
        ·
          refine ⟨41430542818494619169055185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110481447515985651117480493 41430542818494619169055185)
          ·
            refine ⟨31072907113870964376791389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41430542818494619169055185 31072907113870964376791389)
            ·
              refine ⟨11652340167701611641296771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31072907113870964376791389 11652340167701611641296771)
              ·
                refine ⟨17478510251552417461945157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11652340167701611641296771 17478510251552417461945157)
                ·
                  refine ⟨3277220672166078274114717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17478510251552417461945157 3277220672166078274114717)
                  ·
                    refine ⟨1228957752062279352793019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277220672166078274114717 1228957752062279352793019)
                    ·
                      rfl

theorem cell22_3590080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_3590080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590080 prefixEnd_3590080 := by exact prefixLift 3590080
  have htrace : WordTrace (prefixWord ++ tailWord_3590080) baseStart_3590080 baseEnd_3590080 := by
    simpa [prefixWord, tailWord_3590080, baseEnd_3590080] using wordTrace_append hprefix tailTrace_3590080
  have hstable : (prefixWord ++ tailWord_3590080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590080).length < 2 ^ (prefixWord ++ tailWord_3590080).sum := by decide
  have hdescent : baseEnd_3590080 < baseStart_3590080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590148 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_3590148 : Nat := 118140960795 + 3590148 * 2 ^ 59
def prefixEnd_3590148 : Nat := 4983230072969 + 3 ^ 40 * 3590148 * 2
def baseEnd_3590148 : Nat := 1228981029851949842092811

theorem tailTrace_3590148 : CollatzResearch.WordTrace tailWord_3590148 prefixEnd_3590148 1228981029851949842092811 := by
  unfold tailWord_3590148
  simp only [CollatzResearch.WordTrace]
  refine ⟨65471727498757209654133549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87295636665009612872178065 65471727498757209654133549)
  ·
    refine ⟨24551897812033953620300081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65471727498757209654133549 24551897812033953620300081)
    ·
      refine ⟨18413923359025465215225061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24551897812033953620300081 18413923359025465215225061)
      ·
        refine ⟨3452610629817274727854699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18413923359025465215225061 3452610629817274727854699)
        ·
          refine ⟨5178915944725912091782049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3452610629817274727854699 5178915944725912091782049)
          ·
            refine ⟨3884186958544434068836537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5178915944725912091782049 3884186958544434068836537)
            ·
              refine ⟨2913140218908325551627403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3884186958544434068836537 2913140218908325551627403)
              ·
                refine ⟨4369710328362488327441105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913140218908325551627403 4369710328362488327441105)
                ·
                  refine ⟨3277282746271866245580829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4369710328362488327441105 3277282746271866245580829)
                  ·
                    refine ⟨1228981029851949842092811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277282746271866245580829 1228981029851949842092811)
                    ·
                      rfl

theorem cell22_3590148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_3590148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590148 prefixEnd_3590148 := by exact prefixLift 3590148
  have htrace : WordTrace (prefixWord ++ tailWord_3590148) baseStart_3590148 baseEnd_3590148 := by
    simpa [prefixWord, tailWord_3590148, baseEnd_3590148] using wordTrace_append hprefix tailTrace_3590148
  have hstable : (prefixWord ++ tailWord_3590148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590148).length < 2 ^ (prefixWord ++ tailWord_3590148).sum := by decide
  have hdescent : baseEnd_3590148 < baseStart_3590148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590155 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 5]
def baseStart_3590155 : Nat := 118140960795 + 3590155 * 2 ^ 59
def prefixEnd_3590155 : Nat := 4983230072969 + 3 ^ 40 * 3590155 * 2
def baseEnd_3590155 : Nat := 409661142031668052389263

theorem tailTrace_3590155 : CollatzResearch.WordTrace tailWord_3590155 prefixEnd_3590155 409661142031668052389263 := by
  unfold tailWord_3590155
  simp only [CollatzResearch.WordTrace]
  refine ⟨130943710308489059503771919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87295806872326039669181279 130943710308489059503771919)
  ·
    refine ⟨196415565462733589255657879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130943710308489059503771919 196415565462733589255657879)
    ·
      refine ⟨294623348194100383883486819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196415565462733589255657879 294623348194100383883486819)
      ·
        refine ⟨441935022291150575825230229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294623348194100383883486819 441935022291150575825230229)
        ·
          refine ⟨20715704169897683241807667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 441935022291150575825230229 20715704169897683241807667)
          ·
            refine ⟨31073556254846524862711501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20715704169897683241807667 31073556254846524862711501)
            ·
              refine ⟨11652583595567446823516813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31073556254846524862711501 11652583595567446823516813)
              ·
                refine ⟨4369718848337792558818805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11652583595567446823516813 4369718848337792558818805)
                ·
                  refine ⟨409661142031668052389263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4369718848337792558818805 409661142031668052389263)
                  ·
                    rfl

theorem cell22_3590155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 5].length) (baseStart_3590155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590155 prefixEnd_3590155 := by exact prefixLift 3590155
  have htrace : WordTrace (prefixWord ++ tailWord_3590155) baseStart_3590155 baseEnd_3590155 := by
    simpa [prefixWord, tailWord_3590155, baseEnd_3590155] using wordTrace_append hprefix tailTrace_3590155
  have hstable : (prefixWord ++ tailWord_3590155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590155).length < 2 ^ (prefixWord ++ tailWord_3590155).sum := by decide
  have hdescent : baseEnd_3590155 < baseStart_3590155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590236 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3590236 : Nat := 118140960795 + 3590236 * 2 ^ 59
def prefixEnd_3590236 : Nat := 4983230072969 + 3 ^ 40 * 3590236 * 2
def baseEnd_3590236 : Nat := 1229011154050346945892541

theorem tailTrace_3590236 : CollatzResearch.WordTrace tailWord_3590236 prefixEnd_3590236 1229011154050346945892541 := by
  unfold tailWord_3590236
  simp only [CollatzResearch.WordTrace]
  refine ⟨65473332310597805168735281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87297776414130406891647041 65473332310597805168735281)
  ·
    refine ⟨49104999232948353876551461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65473332310597805168735281 49104999232948353876551461)
    ·
      refine ⟨9207187356177816351853399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49104999232948353876551461 9207187356177816351853399)
      ·
        refine ⟨13810781034266724527780099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9207187356177816351853399 13810781034266724527780099)
        ·
          refine ⟨20716171551400086791670149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13810781034266724527780099 20716171551400086791670149)
          ·
            refine ⟨3884282165887516273438153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20716171551400086791670149 3884282165887516273438153)
            ·
              refine ⟨2913211624415637205078615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3884282165887516273438153 2913211624415637205078615)
              ·
                refine ⟨4369817436623455807617923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913211624415637205078615 4369817436623455807617923)
                ·
                  refine ⟨6554726154935183711426885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4369817436623455807617923 6554726154935183711426885)
                  ·
                    refine ⟨1229011154050346945892541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6554726154935183711426885 1229011154050346945892541)
                    ·
                      rfl

theorem cell22_3590236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3590236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590236 prefixEnd_3590236 := by exact prefixLift 3590236
  have htrace : WordTrace (prefixWord ++ tailWord_3590236) baseStart_3590236 baseEnd_3590236 := by
    simpa [prefixWord, tailWord_3590236, baseEnd_3590236] using wordTrace_append hprefix tailTrace_3590236
  have hstable : (prefixWord ++ tailWord_3590236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590236).length < 2 ^ (prefixWord ++ tailWord_3590236).sum := by decide
  have hdescent : baseEnd_3590236 < baseStart_3590236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590245 : List Nat := [1, 3, 1, 3, 2, 3, 9]
def baseStart_3590245 : Nat := 118140960795 + 3590245 * 2 ^ 59
def prefixEnd_3590245 : Nat := 4983230072969 + 3 ^ 40 * 3590245 * 2
def baseEnd_3590245 : Nat := 45519045738306441571019

theorem tailTrace_3590245 : CollatzResearch.WordTrace tailWord_3590245 prefixEnd_3590245 45519045738306441571019 := by
  unfold tailWord_3590245
  simp only [CollatzResearch.WordTrace]
  refine ⟨130946992878163004874548189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87297995252108669916365459 130946992878163004874548189)
  ·
    refine ⟨49105122329311126827955571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130946992878163004874548189 49105122329311126827955571)
    ·
      refine ⟨73657683493966690241933357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49105122329311126827955571 73657683493966690241933357)
      ·
        refine ⟨27621631310237508840725009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73657683493966690241933357 27621631310237508840725009)
        ·
          refine ⟨20716223482678131630543757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27621631310237508840725009 20716223482678131630543757)
          ·
            refine ⟨7768583806004299361453909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20716223482678131630543757 7768583806004299361453909)
            ·
              refine ⟨45519045738306441571019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7768583806004299361453909 45519045738306441571019)
              ·
                rfl

theorem cell22_3590245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 9].length) (baseStart_3590245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590245 prefixEnd_3590245 := by exact prefixLift 3590245
  have htrace : WordTrace (prefixWord ++ tailWord_3590245) baseStart_3590245 baseEnd_3590245 := by
    simpa [prefixWord, tailWord_3590245, baseEnd_3590245] using wordTrace_append hprefix tailTrace_3590245
  have hstable : (prefixWord ++ tailWord_3590245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590245).length < 2 ^ (prefixWord ++ tailWord_3590245).sum := by decide
  have hdescent : baseEnd_3590245 < baseStart_3590245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590335 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 8]
def baseStart_3590335 : Nat := 118140960795 + 3590335 * 2 ^ 59
def prefixEnd_3590335 : Nat := 4983230072969 + 3 ^ 40 * 3590335 * 2
def baseEnd_3590335 : Nat := 409681681257847895889079

theorem tailTrace_3590335 : CollatzResearch.WordTrace tailWord_3590335 prefixEnd_3590335 409681681257847895889079 := by
  unfold tailWord_3590335
  simp only [CollatzResearch.WordTrace]
  refine ⟨130950275447836950245324459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87300183631891300163549639 130950275447836950245324459)
  ·
    refine ⟨196425413171755425367986689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130950275447836950245324459 196425413171755425367986689)
    ·
      refine ⟨147319059878816569025990017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196425413171755425367986689 147319059878816569025990017)
      ·
        refine ⟨110489294909112426769492513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147319059878816569025990017 110489294909112426769492513)
        ·
          refine ⟨82866971181834320077119385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110489294909112426769492513 82866971181834320077119385)
          ·
            refine ⟨62150228386375740057839539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82866971181834320077119385 62150228386375740057839539)
            ·
              refine ⟨93225342579563610086759309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62150228386375740057839539 93225342579563610086759309)
              ·
                refine ⟨34959503467336353782534741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93225342579563610086759309 34959503467336353782534741)
                ·
                  refine ⟨409681681257847895889079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34959503467336353782534741 409681681257847895889079)
                  ·
                    rfl

theorem cell22_3590335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 8].length) (baseStart_3590335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590335 prefixEnd_3590335 := by exact prefixLift 3590335
  have htrace : WordTrace (prefixWord ++ tailWord_3590335) baseStart_3590335 baseEnd_3590335 := by
    simpa [prefixWord, tailWord_3590335, baseEnd_3590335] using wordTrace_append hprefix tailTrace_3590335
  have hstable : (prefixWord ++ tailWord_3590335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590335).length < 2 ^ (prefixWord ++ tailWord_3590335).sum := by decide
  have hdescent : baseEnd_3590335 < baseStart_3590335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590369 : List Nat := [1, 2, 3, 1, 3, 1, 3, 4, 4]
def baseStart_3590369 : Nat := 118140960795 + 3590369 * 2 ^ 59
def prefixEnd_3590369 : Nat := 4983230072969 + 3 ^ 40 * 3590369 * 2
def baseEnd_3590369 : Nat := 409685560889459644105711

theorem tailTrace_3590369 : CollatzResearch.WordTrace tailWord_3590369 prefixEnd_3590369 409685560889459644105711 := by
  unfold tailWord_3590369
  simp only [CollatzResearch.WordTrace]
  refine ⟨130951515529713774052062161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87301010353142516034708107 130951515529713774052062161)
  ·
    refine ⟨98213636647285330539046621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130951515529713774052062161 98213636647285330539046621)
    ·
      refine ⟨36830113742731998952142483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98213636647285330539046621 36830113742731998952142483)
      ·
        refine ⟨55245170614097998428213725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36830113742731998952142483 55245170614097998428213725)
        ·
          refine ⟨20716938980286749410580147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55245170614097998428213725 20716938980286749410580147)
          ·
            refine ⟨31075408470430124115870221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20716938980286749410580147 31075408470430124115870221)
            ·
              refine ⟨11653278176411296543451333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31075408470430124115870221 11653278176411296543451333)
              ·
                refine ⟨2184989658077118101897125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11653278176411296543451333 2184989658077118101897125)
                ·
                  refine ⟨409685560889459644105711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2184989658077118101897125 409685560889459644105711)
                  ·
                    rfl

theorem cell22_3590369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 4].length) (baseStart_3590369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590369 prefixEnd_3590369 := by exact prefixLift 3590369
  have htrace : WordTrace (prefixWord ++ tailWord_3590369) baseStart_3590369 baseEnd_3590369 := by
    simpa [prefixWord, tailWord_3590369, baseEnd_3590369] using wordTrace_append hprefix tailTrace_3590369
  have hstable : (prefixWord ++ tailWord_3590369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590369).length < 2 ^ (prefixWord ++ tailWord_3590369).sum := by decide
  have hdescent : baseEnd_3590369 < baseStart_3590369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590382 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3590382 : Nat := 118140960795 + 3590382 * 2 ^ 59
def prefixEnd_3590382 : Nat := 4983230072969 + 3 ^ 40 * 3590382 * 2
def baseEnd_3590382 : Nat := 1229061132834051231742093

theorem tailTrace_3590382 : CollatzResearch.WordTrace tailWord_3590382 prefixEnd_3590382 1229061132834051231742093 := by
  unfold tailWord_3590382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16368998709833334659035675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87301326452444451514856933 16368998709833334659035675)
  ·
    refine ⟨24553498064750001988553513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16368998709833334659035675 24553498064750001988553513)
    ·
      refine ⟨18415123548562501491415135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24553498064750001988553513 18415123548562501491415135)
      ·
        refine ⟨27622685322843752237122703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18415123548562501491415135 27622685322843752237122703)
        ·
          refine ⟨41434027984265628355684055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27622685322843752237122703 41434027984265628355684055)
          ·
            refine ⟨62151041976398442533526083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41434027984265628355684055 62151041976398442533526083)
            ·
              refine ⟨93226562964597663800289125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62151041976398442533526083 93226562964597663800289125)
              ·
                refine ⟨17479980555862061962554211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93226562964597663800289125 17479980555862061962554211)
                ·
                  refine ⟨26219970833793092943831317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17479980555862061962554211 26219970833793092943831317)
                  ·
                    refine ⟨1229061132834051231742093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26219970833793092943831317 1229061132834051231742093)
                    ·
                      rfl

theorem cell22_3590382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3590382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590382 prefixEnd_3590382 := by exact prefixLift 3590382
  have htrace : WordTrace (prefixWord ++ tailWord_3590382) baseStart_3590382 baseEnd_3590382 := by
    simpa [prefixWord, tailWord_3590382, baseEnd_3590382] using wordTrace_append hprefix tailTrace_3590382
  have hstable : (prefixWord ++ tailWord_3590382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590382).length < 2 ^ (prefixWord ++ tailWord_3590382).sum := by decide
  have hdescent : baseEnd_3590382 < baseStart_3590382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590506 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3590506 : Nat := 118140960795 + 3590506 * 2 ^ 59
def prefixEnd_3590506 : Nat := 4983230072969 + 3 ^ 40 * 3590506 * 2
def baseEnd_3590506 : Nat := 1229103580568156241641713

theorem tailTrace_3590506 : CollatzResearch.WordTrace tailWord_3590506 prefixEnd_3590506 1229103580568156241641713 := by
  unfold tailWord_3590506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32739128082554361612449843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87304341553478297633199581 32739128082554361612449843)
  ·
    refine ⟨49108692123831542418674765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32739128082554361612449843 49108692123831542418674765)
    ·
      refine ⟨18415759546436828407003037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49108692123831542418674765 18415759546436828407003037)
      ·
        refine ⟨6905909829913810652626139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18415759546436828407003037 6905909829913810652626139)
        ·
          refine ⟨10358864744870715978939209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6905909829913810652626139 10358864744870715978939209)
          ·
            refine ⟨7769148558653036984204407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10358864744870715978939209 7769148558653036984204407)
            ·
              refine ⟨11653722837979555476306611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769148558653036984204407 11653722837979555476306611)
              ·
                refine ⟨17480584256969333214459917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11653722837979555476306611 17480584256969333214459917)
                ·
                  refine ⟨6555219096363499955422469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17480584256969333214459917 6555219096363499955422469)
                  ·
                    refine ⟨1229103580568156241641713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6555219096363499955422469 1229103580568156241641713)
                    ·
                      rfl

theorem cell22_3590506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3590506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590506 prefixEnd_3590506 := by exact prefixLift 3590506
  have htrace : WordTrace (prefixWord ++ tailWord_3590506) baseStart_3590506 baseEnd_3590506 := by
    simpa [prefixWord, tailWord_3590506, baseEnd_3590506] using wordTrace_append hprefix tailTrace_3590506
  have hstable : (prefixWord ++ tailWord_3590506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590506).length < 2 ^ (prefixWord ++ tailWord_3590506).sum := by decide
  have hdescent : baseEnd_3590506 < baseStart_3590506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590519 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 4, 3]
def baseStart_3590519 : Nat := 118140960795 + 3590519 * 2 ^ 59
def prefixEnd_3590519 : Nat := 4983230072969 + 3 ^ 40 * 3590519 * 2
def baseEnd_3590519 : Nat := 1229108030733828541066673

theorem tailTrace_3590519 : CollatzResearch.WordTrace tailWord_3590519 prefixEnd_3590519 1229108030733828541066673 := by
  unfold tailWord_3590519
  simp only [CollatzResearch.WordTrace]
  refine ⟨130956986479170349670022611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87304657652780233113348407 130956986479170349670022611)
  ·
    refine ⟨196435479718755524505033917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130956986479170349670022611 196435479718755524505033917)
    ·
      refine ⟨73663304894533321689387719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196435479718755524505033917 73663304894533321689387719)
      ·
        refine ⟨110494957341799982534081579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73663304894533321689387719 110494957341799982534081579)
        ·
          refine ⟨165742436012699973801122369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110494957341799982534081579 165742436012699973801122369)
          ·
            refine ⟨124306827009524980350841777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165742436012699973801122369 124306827009524980350841777)
            ·
              refine ⟨93230120257143735263131333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124306827009524980350841777 93230120257143735263131333)
              ·
                refine ⟨17480647548214450361837125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93230120257143735263131333 17480647548214450361837125)
                ·
                  refine ⟨3277621415290209442844461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17480647548214450361837125 3277621415290209442844461)
                  ·
                    refine ⟨1229108030733828541066673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277621415290209442844461 1229108030733828541066673)
                    ·
                      rfl

theorem cell22_3590519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 3].length) (baseStart_3590519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590519 prefixEnd_3590519 := by exact prefixLift 3590519
  have htrace : WordTrace (prefixWord ++ tailWord_3590519) baseStart_3590519 baseEnd_3590519 := by
    simpa [prefixWord, tailWord_3590519, baseEnd_3590519] using wordTrace_append hprefix tailTrace_3590519
  have hstable : (prefixWord ++ tailWord_3590519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590519).length < 2 ^ (prefixWord ++ tailWord_3590519).sum := by decide
  have hdescent : baseEnd_3590519 < baseStart_3590519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590568 : List Nat := [2, 1, 6, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3590568 : Nat := 118140960795 + 3590568 * 2 ^ 59
def prefixEnd_3590568 : Nat := 4983230072969 + 3 ^ 40 * 3590568 * 2
def baseEnd_3590568 : Nat := 1229124804435208746591523

theorem tailTrace_3590568 : CollatzResearch.WordTrace tailWord_3590568 prefixEnd_3590568 1229124804435208746591523 := by
  unfold tailWord_3590568
  simp only [CollatzResearch.WordTrace]
  refine ⟨65479386827996415519278179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87305849103995220692370905 65479386827996415519278179)
  ·
    refine ⟨98219080241994623278917269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65479386827996415519278179 98219080241994623278917269)
    ·
      refine ⟨4604019386343497966199247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98219080241994623278917269 4604019386343497966199247)
      ·
        refine ⟨6906029079515246949298871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604019386343497966199247 6906029079515246949298871)
        ·
          refine ⟨10359043619272870423948307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906029079515246949298871 10359043619272870423948307)
          ·
            refine ⟨15538565428909305635922461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359043619272870423948307 15538565428909305635922461)
            ·
              refine ⟨5826962035840989613470923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15538565428909305635922461 5826962035840989613470923)
              ·
                refine ⟨8740443053761484420206385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5826962035840989613470923 8740443053761484420206385)
                ·
                  refine ⟨6555332290321113315154789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8740443053761484420206385 6555332290321113315154789)
                  ·
                    refine ⟨1229124804435208746591523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6555332290321113315154789 1229124804435208746591523)
                    ·
                      rfl

theorem cell22_3590568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3590568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590568 prefixEnd_3590568 := by exact prefixLift 3590568
  have htrace : WordTrace (prefixWord ++ tailWord_3590568) baseStart_3590568 baseEnd_3590568 := by
    simpa [prefixWord, tailWord_3590568, baseEnd_3590568] using wordTrace_append hprefix tailTrace_3590568
  have hstable : (prefixWord ++ tailWord_3590568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590568).length < 2 ^ (prefixWord ++ tailWord_3590568).sum := by decide
  have hdescent : baseEnd_3590568 < baseStart_3590568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590641 : List Nat := [1, 2, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_3590641 : Nat := 118140960795 + 3590641 * 2 ^ 59
def prefixEnd_3590641 : Nat := 4983230072969 + 3 ^ 40 * 3590641 * 2
def baseEnd_3590641 : Nat := 1229149793827060889516299

theorem tailTrace_3590641 : CollatzResearch.WordTrace tailWord_3590641 prefixEnd_3590641 1229149793827060889516299 := by
  unfold tailWord_3590641
  simp only [CollatzResearch.WordTrace]
  refine ⟨130961436184728364505963777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87307624123152243003975851 130961436184728364505963777)
  ·
    refine ⟨98221077138546273379472833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130961436184728364505963777 98221077138546273379472833)
    ·
      refine ⟨73665807853909705034604625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98221077138546273379472833 73665807853909705034604625)
      ·
        refine ⟨55249355890432278775953469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73665807853909705034604625 55249355890432278775953469)
        ·
          refine ⟨20718508458912104540982551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55249355890432278775953469 20718508458912104540982551)
          ·
            refine ⟨31077762688368156811473827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20718508458912104540982551 31077762688368156811473827)
            ·
              refine ⟨46616644032552235217210741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31077762688368156811473827 46616644032552235217210741)
              ·
                refine ⟨4370310378051772051613507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46616644032552235217210741 4370310378051772051613507)
                ·
                  refine ⟨6555465567077658077420261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370310378051772051613507 6555465567077658077420261)
                  ·
                    refine ⟨1229149793827060889516299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6555465567077658077420261 1229149793827060889516299)
                    ·
                      rfl

theorem cell22_3590641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_3590641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590641 prefixEnd_3590641 := by exact prefixLift 3590641
  have htrace : WordTrace (prefixWord ++ tailWord_3590641) baseStart_3590641 baseEnd_3590641 := by
    simpa [prefixWord, tailWord_3590641, baseEnd_3590641] using wordTrace_append hprefix tailTrace_3590641
  have hstable : (prefixWord ++ tailWord_3590641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590641).length < 2 ^ (prefixWord ++ tailWord_3590641).sum := by decide
  have hdescent : baseEnd_3590641 < baseStart_3590641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590662 : List Nat := [6, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3590662 : Nat := 118140960795 + 3590662 * 2 ^ 59
def prefixEnd_3590662 : Nat := 4983230072969 + 3 ^ 40 * 3590662 * 2
def baseEnd_3590662 : Nat := 409718994185407944913745

theorem tailTrace_3590662 : CollatzResearch.WordTrace tailWord_3590662 prefixEnd_3590662 409718994185407944913745 := by
  unfold tailWord_3590662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4092568816176633909139945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87308134745101523394985493 4092568816176633909139945)
  ·
    refine ⟨3069426612132475431854959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4092568816176633909139945 3069426612132475431854959)
    ·
      refine ⟨4604139918198713147782439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3069426612132475431854959 4604139918198713147782439)
      ·
        refine ⟨6906209877298069721673659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604139918198713147782439 6906209877298069721673659)
        ·
          refine ⟨10359314815947104582510489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906209877298069721673659 10359314815947104582510489)
          ·
            refine ⟨7769486111960328436882867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10359314815947104582510489 7769486111960328436882867)
            ·
              refine ⟨11654229167940492655324301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769486111960328436882867 11654229167940492655324301)
              ·
                refine ⟨4370335937977684745746613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11654229167940492655324301 4370335937977684745746613)
                ·
                  refine ⟨409718994185407944913745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4370335937977684745746613 409718994185407944913745)
                  ·
                    rfl

theorem cell22_3590662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3590662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590662 prefixEnd_3590662 := by exact prefixLift 3590662
  have htrace : WordTrace (prefixWord ++ tailWord_3590662) baseStart_3590662 baseEnd_3590662 := by
    simpa [prefixWord, tailWord_3590662, baseEnd_3590662] using wordTrace_append hprefix tailTrace_3590662
  have hstable : (prefixWord ++ tailWord_3590662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590662).length < 2 ^ (prefixWord ++ tailWord_3590662).sum := by decide
  have hdescent : baseEnd_3590662 < baseStart_3590662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590688 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 1, 5]
def baseStart_3590688 : Nat := 118140960795 + 3590688 * 2 ^ 59
def prefixEnd_3590688 : Nat := 4983230072969 + 3 ^ 40 * 3590688 * 2
def baseEnd_3590688 : Nat := 1229165882887568433591155

theorem tailTrace_3590688 : CollatzResearch.WordTrace tailWord_3590688 prefixEnd_3590688 1229165882887568433591155 := by
  unfold tailWord_3590688
  simp only [CollatzResearch.WordTrace]
  refine ⟨65481575207779045766462359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87308766943705394355283145 65481575207779045766462359)
  ·
    refine ⟨98222362811668568649693539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65481575207779045766462359 98222362811668568649693539)
    ·
      refine ⟨147333544217502852974540309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98222362811668568649693539 147333544217502852974540309)
      ·
        refine ⟨6906259885195446233181577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147333544217502852974540309 6906259885195446233181577)
        ·
          refine ⟨5179694913896584674886183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6906259885195446233181577 5179694913896584674886183)
          ·
            refine ⟨7769542370844877012329275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179694913896584674886183 7769542370844877012329275)
            ·
              refine ⟨11654313556267315518493913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769542370844877012329275 11654313556267315518493913)
              ·
                refine ⟨8740735167200486638870435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11654313556267315518493913 8740735167200486638870435)
                ·
                  refine ⟨13111102750800729958305653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8740735167200486638870435 13111102750800729958305653)
                  ·
                    refine ⟨1229165882887568433591155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13111102750800729958305653 1229165882887568433591155)
                    ·
                      rfl

theorem cell22_3590688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_3590688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590688 prefixEnd_3590688 := by exact prefixLift 3590688
  have htrace : WordTrace (prefixWord ++ tailWord_3590688) baseStart_3590688 baseEnd_3590688 := by
    simpa [prefixWord, tailWord_3590688, baseEnd_3590688] using wordTrace_append hprefix tailTrace_3590688
  have hstable : (prefixWord ++ tailWord_3590688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590688).length < 2 ^ (prefixWord ++ tailWord_3590688).sum := by decide
  have hdescent : baseEnd_3590688 < baseStart_3590688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590692 : List Nat := [2, 3, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_3590692 : Nat := 118140960795 + 3590692 * 2 ^ 59
def prefixEnd_3590692 : Nat := 4983230072969 + 3 ^ 40 * 3590692 * 2
def baseEnd_3590692 : Nat := 1229167252169313756491143

theorem tailTrace_3590692 : CollatzResearch.WordTrace tailWord_3590692 prefixEnd_3590692 1229167252169313756491143 := by
  unfold tailWord_3590692
  simp only [CollatzResearch.WordTrace]
  refine ⟨65481648153771800108035165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87308864205029066810713553 65481648153771800108035165)
  ·
    refine ⟨24555618057664425040513187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65481648153771800108035165 24555618057664425040513187)
    ·
      refine ⟨36833427086496637560769781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555618057664425040513187 36833427086496637560769781)
      ·
        refine ⟨3453133789359059771322167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36833427086496637560769781 3453133789359059771322167)
        ·
          refine ⟨5179700684038589656983251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453133789359059771322167 5179700684038589656983251)
          ·
            refine ⟨7769551026057884485474877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179700684038589656983251 7769551026057884485474877)
            ·
              refine ⟨2913581634771706682053079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7769551026057884485474877 2913581634771706682053079)
              ·
                refine ⟨4370372452157560023079619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2913581634771706682053079 4370372452157560023079619)
                ·
                  refine ⟨6555558678236340034619429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370372452157560023079619 6555558678236340034619429)
                  ·
                    refine ⟨1229167252169313756491143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6555558678236340034619429 1229167252169313756491143)
                    ·
                      rfl

theorem cell22_3590692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_3590692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590692 prefixEnd_3590692 := by exact prefixLift 3590692
  have htrace : WordTrace (prefixWord ++ tailWord_3590692) baseStart_3590692 baseEnd_3590692 := by
    simpa [prefixWord, tailWord_3590692, baseEnd_3590692] using wordTrace_append hprefix tailTrace_3590692
  have hstable : (prefixWord ++ tailWord_3590692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590692).length < 2 ^ (prefixWord ++ tailWord_3590692).sum := by decide
  have hdescent : baseEnd_3590692 < baseStart_3590692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590729 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 11]
def baseStart_3590729 : Nat := 118140960795 + 3590729 * 2 ^ 59
def prefixEnd_3590729 : Nat := 4983230072969 + 3 ^ 40 * 3590729 * 2
def baseEnd_3590729 : Nat := 409726639341819331105343

theorem tailTrace_3590729 : CollatzResearch.WordTrace tailWord_3590729 prefixEnd_3590729 409726639341819331105343 := by
  unfold tailWord_3590729
  simp only [CollatzResearch.WordTrace]
  refine ⟨130964645808409555535167241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87309763872273037023444827 130964645808409555535167241)
  ·
    refine ⟨98223484356307166651375431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130964645808409555535167241 98223484356307166651375431)
    ·
      refine ⟨147335226534460749977063147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98223484356307166651375431 147335226534460749977063147)
      ·
        refine ⟨221002839801691124965594721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147335226534460749977063147 221002839801691124965594721)
        ·
          refine ⟨165752129851268343724196041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221002839801691124965594721 165752129851268343724196041)
          ·
            refine ⟨124314097388451257793147031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165752129851268343724196041 124314097388451257793147031)
            ·
              refine ⟨186471146082676886689720547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124314097388451257793147031 186471146082676886689720547)
              ·
                refine ⟨279706719124015330034580821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186471146082676886689720547 279706719124015330034580821)
                ·
                  refine ⟨409726639341819331105343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 279706719124015330034580821 409726639341819331105343)
                  ·
                    rfl

theorem cell22_3590729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_3590729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590729 prefixEnd_3590729 := by exact prefixLift 3590729
  have htrace : WordTrace (prefixWord ++ tailWord_3590729) baseStart_3590729 baseEnd_3590729 := by
    simpa [prefixWord, tailWord_3590729, baseEnd_3590729] using wordTrace_append hprefix tailTrace_3590729
  have hstable : (prefixWord ++ tailWord_3590729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590729).length < 2 ^ (prefixWord ++ tailWord_3590729).sum := by decide
  have hdescent : baseEnd_3590729 < baseStart_3590729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590786 : List Nat := [3, 4, 3, 1, 2, 1, 2, 6]
def baseStart_3590786 : Nat := 118140960795 + 3590786 * 2 ^ 59
def prefixEnd_3590786 : Nat := 4983230072969 + 3 ^ 40 * 3590786 * 2
def baseEnd_3590786 : Nat := 136577714476703204960095

theorem tailTrace_3590786 : CollatzResearch.WordTrace tailWord_3590786 prefixEnd_3590786 136577714476703204960095 := by
  unfold tailWord_3590786
  simp only [CollatzResearch.WordTrace]
  refine ⟨32741681192300763567498053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87311149846135369513328141 32741681192300763567498053)
  ·
    refine ⟨6139065223556393168905885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32741681192300763567498053 6139065223556393168905885)
    ·
      refine ⟨2302149458833647438339707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6139065223556393168905885 2302149458833647438339707)
      ·
        refine ⟨3453224188250471157509561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302149458833647438339707 3453224188250471157509561)
        ·
          refine ⟨2589918141187853368132171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3453224188250471157509561 2589918141187853368132171)
          ·
            refine ⟨3884877211781780052198257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2589918141187853368132171 3884877211781780052198257)
            ·
              refine ⟨2913657908836335039148693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3884877211781780052198257 2913657908836335039148693)
              ·
                refine ⟨136577714476703204960095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2913657908836335039148693 136577714476703204960095)
                ·
                  rfl

theorem cell22_3590786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 6].length) (baseStart_3590786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590786 prefixEnd_3590786 := by exact prefixLift 3590786
  have htrace : WordTrace (prefixWord ++ tailWord_3590786) baseStart_3590786 baseEnd_3590786 := by
    simpa [prefixWord, tailWord_3590786, baseEnd_3590786] using wordTrace_append hprefix tailTrace_3590786
  have hstable : (prefixWord ++ tailWord_3590786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590786).length < 2 ^ (prefixWord ++ tailWord_3590786).sum := by decide
  have hdescent : baseEnd_3590786 < baseStart_3590786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590791 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 6]
def baseStart_3590791 : Nat := 118140960795 + 3590791 * 2 ^ 59
def prefixEnd_3590791 : Nat := 4983230072969 + 3 ^ 40 * 3590791 * 2
def baseEnd_3590791 : Nat := 409733713964170166088613

theorem tailTrace_3590791 : CollatzResearch.WordTrace tailWord_3590791 prefixEnd_3590791 409733713964170166088613 := by
  unfold tailWord_3590791
  simp only [CollatzResearch.WordTrace]
  refine ⟨130966907134184940123924227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87311271422789960082616151 130966907134184940123924227)
  ·
    refine ⟨196450360701277410185886341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130966907134184940123924227 196450360701277410185886341)
    ·
      refine ⟨36834442631489514409853689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196450360701277410185886341 36834442631489514409853689)
      ·
        refine ⟨27625831973617135807390267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36834442631489514409853689 27625831973617135807390267)
        ·
          refine ⟨41438747960425703711085401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27625831973617135807390267 41438747960425703711085401)
          ·
            refine ⟨31079060970319277783314051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41438747960425703711085401 31079060970319277783314051)
            ·
              refine ⟨46618591455478916674971077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31079060970319277783314051 46618591455478916674971077)
              ·
                refine ⟨8740985897902296876557077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46618591455478916674971077 8740985897902296876557077)
                ·
                  refine ⟨409733713964170166088613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8740985897902296876557077 409733713964170166088613)
                  ·
                    rfl

theorem cell22_3590791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 6].length) (baseStart_3590791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590791 prefixEnd_3590791 := by exact prefixLift 3590791
  have htrace : WordTrace (prefixWord ++ tailWord_3590791) baseStart_3590791 baseEnd_3590791 := by
    simpa [prefixWord, tailWord_3590791, baseEnd_3590791] using wordTrace_append hprefix tailTrace_3590791
  have hstable : (prefixWord ++ tailWord_3590791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590791).length < 2 ^ (prefixWord ++ tailWord_3590791).sum := by decide
  have hdescent : baseEnd_3590791 < baseStart_3590791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590883 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 2, 6]
def baseStart_3590883 : Nat := 118140960795 + 3590883 * 2 ^ 59
def prefixEnd_3590883 : Nat := 4983230072969 + 3 ^ 40 * 3590883 * 2
def baseEnd_3590883 : Nat := 1229232635372652924965557

theorem tailTrace_3590883 : CollatzResearch.WordTrace tailWord_3590883 prefixEnd_3590883 1229232635372652924965557 := by
  unfold tailWord_3590883
  simp only [CollatzResearch.WordTrace]
  refine ⟨130970262649851639836273303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87313508433234426557515535 130970262649851639836273303)
  ·
    refine ⟨196455393974777459754409955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130970262649851639836273303 196455393974777459754409955)
    ·
      refine ⟨294683090962166189631614933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196455393974777459754409955 294683090962166189631614933)
      ·
        refine ⟨6906634944425770069490975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 294683090962166189631614933 6906634944425770069490975)
        ·
          refine ⟨10359952416638655104236463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906634944425770069490975 10359952416638655104236463)
          ·
            refine ⟨15539928624957982656354695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359952416638655104236463 15539928624957982656354695)
            ·
              refine ⟨23309892937436973984532043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15539928624957982656354695 23309892937436973984532043)
              ·
                refine ⟨34964839406155460976798065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23309892937436973984532043 34964839406155460976798065)
                ·
                  refine ⟨26223629554616595732598549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34964839406155460976798065 26223629554616595732598549)
                  ·
                    refine ⟨1229232635372652924965557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26223629554616595732598549 1229232635372652924965557)
                    ·
                      rfl

theorem cell22_3590883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_3590883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590883 prefixEnd_3590883 := by exact prefixLift 3590883
  have htrace : WordTrace (prefixWord ++ tailWord_3590883) baseStart_3590883 baseEnd_3590883 := by
    simpa [prefixWord, tailWord_3590883, baseEnd_3590883] using wordTrace_append hprefix tailTrace_3590883
  have hstable : (prefixWord ++ tailWord_3590883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590883).length < 2 ^ (prefixWord ++ tailWord_3590883).sum := by decide
  have hdescent : baseEnd_3590883 < baseStart_3590883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590919 : List Nat := [1, 1, 4, 4, 1, 2, 2, 3, 1, 3]
def baseStart_3590919 : Nat := 118140960795 + 3590919 * 2 ^ 59
def prefixEnd_3590919 : Nat := 4983230072969 + 3 ^ 40 * 3590919 * 2
def baseEnd_3590919 : Nat := 1229244958908360831065447

theorem tailTrace_3590919 : CollatzResearch.WordTrace tailWord_3590919 prefixEnd_3590919 1229244958908360831065447 := by
  unfold tailWord_3590919
  simp only [CollatzResearch.WordTrace]
  refine ⟨130971575677721217984583811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87314383785147478656389207 130971575677721217984583811)
  ·
    refine ⟨196457363516581826976875717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130971575677721217984583811 196457363516581826976875717)
    ·
      refine ⟨36835755659359092558164197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196457363516581826976875717 36835755659359092558164197)
      ·
        refine ⟨6906704186129829854655787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36835755659359092558164197 6906704186129829854655787)
        ·
          refine ⟨10360056279194744781983681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906704186129829854655787 10360056279194744781983681)
          ·
            refine ⟨7770042209396058586487761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10360056279194744781983681 7770042209396058586487761)
            ·
              refine ⟨5827531657047043939865821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7770042209396058586487761 5827531657047043939865821)
              ·
                refine ⟨2185324371392641477449683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5827531657047043939865821 2185324371392641477449683)
                ·
                  refine ⟨3277986557088962216174525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2185324371392641477449683 3277986557088962216174525)
                  ·
                    refine ⟨1229244958908360831065447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3277986557088962216174525 1229244958908360831065447)
                    ·
                      rfl

theorem cell22_3590919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_3590919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590919 prefixEnd_3590919 := by exact prefixLift 3590919
  have htrace : WordTrace (prefixWord ++ tailWord_3590919) baseStart_3590919 baseEnd_3590919 := by
    simpa [prefixWord, tailWord_3590919, baseEnd_3590919] using wordTrace_append hprefix tailTrace_3590919
  have hstable : (prefixWord ++ tailWord_3590919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590919).length < 2 ^ (prefixWord ++ tailWord_3590919).sum := by decide
  have hdescent : baseEnd_3590919 < baseStart_3590919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590943 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 6]
def baseStart_3590943 : Nat := 118140960795 + 3590943 * 2 ^ 59
def prefixEnd_3590943 : Nat := 4983230072969 + 3 ^ 40 * 3590943 * 2
def baseEnd_3590943 : Nat := 409751058199610922821791

theorem tailTrace_3590943 : CollatzResearch.WordTrace tailWord_3590943 prefixEnd_3590943 409751058199610922821791 := by
  unfold tailWord_3590943
  simp only [CollatzResearch.WordTrace]
  refine ⟨130972451029634270083457483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87314967353089513388971655 130972451029634270083457483)
  ·
    refine ⟨196458676544451405125186225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130972451029634270083457483 196458676544451405125186225)
    ·
      refine ⟨147344007408338553843889669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196458676544451405125186225 147344007408338553843889669)
      ·
        refine ⟨27627001389063478845729313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147344007408338553843889669 27627001389063478845729313)
        ·
          refine ⟨20720251041797609134296985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27627001389063478845729313 20720251041797609134296985)
          ·
            refine ⟨15540188281348206850722739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20720251041797609134296985 15540188281348206850722739)
            ·
              refine ⟨23310282422022310276084109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540188281348206850722739 23310282422022310276084109)
              ·
                refine ⟨8741355908258366353531541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23310282422022310276084109 8741355908258366353531541)
                ·
                  refine ⟨409751058199610922821791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8741355908258366353531541 409751058199610922821791)
                  ·
                    rfl

theorem cell22_3590943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 6].length) (baseStart_3590943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590943 prefixEnd_3590943 := by exact prefixLift 3590943
  have htrace : WordTrace (prefixWord ++ tailWord_3590943) baseStart_3590943 baseEnd_3590943 := by
    simpa [prefixWord, tailWord_3590943, baseEnd_3590943] using wordTrace_append hprefix tailTrace_3590943
  have hstable : (prefixWord ++ tailWord_3590943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590943).length < 2 ^ (prefixWord ++ tailWord_3590943).sum := by decide
  have hdescent : baseEnd_3590943 < baseStart_3590943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590975 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 4, 3]
def baseStart_3590975 : Nat := 118140960795 + 3590975 * 2 ^ 59
def prefixEnd_3590975 : Nat := 4983230072969 + 3 ^ 40 * 3590975 * 2
def baseEnd_3590975 : Nat := 1229264128852795351665275

theorem tailTrace_3590975 : CollatzResearch.WordTrace tailWord_3590975 prefixEnd_3590975 1229264128852795351665275 := by
  unfold tailWord_3590975
  simp only [CollatzResearch.WordTrace]
  refine ⟨130973618165518339548622379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87315745443678893032414919 130973618165518339548622379)
  ·
    refine ⟨196460427248277509322933569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130973618165518339548622379 196460427248277509322933569)
    ·
      refine ⟨147345320436208131992200177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196460427248277509322933569 147345320436208131992200177)
      ·
        refine ⟨110508990327156098994150133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147345320436208131992200177 110508990327156098994150133)
        ·
          refine ⟨10360217843170884280701575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110508990327156098994150133 10360217843170884280701575)
          ·
            refine ⟨15540326764756326421052363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360217843170884280701575 15540326764756326421052363)
            ·
              refine ⟨23310490147134489631578545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540326764756326421052363 23310490147134489631578545)
              ·
                refine ⟨17482867610350867223683909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23310490147134489631578545 17482867610350867223683909)
                ·
                  refine ⟨3278037676940787604440733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17482867610350867223683909 3278037676940787604440733)
                  ·
                    refine ⟨1229264128852795351665275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278037676940787604440733 1229264128852795351665275)
                    ·
                      rfl

theorem cell22_3590975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 4, 3].length) (baseStart_3590975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590975 prefixEnd_3590975 := by exact prefixLift 3590975
  have htrace : WordTrace (prefixWord ++ tailWord_3590975) baseStart_3590975 baseEnd_3590975 := by
    simpa [prefixWord, tailWord_3590975, baseEnd_3590975] using wordTrace_append hprefix tailTrace_3590975
  have hstable : (prefixWord ++ tailWord_3590975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590975).length < 2 ^ (prefixWord ++ tailWord_3590975).sum := by decide
  have hdescent : baseEnd_3590975 < baseStart_3590975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3590988 : List Nat := [2, 2, 1, 3, 3, 1, 10]
def baseStart_3590988 : Nat := 118140960795 + 3590988 * 2 ^ 59
def prefixEnd_3590988 : Nat := 4983230072969 + 3 ^ 40 * 3590988 * 2
def baseEnd_3590988 : Nat := 45528465889572875966305

theorem tailTrace_3590988 : CollatzResearch.WordTrace tailWord_3590988 prefixEnd_3590988 45528465889572875966305 := by
  unfold tailWord_3590988
  simp only [CollatzResearch.WordTrace]
  refine ⟨65487046157235621384422809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87316061542980828512563745 65487046157235621384422809)
  ·
    refine ⟨49115284617926716038317107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65487046157235621384422809 49115284617926716038317107)
    ·
      refine ⟨73672926926890074057475661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49115284617926716038317107 73672926926890074057475661)
      ·
        refine ⟨27627347597583777771553373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73672926926890074057475661 27627347597583777771553373)
        ·
          refine ⟨10360255349093916664332515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27627347597583777771553373 10360255349093916664332515)
          ·
            refine ⟨15540383023640874996498773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360255349093916664332515 15540383023640874996498773)
            ·
              refine ⟨45528465889572875966305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15540383023640874996498773 45528465889572875966305)
              ·
                rfl

theorem cell22_3590988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 10].length) (baseStart_3590988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3590988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3590988 prefixEnd_3590988 := by exact prefixLift 3590988
  have htrace : WordTrace (prefixWord ++ tailWord_3590988) baseStart_3590988 baseEnd_3590988 := by
    simpa [prefixWord, tailWord_3590988, baseEnd_3590988] using wordTrace_append hprefix tailTrace_3590988
  have hstable : (prefixWord ++ tailWord_3590988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3590988).length < 2 ^ (prefixWord ++ tailWord_3590988).sum := by decide
  have hdescent : baseEnd_3590988 < baseStart_3590988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3590988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591020 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 5, 3]
def baseStart_3591020 : Nat := 118140960795 + 3591020 * 2 ^ 59
def prefixEnd_3591020 : Nat := 4983230072969 + 3 ^ 40 * 3591020 * 2
def baseEnd_3591020 : Nat := 1229279533272430234290137

theorem tailTrace_3591020 : CollatzResearch.WordTrace tailWord_3591020 prefixEnd_3591020 1229279533272430234290137 := by
  unfold tailWord_3591020
  simp only [CollatzResearch.WordTrace]
  refine ⟨65487629725177656117005257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87316839633570208156007009 65487629725177656117005257)
  ·
    refine ⟨49115722293883242087753943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65487629725177656117005257 49115722293883242087753943)
    ·
      refine ⟨73673583440824863131630915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49115722293883242087753943 73673583440824863131630915)
      ·
        refine ⟨110510375161237294697446373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73673583440824863131630915 110510375161237294697446373)
        ·
          refine ⟨20720695342731992755771195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110510375161237294697446373 20720695342731992755771195)
          ·
            refine ⟨31081043014097989133656793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20720695342731992755771195 31081043014097989133656793)
            ·
              refine ⟨23310782260573491850242595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31081043014097989133656793 23310782260573491850242595)
              ·
                refine ⟨34966173390860237775363893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23310782260573491850242595 34966173390860237775363893)
                ·
                  refine ⟨3278078755393147291440365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34966173390860237775363893 3278078755393147291440365)
                  ·
                    refine ⟨1229279533272430234290137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278078755393147291440365 1229279533272430234290137)
                    ·
                      rfl

theorem cell22_3591020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_3591020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591020 prefixEnd_3591020 := by exact prefixLift 3591020
  have htrace : WordTrace (prefixWord ++ tailWord_3591020) baseStart_3591020 baseEnd_3591020 := by
    simpa [prefixWord, tailWord_3591020, baseEnd_3591020] using wordTrace_append hprefix tailTrace_3591020
  have hstable : (prefixWord ++ tailWord_3591020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591020).length < 2 ^ (prefixWord ++ tailWord_3591020).sum := by decide
  have hdescent : baseEnd_3591020 < baseStart_3591020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591097 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_3591097 : Nat := 118140960795 + 3591097 * 2 ^ 59
def prefixEnd_3591097 : Nat := 4983230072969 + 3 ^ 40 * 3591097 * 2
def baseEnd_3591097 : Nat := 1229305891946027700114901

theorem tailTrace_3591097 : CollatzResearch.WordTrace tailWord_3591097 prefixEnd_3591097 1229305891946027700114901 := by
  unfold tailWord_3591097
  simp only [CollatzResearch.WordTrace]
  refine ⟨130978067871076354384563545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87318711914050902923042363 130978067871076354384563545)
  ·
    refine ⟨98233550903307265788422659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130978067871076354384563545 98233550903307265788422659)
    ·
      refine ⟨147350326354960898682633989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98233550903307265788422659 147350326354960898682633989)
      ·
        refine ⟨27628186191555168502993873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147350326354960898682633989 27628186191555168502993873)
        ·
          refine ⟨20721139643666376377245405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27628186191555168502993873 20721139643666376377245405)
          ·
            refine ⟨7770427366374891141467027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20721139643666376377245405 7770427366374891141467027)
            ·
              refine ⟨11655641049562336712200541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770427366374891141467027 11655641049562336712200541)
              ·
                refine ⟨4370865393585876267075203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11655641049562336712200541 4370865393585876267075203)
                ·
                  refine ⟨6556298090378814400612805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370865393585876267075203 6556298090378814400612805)
                  ·
                    refine ⟨1229305891946027700114901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6556298090378814400612805 1229305891946027700114901)
                    ·
                      rfl

theorem cell22_3591097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_3591097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591097 prefixEnd_3591097 := by exact prefixLift 3591097
  have htrace : WordTrace (prefixWord ++ tailWord_3591097) baseStart_3591097 baseEnd_3591097 := by
    simpa [prefixWord, tailWord_3591097, baseEnd_3591097] using wordTrace_append hprefix tailTrace_3591097
  have hstable : (prefixWord ++ tailWord_3591097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591097).length < 2 ^ (prefixWord ++ tailWord_3591097).sum := by decide
  have hdescent : baseEnd_3591097 < baseStart_3591097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591112 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 6]
def baseStart_3591112 : Nat := 118140960795 + 3591112 * 2 ^ 59
def prefixEnd_3591112 : Nat := 4983230072969 + 3 ^ 40 * 3591112 * 2
def baseEnd_3591112 : Nat := 409770342250857553663285

theorem tailTrace_3591112 : CollatzResearch.WordTrace tailWord_3591112 prefixEnd_3591112 409770342250857553663285 := by
  unfold tailWord_3591112
  simp only [CollatzResearch.WordTrace]
  refine ⟨65489307483011005973179795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87319076644014674630906393 65489307483011005973179795)
  ·
    refine ⟨98233961224516508959769693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65489307483011005973179795 98233961224516508959769693)
    ·
      refine ⟨36837735459193690859913635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98233961224516508959769693 36837735459193690859913635)
      ·
        refine ⟨55256603188790536289870453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36837735459193690859913635 55256603188790536289870453)
        ·
          refine ⟨5180306548949112777175355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55256603188790536289870453 5180306548949112777175355)
          ·
            refine ⟨7770459823423669165763033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180306548949112777175355 7770459823423669165763033)
            ·
              refine ⟨5827844867567751874322275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7770459823423669165763033 5827844867567751874322275)
              ·
                refine ⟨8741767301351627811483413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827844867567751874322275 8741767301351627811483413)
                ·
                  refine ⟨409770342250857553663285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8741767301351627811483413 409770342250857553663285)
                  ·
                    rfl

theorem cell22_3591112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 6].length) (baseStart_3591112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591112 prefixEnd_3591112 := by exact prefixLift 3591112
  have htrace : WordTrace (prefixWord ++ tailWord_3591112) baseStart_3591112 baseEnd_3591112 := by
    simpa [prefixWord, tailWord_3591112, baseEnd_3591112] using wordTrace_append hprefix tailTrace_3591112
  have hstable : (prefixWord ++ tailWord_3591112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591112).length < 2 ^ (prefixWord ++ tailWord_3591112).sum := by decide
  have hdescent : baseEnd_3591112 < baseStart_3591112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591264 : List Nat := [2, 1, 1, 3, 2, 2, 4, 3, 4]
def baseStart_3591264 : Nat := 118140960795 + 3591264 * 2 ^ 59
def prefixEnd_3591264 : Nat := 4983230072969 + 3 ^ 40 * 3591264 * 2
def baseEnd_3591264 : Nat := 409787686486298310396463

theorem tailTrace_3591264 : CollatzResearch.WordTrace tailWord_3591264 prefixEnd_3591264 409787686486298310396463 := by
  unfold tailWord_3591264
  simp only [CollatzResearch.WordTrace]
  refine ⟨65492079430735670952946423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87322772574314227937261897 65492079430735670952946423)
  ·
    refine ⟨98238119146103506429419635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65492079430735670952946423 98238119146103506429419635)
    ·
      refine ⟨147357178719155259644129453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98238119146103506429419635 147357178719155259644129453)
      ·
        refine ⟨55258942019683222366548545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147357178719155259644129453 55258942019683222366548545)
        ·
          refine ⟨41444206514762416774911409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55258942019683222366548545 41444206514762416774911409)
          ·
            refine ⟨31083154886071812581183557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41444206514762416774911409 31083154886071812581183557)
            ·
              refine ⟨5828091541138464858971917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31083154886071812581183557 5828091541138464858971917)
              ·
                refine ⟨2185534327926924322114469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5828091541138464858971917 2185534327926924322114469)
                ·
                  refine ⟨409787686486298310396463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185534327926924322114469 409787686486298310396463)
                  ·
                    rfl

theorem cell22_3591264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 4].length) (baseStart_3591264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591264 prefixEnd_3591264 := by exact prefixLift 3591264
  have htrace : WordTrace (prefixWord ++ tailWord_3591264) baseStart_3591264 baseEnd_3591264 := by
    simpa [prefixWord, tailWord_3591264, baseEnd_3591264] using wordTrace_append hprefix tailTrace_3591264
  have hstable : (prefixWord ++ tailWord_3591264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591264).length < 2 ^ (prefixWord ++ tailWord_3591264).sum := by decide
  have hdescent : baseEnd_3591264 < baseStart_3591264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591266 : List Nat := [3, 3, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3591266 : Nat := 118140960795 + 3591266 * 2 ^ 59
def prefixEnd_3591266 : Nat := 4983230072969 + 3 ^ 40 * 3591266 * 2
def baseEnd_3591266 : Nat := 1229363744099767592639383

theorem tailTrace_3591266 : CollatzResearch.WordTrace tailWord_3591266 prefixEnd_3591266 1229363744099767592639383 := by
  unfold tailWord_3591266
  simp only [CollatzResearch.WordTrace]
  refine ⟨32746057951866024061866413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87322821204976064164977101 32746057951866024061866413)
  ·
    refine ⟨12279771731949759023199905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32746057951866024061866413 12279771731949759023199905)
    ·
      refine ⟨9209828798962319267399929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12279771731949759023199905 9209828798962319267399929)
      ·
        refine ⟨6907371599221739450549947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9209828798962319267399929 6907371599221739450549947)
        ·
          refine ⟨10361057398832609175824921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907371599221739450549947 10361057398832609175824921)
          ·
            refine ⟨7770793049124456881868691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10361057398832609175824921 7770793049124456881868691)
            ·
              refine ⟨11656189573686685322803037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770793049124456881868691 11656189573686685322803037)
              ·
                refine ⟨4371071090132506996051139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11656189573686685322803037 4371071090132506996051139)
                ·
                  refine ⟨6556606635198760494076709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371071090132506996051139 6556606635198760494076709)
                  ·
                    refine ⟨1229363744099767592639383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6556606635198760494076709 1229363744099767592639383)
                    ·
                      rfl

theorem cell22_3591266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3591266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591266 prefixEnd_3591266 := by exact prefixLift 3591266
  have htrace : WordTrace (prefixWord ++ tailWord_3591266) baseStart_3591266 baseEnd_3591266 := by
    simpa [prefixWord, tailWord_3591266, baseEnd_3591266] using wordTrace_append hprefix tailTrace_3591266
  have hstable : (prefixWord ++ tailWord_3591266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591266).length < 2 ^ (prefixWord ++ tailWord_3591266).sum := by decide
  have hdescent : baseEnd_3591266 < baseStart_3591266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591448 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 2, 3]
def baseStart_3591448 : Nat := 118140960795 + 3591448 * 2 ^ 59
def prefixEnd_3591448 : Nat := 4983230072969 + 3 ^ 40 * 3591448 * 2
def baseEnd_3591448 : Nat := 1229426046419179784588825

theorem tailTrace_3591448 : CollatzResearch.WordTrace tailWord_3591448 prefixEnd_3591448 1229426046419179784588825 := by
  unfold tailWord_3591448
  simp only [CollatzResearch.WordTrace]
  refine ⟨65495434946402370665295499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87327246595203160887060665 65495434946402370665295499)
  ·
    refine ⟨98243152419603555997943249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65495434946402370665295499 98243152419603555997943249)
    ·
      refine ⟨73682364314702666998457437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98243152419603555997943249 73682364314702666998457437)
      ·
        refine ⟨27630886618013500124421539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73682364314702666998457437 27630886618013500124421539)
        ·
          refine ⟨41446329927020250186632309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27630886618013500124421539 41446329927020250186632309)
          ·
            refine ⟨3885593430658148454996779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41446329927020250186632309 3885593430658148454996779)
            ·
              refine ⟨5828390145987222682495169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3885593430658148454996779 5828390145987222682495169)
              ·
                refine ⟨4371292609490417011871377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828390145987222682495169 4371292609490417011871377)
                ·
                  refine ⟨3278469457117812758903533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371292609490417011871377 3278469457117812758903533)
                  ·
                    refine ⟨1229426046419179784588825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278469457117812758903533 1229426046419179784588825)
                    ·
                      rfl

theorem cell22_3591448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_3591448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591448 prefixEnd_3591448 := by exact prefixLift 3591448
  have htrace : WordTrace (prefixWord ++ tailWord_3591448) baseStart_3591448 baseEnd_3591448 := by
    simpa [prefixWord, tailWord_3591448, baseEnd_3591448] using wordTrace_append hprefix tailTrace_3591448
  have hstable : (prefixWord ++ tailWord_3591448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591448).length < 2 ^ (prefixWord ++ tailWord_3591448).sum := by decide
  have hdescent : baseEnd_3591448 < baseStart_3591448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591478 : List Nat := [5, 1, 2, 3, 1, 1, 1, 8]
def baseStart_3591478 : Nat := 118140960795 + 3591478 * 2 ^ 59
def prefixEnd_3591478 : Nat := 4983230072969 + 3 ^ 40 * 3591478 * 2
def baseEnd_3591478 : Nat := 136604035114696634037637

theorem tailTrace_3591478 : CollatzResearch.WordTrace tailWord_3591478 prefixEnd_3591478 136604035114696634037637 := by
  unfold tailWord_3591478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8186997755168503528386443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87327976055130704302788725 8186997755168503528386443)
  ·
    refine ⟨12280496632752755292579665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8186997755168503528386443 12280496632752755292579665)
    ·
      refine ⟨9210372474564566469434749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12280496632752755292579665 9210372474564566469434749)
      ·
        refine ⟨3453889677961712426038031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9210372474564566469434749 3453889677961712426038031)
        ·
          refine ⟨5180834516942568639057047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453889677961712426038031 5180834516942568639057047)
          ·
            refine ⟨7771251775413852958585571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5180834516942568639057047 7771251775413852958585571)
            ·
              refine ⟨11656877663120779437878357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7771251775413852958585571 11656877663120779437878357)
              ·
                refine ⟨136604035114696634037637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11656877663120779437878357 136604035114696634037637)
                ·
                  rfl

theorem cell22_3591478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_3591478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591478 prefixEnd_3591478 := by exact prefixLift 3591478
  have htrace : WordTrace (prefixWord ++ tailWord_3591478) baseStart_3591478 baseEnd_3591478 := by
    simpa [prefixWord, tailWord_3591478, baseEnd_3591478] using wordTrace_append hprefix tailTrace_3591478
  have hstable : (prefixWord ++ tailWord_3591478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591478).length < 2 ^ (prefixWord ++ tailWord_3591478).sum := by decide
  have hdescent : baseEnd_3591478 < baseStart_3591478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591519 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 3, 4]
def baseStart_3591519 : Nat := 118140960795 + 3591519 * 2 ^ 59
def prefixEnd_3591519 : Nat := 4983230072969 + 3 ^ 40 * 3591519 * 2
def baseEnd_3591519 : Nat := 1229450351170159266063607

theorem tailTrace_3591519 : CollatzResearch.WordTrace tailWord_3591519 prefixEnd_3591519 1229450351170159266063607 := by
  unfold tailWord_3591519
  simp only [CollatzResearch.WordTrace]
  refine ⟨130993459475547520456425611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87328972983698346970950407 130993459475547520456425611)
  ·
    refine ⟨196490189213321280684638417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130993459475547520456425611 196490189213321280684638417)
    ·
      refine ⟨147367641909990960513478813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196490189213321280684638417 147367641909990960513478813)
      ·
        refine ⟨55262865716246610192554555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147367641909990960513478813 55262865716246610192554555)
        ·
          refine ⟨82894298574369915288831833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55262865716246610192554555 82894298574369915288831833)
          ·
            refine ⟨62170723930777436466623875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82894298574369915288831833 62170723930777436466623875)
            ·
              refine ⟨93256085896166154699935813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62170723930777436466623875 93256085896166154699935813)
              ·
                refine ⟨17485516105531154006237965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93256085896166154699935813 17485516105531154006237965)
                ·
                  refine ⟨6557068539574182752339237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17485516105531154006237965 6557068539574182752339237)
                  ·
                    refine ⟨1229450351170159266063607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557068539574182752339237 1229450351170159266063607)
                    ·
                      rfl

theorem cell22_3591519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_3591519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591519 prefixEnd_3591519 := by exact prefixLift 3591519
  have htrace : WordTrace (prefixWord ++ tailWord_3591519) baseStart_3591519 baseEnd_3591519 := by
    simpa [prefixWord, tailWord_3591519, baseEnd_3591519] using wordTrace_append hprefix tailTrace_3591519
  have hstable : (prefixWord ++ tailWord_3591519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591519).length < 2 ^ (prefixWord ++ tailWord_3591519).sum := by decide
  have hdescent : baseEnd_3591519 < baseStart_3591519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591523 : List Nat := [1, 1, 1, 5, 2, 4, 2, 1, 5]
def baseStart_3591523 : Nat := 118140960795 + 3591523 * 2 ^ 59
def prefixEnd_3591523 : Nat := 4983230072969 + 3 ^ 40 * 3591523 * 2
def baseEnd_3591523 : Nat := 409817240150634862987865

theorem tailTrace_3591523 : CollatzResearch.WordTrace tailWord_3591523 prefixEnd_3591523 409817240150634862987865 := by
  unfold tailWord_3591523
  simp only [CollatzResearch.WordTrace]
  refine ⟨130993605367533029139571223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87329070245022019426380815 130993605367533029139571223)
  ·
    refine ⟨196490408051299543709356835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130993605367533029139571223 196490408051299543709356835)
    ·
      refine ⟨294735612076949315564035253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196490408051299543709356835 294735612076949315564035253)
      ·
        refine ⟨27631463632213998334128305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294735612076949315564035253 27631463632213998334128305)
        ·
          refine ⟨20723597724160498750596229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27631463632213998334128305 20723597724160498750596229)
          ·
            refine ⟨3885674573280093515736793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20723597724160498750596229 3885674573280093515736793)
            ·
              refine ⟨2914255929960070136802595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3885674573280093515736793 2914255929960070136802595)
              ·
                refine ⟨4371383894940105205203893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914255929960070136802595 4371383894940105205203893)
                ·
                  refine ⟨409817240150634862987865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4371383894940105205203893 409817240150634862987865)
                  ·
                    rfl

theorem cell22_3591523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 5].length) (baseStart_3591523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591523 prefixEnd_3591523 := by exact prefixLift 3591523
  have htrace : WordTrace (prefixWord ++ tailWord_3591523) baseStart_3591523 baseEnd_3591523 := by
    simpa [prefixWord, tailWord_3591523, baseEnd_3591523] using wordTrace_append hprefix tailTrace_3591523
  have hstable : (prefixWord ++ tailWord_3591523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591523).length < 2 ^ (prefixWord ++ tailWord_3591523).sum := by decide
  have hdescent : baseEnd_3591523 < baseStart_3591523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591583 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 2, 3]
def baseStart_3591583 : Nat := 118140960795 + 3591583 * 2 ^ 59
def prefixEnd_3591583 : Nat := 4983230072969 + 3 ^ 40 * 3591583 * 2
def baseEnd_3591583 : Nat := 1229472259678084432463411

theorem tailTrace_3591583 : CollatzResearch.WordTrace tailWord_3591583 prefixEnd_3591583 1229472259678084432463411 := by
  unfold tailWord_3591583
  simp only [CollatzResearch.WordTrace]
  refine ⟨130995793747315659386755403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87330529164877106257836935 130995793747315659386755403)
  ·
    refine ⟨196493690620973489080133105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130995793747315659386755403 196493690620973489080133105)
    ·
      refine ⟨147370267965730116810099829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196493690620973489080133105 147370267965730116810099829)
      ·
        refine ⟨13815962621787198450946859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147370267965730116810099829 13815962621787198450946859)
        ·
          refine ⟨20723943932680797676420289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13815962621787198450946859 20723943932680797676420289)
          ·
            refine ⟨15542957949510598257315217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20723943932680797676420289 15542957949510598257315217)
            ·
              refine ⟨11657218462132948692986413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15542957949510598257315217 11657218462132948692986413)
              ·
                refine ⟨4371456923299855759869905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11657218462132948692986413 4371456923299855759869905)
                ·
                  refine ⟨3278592692474891819902429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371456923299855759869905 3278592692474891819902429)
                  ·
                    refine ⟨1229472259678084432463411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278592692474891819902429 1229472259678084432463411)
                    ·
                      rfl

theorem cell22_3591583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2, 3].length) (baseStart_3591583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591583 prefixEnd_3591583 := by exact prefixLift 3591583
  have htrace : WordTrace (prefixWord ++ tailWord_3591583) baseStart_3591583 baseEnd_3591583 := by
    simpa [prefixWord, tailWord_3591583, baseEnd_3591583] using wordTrace_append hprefix tailTrace_3591583
  have hstable : (prefixWord ++ tailWord_3591583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591583).length < 2 ^ (prefixWord ++ tailWord_3591583).sum := by decide
  have hdescent : baseEnd_3591583 < baseStart_3591583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591628 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_3591628 : Nat := 118140960795 + 3591628 * 2 ^ 59
def prefixEnd_3591628 : Nat := 4983230072969 + 3 ^ 40 * 3591628 * 2
def baseEnd_3591628 : Nat := 1229487664097719315088273

theorem tailTrace_3591628 : CollatzResearch.WordTrace tailWord_3591628 prefixEnd_3591628 1229487664097719315088273 := by
  unfold tailWord_3591628
  simp only [CollatzResearch.WordTrace]
  refine ⟨65498717516076316036071769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87331623354768421381429025 65498717516076316036071769)
  ·
    refine ⟨49124038137057237027053827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65498717516076316036071769 49124038137057237027053827)
    ·
      refine ⟨73686057205585855540580741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49124038137057237027053827 73686057205585855540580741)
      ·
        refine ⟨13816135726047347913858889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73686057205585855540580741 13816135726047347913858889)
        ·
          refine ⟨10362101794535510935394167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13816135726047347913858889 10362101794535510935394167)
          ·
            refine ⟨15543152691803266403091251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10362101794535510935394167 15543152691803266403091251)
            ·
              refine ⟨23314729037704899604636877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15543152691803266403091251 23314729037704899604636877)
              ·
                refine ⟨8743023389139337351738829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23314729037704899604636877 8743023389139337351738829)
                ·
                  refine ⟨3278633770927251506902061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8743023389139337351738829 3278633770927251506902061)
                  ·
                    refine ⟨1229487664097719315088273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278633770927251506902061 1229487664097719315088273)
                    ·
                      rfl

theorem cell22_3591628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_3591628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591628 prefixEnd_3591628 := by exact prefixLift 3591628
  have htrace : WordTrace (prefixWord ++ tailWord_3591628) baseStart_3591628 baseEnd_3591628 := by
    simpa [prefixWord, tailWord_3591628, baseEnd_3591628] using wordTrace_append hprefix tailTrace_3591628
  have hstable : (prefixWord ++ tailWord_3591628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591628).length < 2 ^ (prefixWord ++ tailWord_3591628).sum := by decide
  have hdescent : baseEnd_3591628 < baseStart_3591628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591692 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 5]
def baseStart_3591692 : Nat := 118140960795 + 3591692 * 2 ^ 59
def prefixEnd_3591692 : Nat := 4983230072969 + 3 ^ 40 * 3591692 * 2
def baseEnd_3591692 : Nat := 409836524201881493829359

theorem tailTrace_3591692 : CollatzResearch.WordTrace tailWord_3591692 prefixEnd_3591692 409836524201881493829359 := by
  unfold tailWord_3591692
  simp only [CollatzResearch.WordTrace]
  refine ⟨65499884651960385501236665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87333179535947180668315553 65499884651960385501236665)
  ·
    refine ⟨49124913488970289125927499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65499884651960385501236665 49124913488970289125927499)
    ·
      refine ⟨73687370233455433688891249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49124913488970289125927499 73687370233455433688891249)
      ·
        refine ⟨55265527675091575266668437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73687370233455433688891249 55265527675091575266668437)
        ·
          refine ⟨2590571609769917590625083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55265527675091575266668437 2590571609769917590625083)
          ·
            refine ⟨3885857414654876385937625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590571609769917590625083 3885857414654876385937625)
            ·
              refine ⟨2914393060991157289453219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3885857414654876385937625 2914393060991157289453219)
              ·
                refine ⟨4371589591486735934179829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914393060991157289453219 4371589591486735934179829)
                ·
                  refine ⟨409836524201881493829359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4371589591486735934179829 409836524201881493829359)
                  ·
                    rfl

theorem cell22_3591692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 5].length) (baseStart_3591692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591692 prefixEnd_3591692 := by exact prefixLift 3591692
  have htrace : WordTrace (prefixWord ++ tailWord_3591692) baseStart_3591692 baseEnd_3591692 := by
    simpa [prefixWord, tailWord_3591692, baseEnd_3591692] using wordTrace_append hprefix tailTrace_3591692
  have hstable : (prefixWord ++ tailWord_3591692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591692).length < 2 ^ (prefixWord ++ tailWord_3591692).sum := by decide
  have hdescent : baseEnd_3591692 < baseStart_3591692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591733 : List Nat := [1, 3, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3591733 : Nat := 118140960795 + 3591733 * 2 ^ 59
def prefixEnd_3591733 : Nat := 4983230072969 + 3 ^ 40 * 3591733 * 2
def baseEnd_3591733 : Nat := 1229523607743534041212951

theorem tailTrace_3591733 : CollatzResearch.WordTrace tailWord_3591733 prefixEnd_3591733 1229523607743534041212951 := by
  unfold tailWord_3591733
  simp only [CollatzResearch.WordTrace]
  refine ⟨131001264696772235004715853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87334176464514823336477235 131001264696772235004715853)
  ·
    refine ⟨49125474261289588126768445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131001264696772235004715853 49125474261289588126768445)
    ·
      refine ⟨18422052847983595547538167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49125474261289588126768445 18422052847983595547538167)
      ·
        refine ⟨27633079271975393321307251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18422052847983595547538167 27633079271975393321307251)
        ·
          refine ⟨41449618907963089981960877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27633079271975393321307251 41449618907963089981960877)
          ·
            refine ⟨15543607090486158743235329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41449618907963089981960877 15543607090486158743235329)
            ·
              refine ⟨11657705317864619057426497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15543607090486158743235329 11657705317864619057426497)
              ·
                refine ⟨8743278988398464293069873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11657705317864619057426497 8743278988398464293069873)
                ·
                  refine ⟨6557459241298848219802405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8743278988398464293069873 6557459241298848219802405)
                  ·
                    refine ⟨1229523607743534041212951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557459241298848219802405 1229523607743534041212951)
                    ·
                      rfl

theorem cell22_3591733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3591733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591733 prefixEnd_3591733 := by exact prefixLift 3591733
  have htrace : WordTrace (prefixWord ++ tailWord_3591733) baseStart_3591733 baseEnd_3591733 := by
    simpa [prefixWord, tailWord_3591733, baseEnd_3591733] using wordTrace_append hprefix tailTrace_3591733
  have hstable : (prefixWord ++ tailWord_3591733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591733).length < 2 ^ (prefixWord ++ tailWord_3591733).sum := by decide
  have hdescent : baseEnd_3591733 < baseStart_3591733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591735 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 2, 3]
def baseStart_3591735 : Nat := 118140960795 + 3591735 * 2 ^ 59
def prefixEnd_3591735 : Nat := 4983230072969 + 3 ^ 40 * 3591735 * 2
def baseEnd_3591735 : Nat := 1229524292384406702662945

theorem tailTrace_3591735 : CollatzResearch.WordTrace tailWord_3591735 prefixEnd_3591735 1229524292384406702662945 := by
  unfold tailWord_3591735
  simp only [CollatzResearch.WordTrace]
  refine ⟨131001337642764989346288659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87334225095176659564192439 131001337642764989346288659)
  ·
    refine ⟨196502006464147484019432989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131001337642764989346288659 196502006464147484019432989)
    ·
      refine ⟨73688252424055306507287371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196502006464147484019432989 73688252424055306507287371)
      ·
        refine ⟨110532378636082959760931057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73688252424055306507287371 110532378636082959760931057)
        ·
          refine ⟨82899283977062219820698293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110532378636082959760931057 82899283977062219820698293)
          ·
            refine ⟨7771807872849583108190465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82899283977062219820698293 7771807872849583108190465)
            ·
              refine ⟨5828855904637187331142849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7771807872849583108190465 5828855904637187331142849)
              ·
                refine ⟨4371641928477890498357137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828855904637187331142849 4371641928477890498357137)
                ·
                  refine ⟨3278731446358417873767853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4371641928477890498357137 3278731446358417873767853)
                  ·
                    refine ⟨1229524292384406702662945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278731446358417873767853 1229524292384406702662945)
                    ·
                      rfl

theorem cell22_3591735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_3591735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591735 prefixEnd_3591735 := by exact prefixLift 3591735
  have htrace : WordTrace (prefixWord ++ tailWord_3591735) baseStart_3591735 baseEnd_3591735 := by
    simpa [prefixWord, tailWord_3591735, baseEnd_3591735] using wordTrace_append hprefix tailTrace_3591735
  have hstable : (prefixWord ++ tailWord_3591735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591735).length < 2 ^ (prefixWord ++ tailWord_3591735).sum := by decide
  have hdescent : baseEnd_3591735 < baseStart_3591735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591737 : List Nat := [1, 2, 1, 5, 1, 4, 2, 2, 4]
def baseStart_3591737 : Nat := 118140960795 + 3591737 * 2 ^ 59
def prefixEnd_3591737 : Nat := 4983230072969 + 3 ^ 40 * 3591737 * 2
def baseEnd_3591737 : Nat := 409841659008426454704313

theorem tailTrace_3591737 : CollatzResearch.WordTrace tailWord_3591737 prefixEnd_3591737 409841659008426454704313 := by
  unfold tailWord_3591737
  simp only [CollatzResearch.WordTrace]
  refine ⟨131001410588757743687861465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87334273725838495791907643 131001410588757743687861465)
  ·
    refine ⟨98251057941568307765896099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131001410588757743687861465 98251057941568307765896099)
    ·
      refine ⟨147376586912352461648844149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98251057941568307765896099 147376586912352461648844149)
      ·
        refine ⟨13816555023033043279579139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147376586912352461648844149 13816555023033043279579139)
        ·
          refine ⟨20724832534549564919368709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13816555023033043279579139 20724832534549564919368709)
          ·
            refine ⟨3885906100228043422381633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20724832534549564919368709 3885906100228043422381633)
            ·
              refine ⟨2914429575171032566786225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3885906100228043422381633 2914429575171032566786225)
              ·
                refine ⟨2185822181378274425089669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2914429575171032566786225 2185822181378274425089669)
                ·
                  refine ⟨409841659008426454704313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185822181378274425089669 409841659008426454704313)
                  ·
                    rfl

theorem cell22_3591737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 2, 4].length) (baseStart_3591737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591737 prefixEnd_3591737 := by exact prefixLift 3591737
  have htrace : WordTrace (prefixWord ++ tailWord_3591737) baseStart_3591737 baseEnd_3591737 := by
    simpa [prefixWord, tailWord_3591737, baseEnd_3591737] using wordTrace_append hprefix tailTrace_3591737
  have hstable : (prefixWord ++ tailWord_3591737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591737).length < 2 ^ (prefixWord ++ tailWord_3591737).sum := by decide
  have hdescent : baseEnd_3591737 < baseStart_3591737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591761 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_3591761 : Nat := 118140960795 + 3591761 * 2 ^ 59
def prefixEnd_3591761 : Nat := 4983230072969 + 3 ^ 40 * 3591761 * 2
def baseEnd_3591761 : Nat := 1229533192715751301512865

theorem tailTrace_3591761 : CollatzResearch.WordTrace tailWord_3591761 prefixEnd_3591761 1229533192715751301512865 := by
  unfold tailWord_3591761
  simp only [CollatzResearch.WordTrace]
  refine ⟨131002285940670795786735137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87334857293780530524490091 131002285940670795786735137)
  ·
    refine ⟨98251714455503096840051353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131002285940670795786735137 98251714455503096840051353)
    ·
      refine ⟨73688785841627322630038515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98251714455503096840051353 73688785841627322630038515)
      ·
        refine ⟨110533178762440983945057773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73688785841627322630038515 110533178762440983945057773)
        ·
          refine ⟨41449942035915368979396665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110533178762440983945057773 41449942035915368979396665)
          ·
            refine ⟨31087456526936526734547499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41449942035915368979396665 31087456526936526734547499)
            ·
              refine ⟨46631184790404790101821249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31087456526936526734547499 46631184790404790101821249)
              ·
                refine ⟨34973388592803592576365937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46631184790404790101821249 34973388592803592576365937)
                ·
                  refine ⟨26230041444602694432274453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34973388592803592576365937 26230041444602694432274453)
                  ·
                    refine ⟨1229533192715751301512865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26230041444602694432274453 1229533192715751301512865)
                    ·
                      rfl

theorem cell22_3591761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_3591761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591761 prefixEnd_3591761 := by exact prefixLift 3591761
  have htrace : WordTrace (prefixWord ++ tailWord_3591761) baseStart_3591761 baseEnd_3591761 := by
    simpa [prefixWord, tailWord_3591761, baseEnd_3591761] using wordTrace_append hprefix tailTrace_3591761
  have hstable : (prefixWord ++ tailWord_3591761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591761).length < 2 ^ (prefixWord ++ tailWord_3591761).sum := by decide
  have hdescent : baseEnd_3591761 < baseStart_3591761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591776 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 7]
def baseStart_3591776 : Nat := 118140960795 + 3591776 * 2 ^ 59
def prefixEnd_3591776 : Nat := 4983230072969 + 3 ^ 40 * 3591776 * 2
def baseEnd_3591776 : Nat := 409846109174098754129273

theorem tailTrace_3591776 : CollatzResearch.WordTrace tailWord_3591776 prefixEnd_3591776 409846109174098754129273 := by
  unfold tailWord_3591776
  simp only [CollatzResearch.WordTrace]
  refine ⟨65501416517808226674265591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87335222023744302232354121 65501416517808226674265591)
  ·
    refine ⟨98252124776712340011398387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65501416517808226674265591 98252124776712340011398387)
    ·
      refine ⟨147378187165068510017097581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98252124776712340011398387 147378187165068510017097581)
      ·
        refine ⟨55266820186900691256411593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147378187165068510017097581 55266820186900691256411593)
        ·
          refine ⟨41450115140175518442308695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55266820186900691256411593 41450115140175518442308695)
          ·
            refine ⟨62175172710263277663463043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41450115140175518442308695 62175172710263277663463043)
            ·
              refine ⟨93262759065394916495194565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62175172710263277663463043 93262759065394916495194565)
              ·
                refine ⟨17486767324761546842848981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 93262759065394916495194565 17486767324761546842848981)
                ·
                  refine ⟨409846109174098754129273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17486767324761546842848981 409846109174098754129273)
                  ·
                    rfl

theorem cell22_3591776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 7].length) (baseStart_3591776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591776 prefixEnd_3591776 := by exact prefixLift 3591776
  have htrace : WordTrace (prefixWord ++ tailWord_3591776) baseStart_3591776 baseEnd_3591776 := by
    simpa [prefixWord, tailWord_3591776, baseEnd_3591776] using wordTrace_append hprefix tailTrace_3591776
  have hstable : (prefixWord ++ tailWord_3591776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591776).length < 2 ^ (prefixWord ++ tailWord_3591776).sum := by decide
  have hdescent : baseEnd_3591776 < baseStart_3591776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591797 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3591797 : Nat := 118140960795 + 3591797 * 2 ^ 59
def prefixEnd_3591797 : Nat := 4983230072969 + 3 ^ 40 * 3591797 * 2
def baseEnd_3591797 : Nat := 1229545516251459207612755

theorem tailTrace_3591797 : CollatzResearch.WordTrace tailWord_3591797 prefixEnd_3591797 1229545516251459207612755 := by
  unfold tailWord_3591797
  simp only [CollatzResearch.WordTrace]
  refine ⟨131003598968540373935045645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87335732645693582623363763 131003598968540373935045645)
  ·
    refine ⟨49126349613202640225642117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131003598968540373935045645 49126349613202640225642117)
    ·
      refine ⟨9211190552475495042307897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49126349613202640225642117 9211190552475495042307897)
      ·
        refine ⟨6908392914356621281730923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9211190552475495042307897 6908392914356621281730923)
        ·
          refine ⟨10362589371534931922596385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6908392914356621281730923 10362589371534931922596385)
          ·
            refine ⟨7771942028651198941947289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10362589371534931922596385 7771942028651198941947289)
            ·
              refine ⟨5828956521488399206460467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7771942028651198941947289 5828956521488399206460467)
              ·
                refine ⟨8743434782232598809690701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828956521488399206460467 8743434782232598809690701)
                ·
                  refine ⟨3278788043337224553634013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8743434782232598809690701 3278788043337224553634013)
                  ·
                    refine ⟨1229545516251459207612755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278788043337224553634013 1229545516251459207612755)
                    ·
                      rfl

theorem cell22_3591797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3591797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591797 prefixEnd_3591797 := by exact prefixLift 3591797
  have htrace : WordTrace (prefixWord ++ tailWord_3591797) baseStart_3591797 baseEnd_3591797 := by
    simpa [prefixWord, tailWord_3591797, baseEnd_3591797] using wordTrace_append hprefix tailTrace_3591797
  have hstable : (prefixWord ++ tailWord_3591797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591797).length < 2 ^ (prefixWord ++ tailWord_3591797).sum := by decide
  have hdescent : baseEnd_3591797 < baseStart_3591797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591840 : List Nat := [2, 1, 1, 4, 3, 1, 2, 3, 1, 4]
def baseStart_3591840 : Nat := 118140960795 + 3591840 * 2 ^ 59
def prefixEnd_3591840 : Nat := 4983230072969 + 3 ^ 40 * 3591840 * 2
def baseEnd_3591840 : Nat := 1229560236030221428787623

theorem tailTrace_3591840 : CollatzResearch.WordTrace tailWord_3591840 prefixEnd_3591840 1229560236030221428787623 := by
  unfold tailWord_3591840
  simp only [CollatzResearch.WordTrace]
  refine ⟨65502583653692296139430487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87336778204923061519240649 65502583653692296139430487)
  ·
    refine ⟨98253875480538444209145731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65502583653692296139430487 98253875480538444209145731)
    ·
      refine ⟨147380813220807666313718597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98253875480538444209145731 147380813220807666313718597)
      ·
        refine ⟨27633902478901437433822237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147380813220807666313718597 27633902478901437433822237)
        ·
          refine ⟨10362713429588039037683339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27633902478901437433822237 10362713429588039037683339)
          ·
            refine ⟨15544070144382058556525009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10362713429588039037683339 15544070144382058556525009)
            ·
              refine ⟨11658052608286543917393757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15544070144382058556525009 11658052608286543917393757)
              ·
                refine ⟨4371769728107453969022659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11658052608286543917393757 4371769728107453969022659)
                ·
                  refine ⟨6557654592161180953533989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371769728107453969022659 6557654592161180953533989)
                  ·
                    refine ⟨1229560236030221428787623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557654592161180953533989 1229560236030221428787623)
                    ·
                      rfl

theorem cell22_3591840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_3591840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591840 prefixEnd_3591840 := by exact prefixLift 3591840
  have htrace : WordTrace (prefixWord ++ tailWord_3591840) baseStart_3591840 baseEnd_3591840 := by
    simpa [prefixWord, tailWord_3591840, baseEnd_3591840] using wordTrace_append hprefix tailTrace_3591840
  have hstable : (prefixWord ++ tailWord_3591840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591840).length < 2 ^ (prefixWord ++ tailWord_3591840).sum := by decide
  have hdescent : baseEnd_3591840 < baseStart_3591840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591848 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3591848 : Nat := 118140960795 + 3591848 * 2 ^ 59
def prefixEnd_3591848 : Nat := 4983230072969 + 3 ^ 40 * 3591848 * 2
def baseEnd_3591848 : Nat := 1229562974593712074587599

theorem tailTrace_3591848 : CollatzResearch.WordTrace tailWord_3591848 prefixEnd_3591848 1229562974593712074587599 := by
  unfold tailWord_3591848
  simp only [CollatzResearch.WordTrace]
  refine ⟨65502729545677804822576099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87336972727570406430101465 65502729545677804822576099)
  ·
    refine ⟨98254094318516707233864149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65502729545677804822576099 98254094318516707233864149)
    ·
      refine ⟨2302830335590235325793691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 98254094318516707233864149 2302830335590235325793691)
      ·
        refine ⟨3454245503385352988690537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302830335590235325793691 3454245503385352988690537)
        ·
          refine ⟨2590684127539014741517903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3454245503385352988690537 2590684127539014741517903)
          ·
            refine ⟨3886026191308522112276855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2590684127539014741517903 3886026191308522112276855)
            ·
              refine ⟨5829039286962783168415283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886026191308522112276855 5829039286962783168415283)
              ·
                refine ⟨8743558930444174752622925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829039286962783168415283 8743558930444174752622925)
                ·
                  refine ⟨3278834598916565532233597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8743558930444174752622925 3278834598916565532233597)
                  ·
                    refine ⟨1229562974593712074587599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278834598916565532233597 1229562974593712074587599)
                    ·
                      rfl

theorem cell22_3591848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3591848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591848 prefixEnd_3591848 := by exact prefixLift 3591848
  have htrace : WordTrace (prefixWord ++ tailWord_3591848) baseStart_3591848 baseEnd_3591848 := by
    simpa [prefixWord, tailWord_3591848, baseEnd_3591848] using wordTrace_append hprefix tailTrace_3591848
  have hstable : (prefixWord ++ tailWord_3591848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591848).length < 2 ^ (prefixWord ++ tailWord_3591848).sum := by decide
  have hdescent : baseEnd_3591848 < baseStart_3591848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591851 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 12]
def baseStart_3591851 : Nat := 118140960795 + 3591851 * 2 ^ 59
def prefixEnd_3591851 : Nat := 4983230072969 + 3 ^ 40 * 3591851 * 2
def baseEnd_3591851 : Nat := 1229564001555021066762589

theorem tailTrace_3591851 : CollatzResearch.WordTrace tailWord_3591851 prefixEnd_3591851 1229564001555021066762589 := by
  unfold tailWord_3591851
  simp only [CollatzResearch.WordTrace]
  refine ⟨131005568510344741157511407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87337045673563160771674271 131005568510344741157511407)
  ·
    refine ⟨196508352765517111736267111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131005568510344741157511407 196508352765517111736267111)
    ·
      refine ⟨294762529148275667604400667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196508352765517111736267111 294762529148275667604400667)
      ·
        refine ⟨442143793722413501406601001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294762529148275667604400667 442143793722413501406601001)
        ·
          refine ⟨331607845291810126054950751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442143793722413501406601001 331607845291810126054950751)
          ·
            refine ⟨497411767937715189082426127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331607845291810126054950751 497411767937715189082426127)
            ·
              refine ⟨746117651906572783623639191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497411767937715189082426127 746117651906572783623639191)
              ·
                refine ⟨1119176477859859175435458787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746117651906572783623639191 1119176477859859175435458787)
                ·
                  refine ⟨1678764716789788763153188181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119176477859859175435458787 1678764716789788763153188181)
                  ·
                    refine ⟨1229564001555021066762589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1678764716789788763153188181 1229564001555021066762589)
                    ·
                      rfl

theorem cell22_3591851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_3591851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591851 prefixEnd_3591851 := by exact prefixLift 3591851
  have htrace : WordTrace (prefixWord ++ tailWord_3591851) baseStart_3591851 baseEnd_3591851 := by
    simpa [prefixWord, tailWord_3591851, baseEnd_3591851] using wordTrace_append hprefix tailTrace_3591851
  have hstable : (prefixWord ++ tailWord_3591851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591851).length < 2 ^ (prefixWord ++ tailWord_3591851).sum := by decide
  have hdescent : baseEnd_3591851 < baseStart_3591851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591900 : List Nat := [2, 2, 5, 1, 2, 10]
def baseStart_3591900 : Nat := 118140960795 + 3591900 * 2 ^ 59
def prefixEnd_3591900 : Nat := 4983230072969 + 3 ^ 40 * 3591900 * 2
def baseEnd_3591900 : Nat := 15180009571066682373919

theorem tailTrace_3591900 : CollatzResearch.WordTrace tailWord_3591900 prefixEnd_3591900 15180009571066682373919 := by
  unfold tailWord_3591900
  simp only [CollatzResearch.WordTrace]
  refine ⟨65503677843583611263022577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87338237124778148350696769 65503677843583611263022577)
  ·
    refine ⟨49127758382687708447266933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65503677843583611263022577 49127758382687708447266933)
    ·
      refine ⟨4605727348376972666931275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49127758382687708447266933 4605727348376972666931275)
      ·
        refine ⟨6908591022565459000396913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605727348376972666931275 6908591022565459000396913)
        ·
          refine ⟨5181443266924094250297685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6908591022565459000396913 5181443266924094250297685)
          ·
            refine ⟨15180009571066682373919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5181443266924094250297685 15180009571066682373919)
            ·
              rfl

theorem cell22_3591900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 10].length) (baseStart_3591900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591900 prefixEnd_3591900 := by exact prefixLift 3591900
  have htrace : WordTrace (prefixWord ++ tailWord_3591900) baseStart_3591900 baseEnd_3591900 := by
    simpa [prefixWord, tailWord_3591900, baseEnd_3591900] using wordTrace_append hprefix tailTrace_3591900
  have hstable : (prefixWord ++ tailWord_3591900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591900).length < 2 ^ (prefixWord ++ tailWord_3591900).sum := by decide
  have hdescent : baseEnd_3591900 < baseStart_3591900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591942 : List Nat := [6, 2, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3591942 : Nat := 118140960795 + 3591942 * 2 ^ 59
def prefixEnd_3591942 : Nat := 4983230072969 + 3 ^ 40 * 3591942 * 2
def baseEnd_3591942 : Nat := 1229595152714727162737311

theorem tailTrace_3591942 : CollatzResearch.WordTrace tailWord_3591942 prefixEnd_3591942 1229595152714727162737311 := by
  unfold tailWord_3591942
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094027736031720740596065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87339258368676709132716053 4094027736031720740596065)
  ·
    refine ⟨3070520802023790555447049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4094027736031720740596065 3070520802023790555447049)
    ·
      refine ⟨2302890601517842916585287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3070520802023790555447049 2302890601517842916585287)
      ·
        refine ⟨3454335902276764374877931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302890601517842916585287 3454335902276764374877931)
        ·
          refine ⟨5181503853415146562316897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3454335902276764374877931 5181503853415146562316897)
          ·
            refine ⟨3886127890061359921737673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5181503853415146562316897 3886127890061359921737673)
            ·
              refine ⟨2914595917546019941303255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886127890061359921737673 2914595917546019941303255)
              ·
                refine ⟨4371893876319029911954883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2914595917546019941303255 4371893876319029911954883)
                ·
                  refine ⟨6557840814478544867932325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371893876319029911954883 6557840814478544867932325)
                  ·
                    refine ⟨1229595152714727162737311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557840814478544867932325 1229595152714727162737311)
                    ·
                      rfl

theorem cell22_3591942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3591942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591942 prefixEnd_3591942 := by exact prefixLift 3591942
  have htrace : WordTrace (prefixWord ++ tailWord_3591942) baseStart_3591942 baseEnd_3591942 := by
    simpa [prefixWord, tailWord_3591942, baseEnd_3591942] using wordTrace_append hprefix tailTrace_3591942
  have hstable : (prefixWord ++ tailWord_3591942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591942).length < 2 ^ (prefixWord ++ tailWord_3591942).sum := by decide
  have hdescent : baseEnd_3591942 < baseStart_3591942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591962 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_3591962 : Nat := 118140960795 + 3591962 * 2 ^ 59
def prefixEnd_3591962 : Nat := 4983230072969 + 3 ^ 40 * 3591962 * 2
def baseEnd_3591962 : Nat := 409867333041151259079083

theorem tailTrace_3591962 : CollatzResearch.WordTrace tailWord_3591962 prefixEnd_3591962 409867333041151259079083 := by
  unfold tailWord_3591962
  simp only [CollatzResearch.WordTrace]
  refine ⟨32752404253235651778700535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87339744675295071409868093 32752404253235651778700535)
  ·
    refine ⟨49128606379853477668050803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32752404253235651778700535 49128606379853477668050803)
    ·
      refine ⟨73692909569780216502076205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49128606379853477668050803 73692909569780216502076205)
      ·
        refine ⟨27634841088667581188278577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73692909569780216502076205 27634841088667581188278577)
        ·
          refine ⟨20726130816500685891208933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27634841088667581188278577 20726130816500685891208933)
          ·
            refine ⟨3886149528093878604601675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20726130816500685891208933 3886149528093878604601675)
            ·
              refine ⟨5829224292140817906902513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3886149528093878604601675 5829224292140817906902513)
              ·
                refine ⟨4371918219105613430176885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829224292140817906902513 4371918219105613430176885)
                ·
                  refine ⟨409867333041151259079083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4371918219105613430176885 409867333041151259079083)
                  ·
                    rfl

theorem cell22_3591962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_3591962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591962 prefixEnd_3591962 := by exact prefixLift 3591962
  have htrace : WordTrace (prefixWord ++ tailWord_3591962) baseStart_3591962 baseEnd_3591962 := by
    simpa [prefixWord, tailWord_3591962, baseEnd_3591962] using wordTrace_append hprefix tailTrace_3591962
  have hstable : (prefixWord ++ tailWord_3591962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591962).length < 2 ^ (prefixWord ++ tailWord_3591962).sum := by decide
  have hdescent : baseEnd_3591962 < baseStart_3591962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3591992 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 1, 4]
def baseStart_3591992 : Nat := 118140960795 + 3591992 * 2 ^ 59
def prefixEnd_3591992 : Nat := 4983230072969 + 3 ^ 40 * 3591992 * 2
def baseEnd_3591992 : Nat := 1229612268736543698987157

theorem tailTrace_3591992 : CollatzResearch.WordTrace tailWord_3591992 prefixEnd_3591992 1229612268736543698987157 := by
  unfold tailWord_3591992
  simp only [CollatzResearch.WordTrace]
  refine ⟨65505355601416961119197115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87340474135222614825596153 65505355601416961119197115)
  ·
    refine ⟨98258033402125441678795673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65505355601416961119197115 98258033402125441678795673)
    ·
      refine ⟨73693525051594081259096755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98258033402125441678795673 73693525051594081259096755)
      ·
        refine ⟨110540287577391121888645133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73693525051594081259096755 110540287577391121888645133)
        ·
          refine ⟨41452607841521670708241925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110540287577391121888645133 41452607841521670708241925)
          ·
            refine ⟨7772363970285313257795361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41452607841521670708241925 7772363970285313257795361)
            ·
              refine ⟨5829272977713984943346521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7772363970285313257795361 5829272977713984943346521)
              ·
                refine ⟨4371954733285488707509891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829272977713984943346521 4371954733285488707509891)
                ·
                  refine ⟨6557932099928233061264837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371954733285488707509891 6557932099928233061264837)
                  ·
                    refine ⟨1229612268736543698987157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557932099928233061264837 1229612268736543698987157)
                    ·
                      rfl

theorem cell22_3591992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 4].length) (baseStart_3591992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3591992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3591992 prefixEnd_3591992 := by exact prefixLift 3591992
  have htrace : WordTrace (prefixWord ++ tailWord_3591992) baseStart_3591992 baseEnd_3591992 := by
    simpa [prefixWord, tailWord_3591992, baseEnd_3591992] using wordTrace_append hprefix tailTrace_3591992
  have hstable : (prefixWord ++ tailWord_3591992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3591992).length < 2 ^ (prefixWord ++ tailWord_3591992).sum := by decide
  have hdescent : baseEnd_3591992 < baseStart_3591992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3591992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592005 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 6, 3]
def baseStart_3592005 : Nat := 118140960795 + 3592005 * 2 ^ 59
def prefixEnd_3592005 : Nat := 4983230072969 + 3 ^ 40 * 3592005 * 2
def baseEnd_3592005 : Nat := 1229616718902215998412117

theorem tailTrace_3592005 : CollatzResearch.WordTrace tailWord_3592005 prefixEnd_3592005 1229616718902215998412117 := by
  unfold tailWord_3592005
  simp only [CollatzResearch.WordTrace]
  refine ⟨131011185351786825458617469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87340790234524550305744979 131011185351786825458617469)
  ·
    refine ⟨49129194506920059546981551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131011185351786825458617469 49129194506920059546981551)
    ·
      refine ⟨73693791760380089320472327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49129194506920059546981551 73693791760380089320472327)
      ·
        refine ⟨110540687640570133980708491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73693791760380089320472327 110540687640570133980708491)
        ·
          refine ⟨165811031460855200971062737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110540687640570133980708491 165811031460855200971062737)
          ·
            refine ⟨124358273595641400728297053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165811031460855200971062737 124358273595641400728297053)
            ·
              refine ⟨46634352598365525273111395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124358273595641400728297053 46634352598365525273111395)
              ·
                refine ⟨69951528897548287909667093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46634352598365525273111395 69951528897548287909667093)
                ·
                  refine ⟨3278977917072575995765645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69951528897548287909667093 3278977917072575995765645)
                  ·
                    refine ⟨1229616718902215998412117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3278977917072575995765645 1229616718902215998412117)
                    ·
                      rfl

theorem cell22_3592005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_3592005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592005 prefixEnd_3592005 := by exact prefixLift 3592005
  have htrace : WordTrace (prefixWord ++ tailWord_3592005) baseStart_3592005 baseEnd_3592005 := by
    simpa [prefixWord, tailWord_3592005, baseEnd_3592005] using wordTrace_append hprefix tailTrace_3592005
  have hstable : (prefixWord ++ tailWord_3592005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592005).length < 2 ^ (prefixWord ++ tailWord_3592005).sum := by decide
  have hdescent : baseEnd_3592005 < baseStart_3592005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592007 : List Nat := [1, 1, 4, 1, 2, 1, 5, 3, 4]
def baseStart_3592007 : Nat := 118140960795 + 3592007 * 2 ^ 59
def prefixEnd_3592007 : Nat := 4983230072969 + 3 ^ 40 * 3592007 * 2
def baseEnd_3592007 : Nat := 409872467847696219954037

theorem tailTrace_3592007 : CollatzResearch.WordTrace tailWord_3592007 prefixEnd_3592007 409872467847696219954037 := by
  unfold tailWord_3592007
  simp only [CollatzResearch.WordTrace]
  refine ⟨131011258297779579800190275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87340838865186386533460183 131011258297779579800190275)
  ·
    refine ⟨196516887446669369700285413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131011258297779579800190275 196516887446669369700285413)
    ·
      refine ⟨36846916396250506818803515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196516887446669369700285413 36846916396250506818803515)
      ·
        refine ⟨55270374594375760228205273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36846916396250506818803515 55270374594375760228205273)
        ·
          refine ⟨41452780945781820171153955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55270374594375760228205273 41452780945781820171153955)
          ·
            refine ⟨62179171418672730256730933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41452780945781820171153955 62179171418672730256730933)
            ·
              refine ⟨5829297320500568461568525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62179171418672730256730933 5829297320500568461568525)
              ·
                refine ⟨2185986495187713173088197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5829297320500568461568525 2185986495187713173088197)
                ·
                  refine ⟨409872467847696219954037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2185986495187713173088197 409872467847696219954037)
                  ·
                    rfl

theorem cell22_3592007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 3, 4].length) (baseStart_3592007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592007 prefixEnd_3592007 := by exact prefixLift 3592007
  have htrace : WordTrace (prefixWord ++ tailWord_3592007) baseStart_3592007 baseEnd_3592007 := by
    simpa [prefixWord, tailWord_3592007, baseEnd_3592007] using wordTrace_append hprefix tailTrace_3592007
  have hstable : (prefixWord ++ tailWord_3592007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592007).length < 2 ^ (prefixWord ++ tailWord_3592007).sum := by decide
  have hdescent : baseEnd_3592007 < baseStart_3592007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592080 : List Nat := [2, 1, 1, 1, 1, 1, 2, 8, 5]
def baseStart_3592080 : Nat := 118140960795 + 3592080 * 2 ^ 59
def prefixEnd_3592080 : Nat := 4983230072969 + 3 ^ 40 * 3592080 * 2
def baseEnd_3592080 : Nat := 409880797644980267595629

theorem tailTrace_3592080 : CollatzResearch.WordTrace tailWord_3592080 prefixEnd_3592080 409880797644980267595629 := by
  unfold tailWord_3592080
  simp only [CollatzResearch.WordTrace]
  refine ⟨65506960413257556633798847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87342613884343408845065129 65506960413257556633798847)
  ·
    refine ⟨98260440619886334950698271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65506960413257556633798847 98260440619886334950698271)
    ·
      refine ⟨147390660929829502426047407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98260440619886334950698271 147390660929829502426047407)
      ·
        refine ⟨221085991394744253639071111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147390660929829502426047407 221085991394744253639071111)
        ·
          refine ⟨331628987092116380458606667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221085991394744253639071111 331628987092116380458606667)
          ·
            refine ⟨497443480638174570687910001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331628987092116380458606667 497443480638174570687910001)
            ·
              refine ⟨373082610478630928015932501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497443480638174570687910001 373082610478630928015932501)
              ·
                refine ⟨4372061841546456187686709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 373082610478630928015932501 4372061841546456187686709)
                ·
                  refine ⟨409880797644980267595629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4372061841546456187686709 409880797644980267595629)
                  ·
                    rfl

theorem cell22_3592080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8, 5].length) (baseStart_3592080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592080 prefixEnd_3592080 := by exact prefixLift 3592080
  have htrace : WordTrace (prefixWord ++ tailWord_3592080) baseStart_3592080 baseEnd_3592080 := by
    simpa [prefixWord, tailWord_3592080, baseEnd_3592080] using wordTrace_append hprefix tailTrace_3592080
  have hstable : (prefixWord ++ tailWord_3592080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592080).length < 2 ^ (prefixWord ++ tailWord_3592080).sum := by decide
  have hdescent : baseEnd_3592080 < baseStart_3592080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592082 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3592082 : Nat := 118140960795 + 3592082 * 2 ^ 59
def prefixEnd_3592082 : Nat := 4983230072969 + 3 ^ 40 * 3592082 * 2
def baseEnd_3592082 : Nat := 1229643077575813464236881

theorem tailTrace_3592082 : CollatzResearch.WordTrace tailWord_3592082 prefixEnd_3592082 1229643077575813464236881 := by
  unfold tailWord_3592082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32753498443126966902292625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87342662515005245072780333 32753498443126966902292625)
  ·
    refine ⟨24565123832345225176719469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32753498443126966902292625 24565123832345225176719469)
    ·
      refine ⟨9211921437129459441269801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24565123832345225176719469 9211921437129459441269801)
      ·
        refine ⟨6908941077847094580952351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9211921437129459441269801 6908941077847094580952351)
        ·
          refine ⟨10363411616770641871428527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6908941077847094580952351 10363411616770641871428527)
          ·
            refine ⟨15545117425155962807142791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363411616770641871428527 15545117425155962807142791)
            ·
              refine ⟨23317676137733944210714187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15545117425155962807142791 23317676137733944210714187)
              ·
                refine ⟨34976514206600916316071281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23317676137733944210714187 34976514206600916316071281)
                ·
                  refine ⟨26232385654950687237053461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34976514206600916316071281 26232385654950687237053461)
                  ·
                    refine ⟨1229643077575813464236881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26232385654950687237053461 1229643077575813464236881)
                    ·
                      rfl

theorem cell22_3592082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3592082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592082 prefixEnd_3592082 := by exact prefixLift 3592082
  have htrace : WordTrace (prefixWord ++ tailWord_3592082) baseStart_3592082 baseEnd_3592082 := by
    simpa [prefixWord, tailWord_3592082, baseEnd_3592082] using wordTrace_append hprefix tailTrace_3592082
  have hstable : (prefixWord ++ tailWord_3592082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592082).length < 2 ^ (prefixWord ++ tailWord_3592082).sum := by decide
  have hdescent : baseEnd_3592082 < baseStart_3592082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592127 : List Nat := [1, 1, 2, 2, 2, 1, 5, 3, 1, 4]
def baseStart_3592127 : Nat := 118140960795 + 3592127 * 2 ^ 59
def prefixEnd_3592127 : Nat := 4983230072969 + 3 ^ 40 * 3592127 * 2
def baseEnd_3592127 : Nat := 1229658481995448346861743

theorem tailTrace_3592127 : CollatzResearch.WordTrace tailWord_3592127 prefixEnd_3592127 1229658481995448346861743 := by
  unfold tailWord_3592127
  simp only [CollatzResearch.WordTrace]
  refine ⟨131015635057344840294558635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87343756704896560196372423 131015635057344840294558635)
  ·
    refine ⟨196523452586017260441837953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131015635057344840294558635 196523452586017260441837953)
    ·
      refine ⟨147392589439512945331378465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196523452586017260441837953 147392589439512945331378465)
      ·
        refine ⟨110544442079634708998533849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147392589439512945331378465 110544442079634708998533849)
        ·
          refine ⟨82908331559726031748900387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110544442079634708998533849 82908331559726031748900387)
          ·
            refine ⟨124362497339589047623350581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82908331559726031748900387 124362497339589047623350581)
            ·
              refine ⟨11658984125586473214689117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124362497339589047623350581 11658984125586473214689117)
              ·
                refine ⟨4372119047094927455508419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11658984125586473214689117 4372119047094927455508419)
                ·
                  refine ⟨6558178570642391183262629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372119047094927455508419 6558178570642391183262629)
                  ·
                    refine ⟨1229658481995448346861743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6558178570642391183262629 1229658481995448346861743)
                    ·
                      rfl

theorem cell22_3592127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 4].length) (baseStart_3592127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592127 prefixEnd_3592127 := by exact prefixLift 3592127
  have htrace : WordTrace (prefixWord ++ tailWord_3592127) baseStart_3592127 baseEnd_3592127 := by
    simpa [prefixWord, tailWord_3592127, baseEnd_3592127] using wordTrace_append hprefix tailTrace_3592127
  have hstable : (prefixWord ++ tailWord_3592127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592127).length < 2 ^ (prefixWord ++ tailWord_3592127).sum := by decide
  have hdescent : baseEnd_3592127 < baseStart_3592127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592142 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_3592142 : Nat := 118140960795 + 3592142 * 2 ^ 59
def prefixEnd_3592142 : Nat := 4983230072969 + 3 ^ 40 * 3592142 * 2
def baseEnd_3592142 : Nat := 409887872267331102578899

theorem tailTrace_3592142 : CollatzResearch.WordTrace tailWord_3592142 prefixEnd_3592142 409887872267331102578899 := by
  unfold tailWord_3592142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377022769036312232044335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87344121434860331904236453 16377022769036312232044335)
  ·
    refine ⟨24565534153554468348066503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16377022769036312232044335 24565534153554468348066503)
    ·
      refine ⟨36848301230331702522099755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24565534153554468348066503 36848301230331702522099755)
      ·
        refine ⟨55272451845497553783149633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36848301230331702522099755 55272451845497553783149633)
        ·
          refine ⟨41454338884123165337362225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55272451845497553783149633 41454338884123165337362225)
          ·
            refine ⟨31090754163092374003021669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41454338884123165337362225 31090754163092374003021669)
            ·
              refine ⟨5829516405579820125566563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31090754163092374003021669 5829516405579820125566563)
              ·
                refine ⟨8744274608369730188349845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829516405579820125566563 8744274608369730188349845)
                ·
                  refine ⟨409887872267331102578899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8744274608369730188349845 409887872267331102578899)
                  ·
                    rfl

theorem cell22_3592142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_3592142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592142 prefixEnd_3592142 := by exact prefixLift 3592142
  have htrace : WordTrace (prefixWord ++ tailWord_3592142) baseStart_3592142 baseEnd_3592142 := by
    simpa [prefixWord, tailWord_3592142, baseEnd_3592142] using wordTrace_append hprefix tailTrace_3592142
  have hstable : (prefixWord ++ tailWord_3592142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592142).length < 2 ^ (prefixWord ++ tailWord_3592142).sum := by decide
  have hdescent : baseEnd_3592142 < baseStart_3592142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592174 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_3592174 : Nat := 118140960795 + 3592174 * 2 ^ 59
def prefixEnd_3592174 : Nat := 4983230072969 + 3 ^ 40 * 3592174 * 2
def baseEnd_3592174 : Nat := 1229674571055955890936599

theorem tailTrace_3592174 : CollatzResearch.WordTrace tailWord_3592174 prefixEnd_3592174 1229674571055955890936599 := by
  unfold tailWord_3592174
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377168661021820915189947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87344899525449711547679717 16377168661021820915189947)
  ·
    refine ⟨24565752991532731372784921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16377168661021820915189947 24565752991532731372784921)
    ·
      refine ⟨18424314743649548529588691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24565752991532731372784921 18424314743649548529588691)
      ·
        refine ⟨27636472115474322794383037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18424314743649548529588691 27636472115474322794383037)
        ·
          refine ⟨10363677043302871047893639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27636472115474322794383037 10363677043302871047893639)
          ·
            refine ⟨15545515564954306571840459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363677043302871047893639 15545515564954306571840459)
            ·
              refine ⟨23318273347431459857760689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15545515564954306571840459 23318273347431459857760689)
              ·
                refine ⟨17488705010573594893320517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23318273347431459857760689 17488705010573594893320517)
                ·
                  refine ⟨3279132189482549042497597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17488705010573594893320517 3279132189482549042497597)
                  ·
                    refine ⟨1229674571055955890936599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3279132189482549042497597 1229674571055955890936599)
                    ·
                      rfl

theorem cell22_3592174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_3592174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592174 prefixEnd_3592174 := by exact prefixLift 3592174
  have htrace : WordTrace (prefixWord ++ tailWord_3592174) baseStart_3592174 baseEnd_3592174 := by
    simpa [prefixWord, tailWord_3592174, baseEnd_3592174] using wordTrace_append hprefix tailTrace_3592174
  have hstable : (prefixWord ++ tailWord_3592174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592174).length < 2 ^ (prefixWord ++ tailWord_3592174).sum := by decide
  have hdescent : baseEnd_3592174 < baseStart_3592174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592277 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 8]
def baseStart_3592277 : Nat := 118140960795 + 3592277 * 2 ^ 59
def prefixEnd_3592277 : Nat := 4983230072969 + 3 ^ 40 * 3592277 * 2
def baseEnd_3592277 : Nat := 409903276686965985203761

theorem tailTrace_3592277 : CollatzResearch.WordTrace tailWord_3592277 prefixEnd_3592277 409903276686965985203761 := by
  unfold tailWord_3592277
  simp only [CollatzResearch.WordTrace]
  refine ⟨131021106006801415912519085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87347404004534277275012723 131021106006801415912519085)
  ·
    refine ⟨49132914752550530967194657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131021106006801415912519085 49132914752550530967194657)
    ·
      refine ⟨36849686064412898225395993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49132914752550530967194657 36849686064412898225395993)
      ·
        refine ⟨27637264548309673669046995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36849686064412898225395993 27637264548309673669046995)
        ·
          refine ⟨41455896822464510503570493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27637264548309673669046995 41455896822464510503570493)
          ·
            refine ⟨15545961308424191438838935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41455896822464510503570493 15545961308424191438838935)
            ·
              refine ⟨23318941962636287158258403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15545961308424191438838935 23318941962636287158258403)
              ·
                refine ⟨34978412943954430737387605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23318941962636287158258403 34978412943954430737387605)
                ·
                  refine ⟨409903276686965985203761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34978412943954430737387605 409903276686965985203761)
                  ·
                    rfl

theorem cell22_3592277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_3592277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592277 prefixEnd_3592277 := by exact prefixLift 3592277
  have htrace : WordTrace (prefixWord ++ tailWord_3592277) baseStart_3592277 baseEnd_3592277 := by
    simpa [prefixWord, tailWord_3592277, baseEnd_3592277] using wordTrace_append hprefix tailTrace_3592277
  have hstable : (prefixWord ++ tailWord_3592277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592277).length < 2 ^ (prefixWord ++ tailWord_3592277).sum := by decide
  have hdescent : baseEnd_3592277 < baseStart_3592277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592356 : List Nat := [2, 3, 1, 2, 5, 1, 8]
def baseStart_3592356 : Nat := 118140960795 + 3592356 * 2 ^ 59
def prefixEnd_3592356 : Nat := 4983230072969 + 3 ^ 40 * 3592356 * 2
def baseEnd_3592356 : Nat := 45545810125013632699483

theorem tailTrace_3592356 : CollatzResearch.WordTrace tailWord_3592356 prefixEnd_3592356 45545810125013632699483 := by
  unfold tailWord_3592356
  simp only [CollatzResearch.WordTrace]
  refine ⟨65511993686757606202322461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87349324915676808269763281 65511993686757606202322461)
  ·
    refine ⟨24566997632534102325870923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65511993686757606202322461 24566997632534102325870923)
    ·
      refine ⟨36850496448801153488806385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24566997632534102325870923 36850496448801153488806385)
      ·
        refine ⟨27637872336600865116604789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36850496448801153488806385 27637872336600865116604789)
        ·
          refine ⟨2591050531556331104681699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27637872336600865116604789 2591050531556331104681699)
          ·
            refine ⟨3886575797334496657022549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591050531556331104681699 3886575797334496657022549)
            ·
              refine ⟨45545810125013632699483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3886575797334496657022549 45545810125013632699483)
              ·
                rfl

theorem cell22_3592356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 8].length) (baseStart_3592356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592356 prefixEnd_3592356 := by exact prefixLift 3592356
  have htrace : WordTrace (prefixWord ++ tailWord_3592356) baseStart_3592356 baseEnd_3592356 := by
    simpa [prefixWord, tailWord_3592356, baseEnd_3592356] using wordTrace_append hprefix tailTrace_3592356
  have hstable : (prefixWord ++ tailWord_3592356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592356).length < 2 ^ (prefixWord ++ tailWord_3592356).sum := by decide
  have hdescent : baseEnd_3592356 < baseStart_3592356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592446 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_3592446 : Nat := 118140960795 + 3592446 * 2 ^ 59
def prefixEnd_3592446 : Nat := 4983230072969 + 3 ^ 40 * 3592446 * 2
def baseEnd_3592446 : Nat := 409922560738212616045255

theorem tailTrace_3592446 : CollatzResearch.WordTrace tailWord_3592446 prefixEnd_3592446 409922560738212616045255 := by
  unfold tailWord_3592446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378408742898644721927649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87351513295459438516947461 16378408742898644721927649)
  ·
    refine ⟨12283806557173983541445737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16378408742898644721927649 12283806557173983541445737)
    ·
      refine ⟨9212854917880487656084303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12283806557173983541445737 9212854917880487656084303)
      ·
        refine ⟨13819282376820731484126455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9212854917880487656084303 13819282376820731484126455)
        ·
          refine ⟨20728923565231097226189683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13819282376820731484126455 20728923565231097226189683)
          ·
            refine ⟨31093385347846645839284525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728923565231097226189683 31093385347846645839284525)
            ·
              refine ⟨11660019505442492189731697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31093385347846645839284525 11660019505442492189731697)
              ·
                refine ⟨8745014629081869142298773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11660019505442492189731697 8745014629081869142298773)
                ·
                  refine ⟨409922560738212616045255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8745014629081869142298773 409922560738212616045255)
                  ·
                    rfl

theorem cell22_3592446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_3592446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592446 prefixEnd_3592446 := by exact prefixLift 3592446
  have htrace : WordTrace (prefixWord ++ tailWord_3592446) baseStart_3592446 baseEnd_3592446 := by
    simpa [prefixWord, tailWord_3592446, baseEnd_3592446] using wordTrace_append hprefix tailTrace_3592446
  have hstable : (prefixWord ++ tailWord_3592446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592446).length < 2 ^ (prefixWord ++ tailWord_3592446).sum := by decide
  have hdescent : baseEnd_3592446 < baseStart_3592446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592459 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 1, 6]
def baseStart_3592459 : Nat := 118140960795 + 3592459 * 2 ^ 59
def prefixEnd_3592459 : Nat := 4983230072969 + 3 ^ 40 * 3592459 * 2
def baseEnd_3592459 : Nat := 1229772132380310147560725

theorem tailTrace_3592459 : CollatzResearch.WordTrace tailWord_3592459 prefixEnd_3592459 1229772132380310147560725 := by
  unfold tailWord_3592459
  simp only [CollatzResearch.WordTrace]
  refine ⟨131027744092142060995644431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87351829394761373997096287 131027744092142060995644431)
  ·
    refine ⟨196541616138213091493466647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131027744092142060995644431 196541616138213091493466647)
    ·
      refine ⟨294812424207319637240199971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196541616138213091493466647 294812424207319637240199971)
      ·
        refine ⟨442218636310979455860299957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294812424207319637240199971 442218636310979455860299957)
        ·
          refine ⟨41457997154154323986903121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 442218636310979455860299957 41457997154154323986903121)
          ·
            refine ⟨31093497865615742990177341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41457997154154323986903121 31093497865615742990177341)
            ·
              refine ⟨11660061699605903621316503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31093497865615742990177341 11660061699605903621316503)
              ·
                refine ⟨17490092549408855431974755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11660061699605903621316503 17490092549408855431974755)
                ·
                  refine ⟨26235138824113283147962133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17490092549408855431974755 26235138824113283147962133)
                  ·
                    refine ⟨1229772132380310147560725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26235138824113283147962133 1229772132380310147560725)
                    ·
                      rfl

theorem cell22_3592459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_3592459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592459 prefixEnd_3592459 := by exact prefixLift 3592459
  have htrace : WordTrace (prefixWord ++ tailWord_3592459) baseStart_3592459 baseEnd_3592459 := by
    simpa [prefixWord, tailWord_3592459, baseEnd_3592459] using wordTrace_append hprefix tailTrace_3592459
  have hstable : (prefixWord ++ tailWord_3592459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592459).length < 2 ^ (prefixWord ++ tailWord_3592459).sum := by decide
  have hdescent : baseEnd_3592459 < baseStart_3592459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592504 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 2, 6]
def baseStart_3592504 : Nat := 118140960795 + 3592504 * 2 ^ 59
def prefixEnd_3592504 : Nat := 4983230072969 + 3 ^ 40 * 3592504 * 2
def baseEnd_3592504 : Nat := 1229787536799945030185587

theorem tailTrace_3592504 : CollatzResearch.WordTrace tailWord_3592504 prefixEnd_3592504 1229787536799945030185587 := by
  unfold tailWord_3592504
  simp only [CollatzResearch.WordTrace]
  refine ⟨65514692688489516840516283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87352923584652689120688377 65514692688489516840516283)
  ·
    refine ⟨98272039032734275260774425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65514692688489516840516283 98272039032734275260774425)
    ·
      refine ⟨73704029274550706445580819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98272039032734275260774425 73704029274550706445580819)
      ·
        refine ⟨110556043911826059668371229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73704029274550706445580819 110556043911826059668371229)
        ·
          refine ⟨41458516466934772375639211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110556043911826059668371229 41458516466934772375639211)
          ·
            refine ⟨62187774700402158563458817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41458516466934772375639211 62187774700402158563458817)
            ·
              refine ⟨46640831025301618922594113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62187774700402158563458817 46640831025301618922594113)
              ·
                refine ⟨34980623268976214191945585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46640831025301618922594113 34980623268976214191945585)
                ·
                  refine ⟨26235467451732160643959189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34980623268976214191945585 26235467451732160643959189)
                  ·
                    refine ⟨1229787536799945030185587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26235467451732160643959189 1229787536799945030185587)
                    ·
                      rfl

theorem cell22_3592504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_3592504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592504 prefixEnd_3592504 := by exact prefixLift 3592504
  have htrace : WordTrace (prefixWord ++ tailWord_3592504) baseStart_3592504 baseEnd_3592504 := by
    simpa [prefixWord, tailWord_3592504, baseEnd_3592504] using wordTrace_append hprefix tailTrace_3592504
  have hstable : (prefixWord ++ tailWord_3592504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592504).length < 2 ^ (prefixWord ++ tailWord_3592504).sum := by decide
  have hdescent : baseEnd_3592504 < baseStart_3592504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592519 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 9]
def baseStart_3592519 : Nat := 118140960795 + 3592519 * 2 ^ 59
def prefixEnd_3592519 : Nat := 4983230072969 + 3 ^ 40 * 3592519 * 2
def baseEnd_3592519 : Nat := 409930890535496663686847

theorem tailTrace_3592519 : CollatzResearch.WordTrace tailWord_3592519 prefixEnd_3592519 409930890535496663686847 := by
  unfold tailWord_3592519
  simp only [CollatzResearch.WordTrace]
  refine ⟨131029932471924691242828611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87353288314616460828552407 131029932471924691242828611)
  ·
    refine ⟨196544898707887036864242917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131029932471924691242828611 196544898707887036864242917)
    ·
      refine ⟨36852168507728819412045547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196544898707887036864242917 36852168507728819412045547)
      ·
        refine ⟨55278252761593229118068321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36852168507728819412045547 55278252761593229118068321)
        ·
          refine ⟨41458689571194921838551241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55278252761593229118068321 41458689571194921838551241)
          ·
            refine ⟨31094017178396191378913431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41458689571194921838551241 31094017178396191378913431)
            ·
              refine ⟨46641025767594287068370147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31094017178396191378913431 46641025767594287068370147)
              ·
                refine ⟨69961538651391430602555221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46641025767594287068370147 69961538651391430602555221)
                ·
                  refine ⟨409930890535496663686847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69961538651391430602555221 409930890535496663686847)
                  ·
                    rfl

theorem cell22_3592519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 9].length) (baseStart_3592519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592519 prefixEnd_3592519 := by exact prefixLift 3592519
  have htrace : WordTrace (prefixWord ++ tailWord_3592519) baseStart_3592519 baseEnd_3592519 := by
    simpa [prefixWord, tailWord_3592519, baseEnd_3592519] using wordTrace_append hprefix tailTrace_3592519
  have hstable : (prefixWord ++ tailWord_3592519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592519).length < 2 ^ (prefixWord ++ tailWord_3592519).sum := by decide
  have hdescent : baseEnd_3592519 < baseStart_3592519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592523 : List Nat := [1, 1, 1, 1, 3, 1, 1, 9, 1, 3]
def baseStart_3592523 : Nat := 118140960795 + 3592523 * 2 ^ 59
def prefixEnd_3592523 : Nat := 4983230072969 + 3 ^ 40 * 3592523 * 2
def baseEnd_3592523 : Nat := 1229794040888235313960529

theorem tailTrace_3592523 : CollatzResearch.WordTrace tailWord_3592523 prefixEnd_3592523 1229794040888235313960529 := by
  unfold tailWord_3592523
  simp only [CollatzResearch.WordTrace]
  refine ⟨131030078363910199925974223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87353385575940133283982815 131030078363910199925974223)
  ·
    refine ⟨196545117545865299888961335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131030078363910199925974223 196545117545865299888961335)
    ·
      refine ⟨294817676318797949833442003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196545117545865299888961335 294817676318797949833442003)
      ·
        refine ⟨442226514478196924750163005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294817676318797949833442003 442226514478196924750163005)
        ·
          refine ⟨165834942929323846781311127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442226514478196924750163005 165834942929323846781311127)
          ·
            refine ⟨248752414393985770171966691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165834942929323846781311127 248752414393985770171966691)
            ·
              refine ⟨373128621590978655257950037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248752414393985770171966691 373128621590978655257950037)
              ·
                refine ⟨2186300517134640558152051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 373128621590978655257950037 2186300517134640558152051)
                ·
                  refine ⟨3279450775701960837228077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186300517134640558152051 3279450775701960837228077)
                  ·
                    refine ⟨1229794040888235313960529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3279450775701960837228077 1229794040888235313960529)
                    ·
                      rfl

theorem cell22_3592523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 3].length) (baseStart_3592523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592523 prefixEnd_3592523 := by exact prefixLift 3592523
  have htrace : WordTrace (prefixWord ++ tailWord_3592523) baseStart_3592523 baseEnd_3592523 := by
    simpa [prefixWord, tailWord_3592523, baseEnd_3592523] using wordTrace_append hprefix tailTrace_3592523
  have hstable : (prefixWord ++ tailWord_3592523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592523).length < 2 ^ (prefixWord ++ tailWord_3592523).sum := by decide
  have hdescent : baseEnd_3592523 < baseStart_3592523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592613 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_3592613 : Nat := 118140960795 + 3592613 * 2 ^ 59
def prefixEnd_3592613 : Nat := 4983230072969 + 3 ^ 40 * 3592613 * 2
def baseEnd_3592613 : Nat := 1229824849727505079210253

theorem tailTrace_3592613 : CollatzResearch.WordTrace tailWord_3592613 prefixEnd_3592613 1229824849727505079210253 := by
  unfold tailWord_3592613
  simp only [CollatzResearch.WordTrace]
  refine ⟨131033360933584145296750493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87355573955722763531166995 131033360933584145296750493)
  ·
    refine ⟨49137510350094054486281435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131033360933584145296750493 49137510350094054486281435)
    ·
      refine ⟨73706265525141081729422153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49137510350094054486281435 73706265525141081729422153)
      ·
        refine ⟨55279699143855811297066615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73706265525141081729422153 55279699143855811297066615)
        ·
          refine ⟨82919548715783716945599923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55279699143855811297066615 82919548715783716945599923)
          ·
            refine ⟨124379323073675575418399885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82919548715783716945599923 124379323073675575418399885)
            ·
              refine ⟨46642246152628340781899957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124379323073675575418399885 46642246152628340781899957)
              ·
                refine ⟨4372710576808906948303121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46642246152628340781899957 4372710576808906948303121)
                ·
                  refine ⟨3279532932606680211227341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4372710576808906948303121 3279532932606680211227341)
                  ·
                    refine ⟨1229824849727505079210253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3279532932606680211227341 1229824849727505079210253)
                    ·
                      rfl

theorem cell22_3592613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_3592613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592613 prefixEnd_3592613 := by exact prefixLift 3592613
  have htrace : WordTrace (prefixWord ++ tailWord_3592613) baseStart_3592613 baseEnd_3592613 := by
    simpa [prefixWord, tailWord_3592613, baseEnd_3592613] using wordTrace_append hprefix tailTrace_3592613
  have hstable : (prefixWord ++ tailWord_3592613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592613).length < 2 ^ (prefixWord ++ tailWord_3592613).sum := by decide
  have hdescent : baseEnd_3592613 < baseStart_3592613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592677 : List Nat := [1, 3, 1, 5, 3, 1, 2, 6]
def baseStart_3592677 : Nat := 118140960795 + 3592677 * 2 ^ 59
def prefixEnd_3592677 : Nat := 4983230072969 + 3 ^ 40 * 3592677 * 2
def baseEnd_3592677 : Nat := 136649639803936693956673

theorem tailTrace_3592677 : CollatzResearch.WordTrace tailWord_3592677 prefixEnd_3592677 136649639803936693956673 := by
  unfold tailWord_3592677
  simp only [CollatzResearch.WordTrace]
  refine ⟨131035695205352284227080285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87357130136901522818053523 131035695205352284227080285)
  ·
    refine ⟨49138385702007106585155107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131035695205352284227080285 49138385702007106585155107)
    ·
      refine ⟨73707578553010659877732661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49138385702007106585155107 73707578553010659877732661)
      ·
        refine ⟨6910085489344749363537437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73707578553010659877732661 6910085489344749363537437)
        ·
          refine ⟨2591282058504281011326539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6910085489344749363537437 2591282058504281011326539)
          ·
            refine ⟨3886923087756421516989809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591282058504281011326539 3886923087756421516989809)
            ·
              refine ⟨2915192315817316137742357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3886923087756421516989809 2915192315817316137742357)
              ·
                refine ⟨136649639803936693956673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2915192315817316137742357 136649639803936693956673)
                ·
                  rfl

theorem cell22_3592677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 6].length) (baseStart_3592677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592677 prefixEnd_3592677 := by exact prefixLift 3592677
  have htrace : WordTrace (prefixWord ++ tailWord_3592677) baseStart_3592677 baseEnd_3592677 := by
    simpa [prefixWord, tailWord_3592677, baseEnd_3592677] using wordTrace_append hprefix tailTrace_3592677
  have hstable : (prefixWord ++ tailWord_3592677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592677).length < 2 ^ (prefixWord ++ tailWord_3592677).sum := by decide
  have hdescent : baseEnd_3592677 < baseStart_3592677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592731 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 7, 5]
def baseStart_3592731 : Nat := 118140960795 + 3592731 * 2 ^ 59
def prefixEnd_3592731 : Nat := 4983230072969 + 3 ^ 40 * 3592731 * 2
def baseEnd_3592731 : Nat := 1229865243538992104759891

theorem tailTrace_3592731 : CollatzResearch.WordTrace tailWord_3592731 prefixEnd_3592731 1229865243538992104759891 := by
  unfold tailWord_3592731
  simp only [CollatzResearch.WordTrace]
  refine ⟨131037664747156651449546047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87358443164771100966364031 131037664747156651449546047)
  ·
    refine ⟨196556497120734977174319071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131037664747156651449546047 196556497120734977174319071)
    ·
      refine ⟨294834745681102465761478607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196556497120734977174319071 294834745681102465761478607)
      ·
        refine ⟨442252118521653698642217911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294834745681102465761478607 442252118521653698642217911)
        ·
          refine ⟨663378177782480547963326867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442252118521653698642217911 663378177782480547963326867)
          ·
            refine ⟨995067266673720821944990301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663378177782480547963326867 995067266673720821944990301)
            ·
              refine ⟨373150225002645308229371363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 995067266673720821944990301 373150225002645308229371363)
              ·
                refine ⟨559725337503967962344057045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373150225002645308229371363 559725337503967962344057045)
                ·
                  refine ⟨13118562597749249117438837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 559725337503967962344057045 13118562597749249117438837)
                  ·
                    refine ⟨1229865243538992104759891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13118562597749249117438837 1229865243538992104759891)
                    ·
                      rfl

theorem cell22_3592731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_3592731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592731 prefixEnd_3592731 := by exact prefixLift 3592731
  have htrace : WordTrace (prefixWord ++ tailWord_3592731) baseStart_3592731 baseEnd_3592731 := by
    simpa [prefixWord, tailWord_3592731, baseEnd_3592731] using wordTrace_append hprefix tailTrace_3592731
  have hstable : (prefixWord ++ tailWord_3592731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592731).length < 2 ^ (prefixWord ++ tailWord_3592731).sum := by decide
  have hdescent : baseEnd_3592731 < baseStart_3592731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592748 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 6, 3]
def baseStart_3592748 : Nat := 118140960795 + 3592748 * 2 ^ 59
def prefixEnd_3592748 : Nat := 4983230072969 + 3 ^ 40 * 3592748 * 2
def baseEnd_3592748 : Nat := 1229871062986409727084839

theorem tailTrace_3592748 : CollatzResearch.WordTrace tailWord_3592748 prefixEnd_3592748 1229871062986409727084839 := by
  unfold tailWord_3592748
  simp only [CollatzResearch.WordTrace]
  refine ⟨65519142394047531676457449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87358856525396708901943265 65519142394047531676457449)
  ·
    refine ⟨49139356795535648757343087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65519142394047531676457449 49139356795535648757343087)
    ·
      refine ⟨73709035193303473136014631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49139356795535648757343087 73709035193303473136014631)
      ·
        refine ⟨110563552789955209704021947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73709035193303473136014631 110563552789955209704021947)
        ·
          refine ⟨165845329184932814556032921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110563552789955209704021947 165845329184932814556032921)
          ·
            refine ⟨124383996888699610917024691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165845329184932814556032921 124383996888699610917024691)
            ·
              refine ⟨186575995333049416375537037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124383996888699610917024691 186575995333049416375537037)
              ·
                refine ⟨69965998249893531140826389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186575995333049416375537037 69965998249893531140826389)
                ·
                  refine ⟨3279656167963759272226237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69965998249893531140826389 3279656167963759272226237)
                  ·
                    refine ⟨1229871062986409727084839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3279656167963759272226237 1229871062986409727084839)
                    ·
                      rfl

theorem cell22_3592748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_3592748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592748 prefixEnd_3592748 := by exact prefixLift 3592748
  have htrace : WordTrace (prefixWord ++ tailWord_3592748) baseStart_3592748 baseEnd_3592748 := by
    simpa [prefixWord, tailWord_3592748, baseEnd_3592748] using wordTrace_append hprefix tailTrace_3592748
  have hstable : (prefixWord ++ tailWord_3592748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592748).length < 2 ^ (prefixWord ++ tailWord_3592748).sum := by decide
  have hdescent : baseEnd_3592748 < baseStart_3592748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592778 : List Nat := [3, 1, 2, 1, 1, 4, 3, 7]
def baseStart_3592778 : Nat := 118140960795 + 3592778 * 2 ^ 59
def prefixEnd_3592778 : Nat := 4983230072969 + 3 ^ 40 * 3592778 * 2
def baseEnd_3592778 : Nat := 136653481399944405426083

theorem tailTrace_3592778 : CollatzResearch.WordTrace tailWord_3592778 prefixEnd_3592778 136653481399944405426083 := by
  unfold tailWord_3592778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32759844744496594619126747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87359585985324252317671325 32759844744496594619126747)
  ·
    refine ⟨49139767116744891928690121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32759844744496594619126747 49139767116744891928690121)
    ·
      refine ⟨36854825337558668946517591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49139767116744891928690121 36854825337558668946517591)
      ·
        refine ⟨55282238006338003419776387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36854825337558668946517591 55282238006338003419776387)
        ·
          refine ⟨82923357009507005129664581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55282238006338003419776387 82923357009507005129664581)
          ·
            refine ⟨15548129439282563461812109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82923357009507005129664581 15548129439282563461812109)
            ·
              refine ⟨5830548539730961298179541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15548129439282563461812109 5830548539730961298179541)
              ·
                refine ⟨136653481399944405426083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5830548539730961298179541 136653481399944405426083)
                ·
                  rfl

theorem cell22_3592778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_3592778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592778 prefixEnd_3592778 := by exact prefixLift 3592778
  have htrace : WordTrace (prefixWord ++ tailWord_3592778) baseStart_3592778 baseEnd_3592778 := by
    simpa [prefixWord, tailWord_3592778, baseEnd_3592778] using wordTrace_append hprefix tailTrace_3592778
  have hstable : (prefixWord ++ tailWord_3592778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592778).length < 2 ^ (prefixWord ++ tailWord_3592778).sum := by decide
  have hdescent : baseEnd_3592778 < baseStart_3592778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592810 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_3592810 : Nat := 118140960795 + 3592810 * 2 ^ 59
def prefixEnd_3592810 : Nat := 4983230072969 + 3 ^ 40 * 3592810 * 2
def baseEnd_3592810 : Nat := 1229892286853462232034649

theorem tailTrace_3592810 : CollatzResearch.WordTrace tailWord_3592810 prefixEnd_3592810 1229892286853462232034649 := by
  unfold tailWord_3592810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32760136528467611985417971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87360364075913631961114589 32760136528467611985417971)
  ·
    refine ⟨49140204792701417978126957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32760136528467611985417971 49140204792701417978126957)
    ·
      refine ⟨18427576797263031741797609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49140204792701417978126957 18427576797263031741797609)
      ·
        refine ⟨13820682597947273806348207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18427576797263031741797609 13820682597947273806348207)
        ·
          refine ⟨20731023896920910709522311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13820682597947273806348207 20731023896920910709522311)
          ·
            refine ⟨31096535845381366064283467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20731023896920910709522311 31096535845381366064283467)
            ·
              refine ⟨46644803768072049096425201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31096535845381366064283467 46644803768072049096425201)
              ·
                refine ⟨34983602826054036822318901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46644803768072049096425201 34983602826054036822318901)
                ·
                  refine ⟨3279712764942565952092397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34983602826054036822318901 3279712764942565952092397)
                  ·
                    refine ⟨1229892286853462232034649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3279712764942565952092397 1229892286853462232034649)
                    ·
                      rfl

theorem cell22_3592810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_3592810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592810 prefixEnd_3592810 := by exact prefixLift 3592810
  have htrace : WordTrace (prefixWord ++ tailWord_3592810) baseStart_3592810 baseEnd_3592810 := by
    simpa [prefixWord, tailWord_3592810, baseEnd_3592810] using wordTrace_append hprefix tailTrace_3592810
  have hstable : (prefixWord ++ tailWord_3592810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592810).length < 2 ^ (prefixWord ++ tailWord_3592810).sum := by decide
  have hdescent : baseEnd_3592810 < baseStart_3592810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592878 : List Nat := [4, 1, 4, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3592878 : Nat := 118140960795 + 3592878 * 2 ^ 59
def prefixEnd_3592878 : Nat := 4983230072969 + 3 ^ 40 * 3592878 * 2
def baseEnd_3592878 : Nat := 1229915564643132721334441

theorem tailTrace_3592878 : CollatzResearch.WordTrace tailWord_3592878 prefixEnd_3592878 1229915564643132721334441 := by
  unfold tailWord_3592878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16380378284703011944393411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87362017518416063703431525 16380378284703011944393411)
  ·
    refine ⟨24570567427054517916590117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16380378284703011944393411 24570567427054517916590117)
    ·
      refine ⟨4606981392572722109360647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24570567427054517916590117 4606981392572722109360647)
      ·
        refine ⟨6910472088859083164040971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606981392572722109360647 6910472088859083164040971)
        ·
          refine ⟨10365708133288624746061457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6910472088859083164040971 10365708133288624746061457)
          ·
            refine ⟨7774281099966468559546093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10365708133288624746061457 7774281099966468559546093)
            ·
              refine ⟨2915355412487425709829785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7774281099966468559546093 2915355412487425709829785)
              ·
                refine ⟨2186516559365569282372339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915355412487425709829785 2186516559365569282372339)
                ·
                  refine ⟨3279774839048353923558509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186516559365569282372339 3279774839048353923558509)
                  ·
                    refine ⟨1229915564643132721334441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3279774839048353923558509 1229915564643132721334441)
                    ·
                      rfl

theorem cell22_3592878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3592878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592878 prefixEnd_3592878 := by exact prefixLift 3592878
  have htrace : WordTrace (prefixWord ++ tailWord_3592878) baseStart_3592878 baseEnd_3592878 := by
    simpa [prefixWord, tailWord_3592878, baseEnd_3592878] using wordTrace_append hprefix tailTrace_3592878
  have hstable : (prefixWord ++ tailWord_3592878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592878).length < 2 ^ (prefixWord ++ tailWord_3592878).sum := by decide
  have hdescent : baseEnd_3592878 < baseStart_3592878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592913 : List Nat := [1, 2, 2, 1, 2, 3, 1, 10]
def baseStart_3592913 : Nat := 118140960795 + 3592913 * 2 ^ 59
def prefixEnd_3592913 : Nat := 4983230072969 + 3 ^ 40 * 3592913 * 2
def baseEnd_3592913 : Nat := 136658616206489366301037

theorem tailTrace_3592913 : CollatzResearch.WordTrace tailWord_3592913 prefixEnd_3592913 136658616206489366301037 := by
  unfold tailWord_3592913
  simp only [CollatzResearch.WordTrace]
  refine ⟨131044302832497296532671393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87362868554998197688447595 131044302832497296532671393)
  ·
    refine ⟨98283227124372972399503545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131044302832497296532671393 98283227124372972399503545)
    ·
      refine ⟨73712420343279729299627659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98283227124372972399503545 73712420343279729299627659)
      ·
        refine ⟨110568630514919593949441489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73712420343279729299627659 110568630514919593949441489)
        ·
          refine ⟨82926472886189695462081117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110568630514919593949441489 82926472886189695462081117)
          ·
            refine ⟨31097427332321135798280419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82926472886189695462081117 31097427332321135798280419)
            ·
              refine ⟨46646140998481703697420629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31097427332321135798280419 46646140998481703697420629)
              ·
                refine ⟨136658616206489366301037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46646140998481703697420629 136658616206489366301037)
                ·
                  rfl

theorem cell22_3592913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 10].length) (baseStart_3592913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592913 prefixEnd_3592913 := by exact prefixLift 3592913
  have htrace : WordTrace (prefixWord ++ tailWord_3592913) baseStart_3592913 baseEnd_3592913 := by
    simpa [prefixWord, tailWord_3592913, baseEnd_3592913] using wordTrace_append hprefix tailTrace_3592913
  have hstable : (prefixWord ++ tailWord_3592913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592913).length < 2 ^ (prefixWord ++ tailWord_3592913).sum := by decide
  have hdescent : baseEnd_3592913 < baseStart_3592913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592936 : List Nat := [2, 1, 4, 1, 4, 2, 2, 2, 4]
def baseStart_3592936 : Nat := 118140960795 + 3592936 * 2 ^ 59
def prefixEnd_3592936 : Nat := 4983230072969 + 3 ^ 40 * 3592936 * 2
def baseEnd_3592936 : Nat := 409978473076146634461421

theorem tailTrace_3592936 : CollatzResearch.WordTrace tailWord_3592936 prefixEnd_3592936 409978473076146634461421 := by
  unfold tailWord_3592936
  simp only [CollatzResearch.WordTrace]
  refine ⟨65522570855706985730379331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87363427807609314307172441 65522570855706985730379331)
  ·
    refine ⟨98283856283560478595568997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65522570855706985730379331 98283856283560478595568997)
    ·
      refine ⟨18428223053167589736669187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98283856283560478595568997 18428223053167589736669187)
      ·
        refine ⟨27642334579751384605003781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18428223053167589736669187 27642334579751384605003781)
        ·
          refine ⟨5182937733703384613438209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27642334579751384605003781 5182937733703384613438209)
          ·
            refine ⟨3887203300277538460078657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5182937733703384613438209 3887203300277538460078657)
            ·
              refine ⟨2915402475208153845058993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887203300277538460078657 2915402475208153845058993)
              ·
                refine ⟨2186551856406115383794245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915402475208153845058993 2186551856406115383794245)
                ·
                  refine ⟨409978473076146634461421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2186551856406115383794245 409978473076146634461421)
                  ·
                    rfl

theorem cell22_3592936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 4].length) (baseStart_3592936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592936 prefixEnd_3592936 := by exact prefixLift 3592936
  have htrace : WordTrace (prefixWord ++ tailWord_3592936) baseStart_3592936 baseEnd_3592936 := by
    simpa [prefixWord, tailWord_3592936, baseEnd_3592936] using wordTrace_append hprefix tailTrace_3592936
  have hstable : (prefixWord ++ tailWord_3592936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592936).length < 2 ^ (prefixWord ++ tailWord_3592936).sum := by decide
  have hdescent : baseEnd_3592936 < baseStart_3592936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592979 : List Nat := [1, 1, 1, 2, 1, 3, 6, 3, 1, 3]
def baseStart_3592979 : Nat := 118140960795 + 3592979 * 2 ^ 59
def prefixEnd_3592979 : Nat := 4983230072969 + 3 ^ 40 * 3592979 * 2
def baseEnd_3592979 : Nat := 1229950139007202124559131

theorem tailTrace_3592979 : CollatzResearch.WordTrace tailWord_3592979 prefixEnd_3592979 1229950139007202124559131 := by
  unfold tailWord_3592979
  simp only [CollatzResearch.WordTrace]
  refine ⟨131046710050258189804573991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87364473366838793203049327 131046710050258189804573991)
  ·
    refine ⟨196570065075387284706860987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131046710050258189804573991 196570065075387284706860987)
    ·
      refine ⟨294855097613080927060291481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196570065075387284706860987 294855097613080927060291481)
      ·
        refine ⟨221141323209810695295218611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294855097613080927060291481 221141323209810695295218611)
        ·
          refine ⟨331711984814716042942827917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221141323209810695295218611 331711984814716042942827917)
          ·
            refine ⟨124391994305518516103560469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331711984814716042942827917 124391994305518516103560469)
            ·
              refine ⟨5830874733071180442354397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124391994305518516103560469 5830874733071180442354397)
              ·
                refine ⟨2186578024901692665882899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5830874733071180442354397 2186578024901692665882899)
                ·
                  refine ⟨3279867037352538998824349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186578024901692665882899 3279867037352538998824349)
                  ·
                    refine ⟨1229950139007202124559131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3279867037352538998824349 1229950139007202124559131)
                    ·
                      rfl

theorem cell22_3592979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 1, 3].length) (baseStart_3592979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592979 prefixEnd_3592979 := by exact prefixLift 3592979
  have htrace : WordTrace (prefixWord ++ tailWord_3592979) baseStart_3592979 baseEnd_3592979 := by
    simpa [prefixWord, tailWord_3592979, baseEnd_3592979] using wordTrace_append hprefix tailTrace_3592979
  have hstable : (prefixWord ++ tailWord_3592979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592979).length < 2 ^ (prefixWord ++ tailWord_3592979).sum := by decide
  have hdescent : baseEnd_3592979 < baseStart_3592979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3592992 : List Nat := [2, 1, 1, 5, 1, 2, 3, 2, 5]
def baseStart_3592992 : Nat := 118140960795 + 3592992 * 2 ^ 59
def prefixEnd_3592992 : Nat := 4983230072969 + 3 ^ 40 * 3592992 * 2
def baseEnd_3592992 : Nat := 409984863057624807994697

theorem tailTrace_3592992 : CollatzResearch.WordTrace tailWord_3592992 prefixEnd_3592992 409984863057624807994697 := by
  unfold tailWord_3592992
  simp only [CollatzResearch.WordTrace]
  refine ⟨65523592099605546512398615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87364789466140728683198153 65523592099605546512398615)
  ·
    refine ⟨98285388149408319768597923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65523592099605546512398615 98285388149408319768597923)
    ·
      refine ⟨147428082224112479652896885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98285388149408319768597923 147428082224112479652896885)
      ·
        refine ⟨13821382708510544967459083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147428082224112479652896885 13821382708510544967459083)
        ·
          refine ⟨20732074062765817451188625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13821382708510544967459083 20732074062765817451188625)
          ·
            refine ⟨15549055547074363088391469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20732074062765817451188625 15549055547074363088391469)
            ·
              refine ⟨5830895830152886158146801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15549055547074363088391469 5830895830152886158146801)
              ·
                refine ⟨4373171872614664618610101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5830895830152886158146801 4373171872614664618610101)
                ·
                  refine ⟨409984863057624807994697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4373171872614664618610101 409984863057624807994697)
                  ·
                    rfl

theorem cell22_3592992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 5].length) (baseStart_3592992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3592992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3592992 prefixEnd_3592992 := by exact prefixLift 3592992
  have htrace : WordTrace (prefixWord ++ tailWord_3592992) baseStart_3592992 baseEnd_3592992 := by
    simpa [prefixWord, tailWord_3592992, baseEnd_3592992] using wordTrace_append hprefix tailTrace_3592992
  have hstable : (prefixWord ++ tailWord_3592992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3592992).length < 2 ^ (prefixWord ++ tailWord_3592992).sum := by decide
  have hdescent : baseEnd_3592992 < baseStart_3592992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3592992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593086 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3593086 : Nat := 118140960795 + 3593086 * 2 ^ 59
def prefixEnd_3593086 : Nat := 4983230072969 + 3 ^ 40 * 3593086 * 2
def baseEnd_3593086 : Nat := 1229986767293889512133803

theorem tailTrace_3593086 : CollatzResearch.WordTrace tailWord_3593086 prefixEnd_3593086 1229986767293889512133803 := by
  unfold tailWord_3593086
  simp only [CollatzResearch.WordTrace]
  refine ⟨16381326582608818384839889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87367075107247031385812741 16381326582608818384839889)
  ·
    refine ⟨12285994936956613788629917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16381326582608818384839889 12285994936956613788629917)
    ·
      refine ⟨4607248101358730170736219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12285994936956613788629917 4607248101358730170736219)
      ·
        refine ⟨6910872152038095256104329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4607248101358730170736219 6910872152038095256104329)
        ·
          refine ⟨5183154114028571442078247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6910872152038095256104329 5183154114028571442078247)
          ·
            refine ⟨7774731171042857163117371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183154114028571442078247 7774731171042857163117371)
            ·
              refine ⟨11662096756564285744676057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774731171042857163117371 11662096756564285744676057)
              ·
                refine ⟨8746572567423214308507043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11662096756564285744676057 8746572567423214308507043)
                ·
                  refine ⟨13119858851134821462760565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8746572567423214308507043 13119858851134821462760565)
                  ·
                    refine ⟨1229986767293889512133803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13119858851134821462760565 1229986767293889512133803)
                    ·
                      rfl

theorem cell22_3593086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3593086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593086 prefixEnd_3593086 := by exact prefixLift 3593086
  have htrace : WordTrace (prefixWord ++ tailWord_3593086) baseStart_3593086 baseEnd_3593086 := by
    simpa [prefixWord, tailWord_3593086, baseEnd_3593086] using wordTrace_append hprefix tailTrace_3593086
  have hstable : (prefixWord ++ tailWord_3593086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593086).length < 2 ^ (prefixWord ++ tailWord_3593086).sum := by decide
  have hdescent : baseEnd_3593086 < baseStart_3593086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593090 : List Nat := [3, 4, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3593090 : Nat := 118140960795 + 3593090 * 2 ^ 59
def prefixEnd_3593090 : Nat := 4983230072969 + 3 ^ 40 * 3593090 * 2
def baseEnd_3593090 : Nat := 1229988136575634835033791

theorem tailTrace_3593090 : CollatzResearch.WordTrace tailWord_3593090 prefixEnd_3593090 1229988136575634835033791 := by
  unfold tailWord_3593090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32762689638214013940466181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87367172368570703841243149 32762689638214013940466181)
  ·
    refine ⟨6143004307165127613837409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32762689638214013940466181 6143004307165127613837409)
    ·
      refine ⟨4607253230373845710378057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6143004307165127613837409 4607253230373845710378057)
      ·
        refine ⟨3455439922780384282783543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4607253230373845710378057 3455439922780384282783543)
        ·
          refine ⟨5183159884170576424175315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3455439922780384282783543 5183159884170576424175315)
          ·
            refine ⟨7774739826255864636262973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5183159884170576424175315 7774739826255864636262973)
            ·
              refine ⟨2915527434845949238598615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7774739826255864636262973 2915527434845949238598615)
              ·
                refine ⟨4373291152268923857897923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2915527434845949238598615 4373291152268923857897923)
                ·
                  refine ⟨6559936728403385786846885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373291152268923857897923 6559936728403385786846885)
                  ·
                    refine ⟨1229988136575634835033791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6559936728403385786846885 1229988136575634835033791)
                    ·
                      rfl

theorem cell22_3593090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3593090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593090 prefixEnd_3593090 := by exact prefixLift 3593090
  have htrace : WordTrace (prefixWord ++ tailWord_3593090) baseStart_3593090 baseEnd_3593090 := by
    simpa [prefixWord, tailWord_3593090, baseEnd_3593090] using wordTrace_append hprefix tailTrace_3593090
  have hstable : (prefixWord ++ tailWord_3593090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593090).length < 2 ^ (prefixWord ++ tailWord_3593090).sum := by decide
  have hdescent : baseEnd_3593090 < baseStart_3593090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593116 : List Nat := [2, 2, 3, 3, 3, 1, 1, 7]
def baseStart_3593116 : Nat := 118140960795 + 3593116 * 2 ^ 59
def prefixEnd_3593116 : Nat := 4983230072969 + 3 ^ 40 * 3593116 * 2
def baseEnd_3593116 : Nat := 136666337434108825987079

theorem tailTrace_3593116 : CollatzResearch.WordTrace tailWord_3593116 prefixEnd_3593116 136666337434108825987079 := by
  unfold tailWord_3593116
  simp only [CollatzResearch.WordTrace]
  refine ⟨65525853425380931101155601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87367804567174574801540801 65525853425380931101155601)
  ·
    refine ⟨49144390069035698325866701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65525853425380931101155601 49144390069035698325866701)
    ·
      refine ⟨18429146275888386872200013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49144390069035698325866701 18429146275888386872200013)
      ·
        refine ⟨6910929853458145077075005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18429146275888386872200013 6910929853458145077075005)
        ·
          refine ⟨2591598695046804403903127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6910929853458145077075005 2591598695046804403903127)
          ·
            refine ⟨3887398042570206605854691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2591598695046804403903127 3887398042570206605854691)
            ·
              refine ⟨5831097063855309908782037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887398042570206605854691 5831097063855309908782037)
              ·
                refine ⟨136666337434108825987079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5831097063855309908782037 136666337434108825987079)
                ·
                  rfl

theorem cell22_3593116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 7].length) (baseStart_3593116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593116 prefixEnd_3593116 := by exact prefixLift 3593116
  have htrace : WordTrace (prefixWord ++ tailWord_3593116) baseStart_3593116 baseEnd_3593116 := by
    simpa [prefixWord, tailWord_3593116, baseEnd_3593116] using wordTrace_append hprefix tailTrace_3593116
  have hstable : (prefixWord ++ tailWord_3593116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593116).length < 2 ^ (prefixWord ++ tailWord_3593116).sum := by decide
  have hdescent : baseEnd_3593116 < baseStart_3593116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593191 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3593191 : Nat := 118140960795 + 3593191 * 2 ^ 59
def prefixEnd_3593191 : Nat := 4983230072969 + 3 ^ 40 * 3593191 * 2
def baseEnd_3593191 : Nat := 1230022710939704238258481

theorem tailTrace_3593191 : CollatzResearch.WordTrace tailWord_3593191 prefixEnd_3593191 1230022710939704238258481 := by
  unfold tailWord_3593191
  simp only [CollatzResearch.WordTrace]
  refine ⟨131054442325490150011291427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87369628216993433340860951 131054442325490150011291427)
  ·
    refine ⟨196581663488235225016937141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131054442325490150011291427 196581663488235225016937141)
    ·
      refine ⟨18429530952022052345337857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196581663488235225016937141 18429530952022052345337857)
      ·
        refine ⟨13822148214016539259003393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18429530952022052345337857 13822148214016539259003393)
        ·
          refine ⟨10366611160512404444252545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13822148214016539259003393 10366611160512404444252545)
          ·
            refine ⟨7774958370384303333189409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10366611160512404444252545 7774958370384303333189409)
            ·
              refine ⟨5831218777788227499892057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7774958370384303333189409 5831218777788227499892057)
              ·
                refine ⟨4373414083341170624919043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5831218777788227499892057 4373414083341170624919043)
                ·
                  refine ⟨6560121125011755937378565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373414083341170624919043 6560121125011755937378565)
                  ·
                    refine ⟨1230022710939704238258481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6560121125011755937378565 1230022710939704238258481)
                    ·
                      rfl

theorem cell22_3593191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3593191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593191 prefixEnd_3593191 := by exact prefixLift 3593191
  have htrace : WordTrace (prefixWord ++ tailWord_3593191) baseStart_3593191 baseEnd_3593191 := by
    simpa [prefixWord, tailWord_3593191, baseEnd_3593191] using wordTrace_append hprefix tailTrace_3593191
  have hstable : (prefixWord ++ tailWord_3593191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593191).length < 2 ^ (prefixWord ++ tailWord_3593191).sum := by decide
  have hdescent : baseEnd_3593191 < baseStart_3593191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593217 : List Nat := [1, 2, 4, 1, 2, 2, 10]
def baseStart_3593217 : Nat := 118140960795 + 3593217 * 2 ^ 59
def prefixEnd_3593217 : Nat := 4983230072969 + 3 ^ 40 * 3593217 * 2
def baseEnd_3593217 : Nat := 45556726343372179152163

theorem tailTrace_3593217 : CollatzResearch.WordTrace tailWord_3593217 prefixEnd_3593217 45556726343372179152163 := by
  unfold tailWord_3593217
  simp only [CollatzResearch.WordTrace]
  refine ⟨131055390623395956451737905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87370260415597304301158603 131055390623395956451737905)
  ·
    refine ⟨98291542967546967338803429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131055390623395956451737905 98291542967546967338803429)
    ·
      refine ⟨18429664306415056376025643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98291542967546967338803429 18429664306415056376025643)
      ·
        refine ⟨27644496459622584564038465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18429664306415056376025643 27644496459622584564038465)
        ·
          refine ⟨20733372344716938423028849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27644496459622584564038465 20733372344716938423028849)
          ·
            refine ⟨15550029258537703817271637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20733372344716938423028849 15550029258537703817271637)
            ·
              refine ⟨45556726343372179152163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15550029258537703817271637 45556726343372179152163)
              ·
                rfl

theorem cell22_3593217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 10].length) (baseStart_3593217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593217 prefixEnd_3593217 := by exact prefixLift 3593217
  have htrace : WordTrace (prefixWord ++ tailWord_3593217) baseStart_3593217 baseEnd_3593217 := by
    simpa [prefixWord, tailWord_3593217, baseEnd_3593217] using wordTrace_append hprefix tailTrace_3593217
  have hstable : (prefixWord ++ tailWord_3593217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593217).length < 2 ^ (prefixWord ++ tailWord_3593217).sum := by decide
  have hdescent : baseEnd_3593217 < baseStart_3593217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593294 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3593294 : Nat := 118140960795 + 3593294 * 2 ^ 59
def prefixEnd_3593294 : Nat := 4983230072969 + 3 ^ 40 * 3593294 * 2
def baseEnd_3593294 : Nat := 1230057969944646302933165

theorem tailTrace_3593294 : CollatzResearch.WordTrace tailWord_3593294 prefixEnd_3593294 1230057969944646302933165 := by
  unfold tailWord_3593294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16382274880514624825286367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87372132696077999068193957 16382274880514624825286367)
  ·
    refine ⟨24573412320771937237929551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16382274880514624825286367 24573412320771937237929551)
    ·
      refine ⟨36860118481157905856894327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24573412320771937237929551 36860118481157905856894327)
      ·
        refine ⟨55290177721736858785341491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36860118481157905856894327 55290177721736858785341491)
        ·
          refine ⟨82935266582605288178012237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55290177721736858785341491 82935266582605288178012237)
          ·
            refine ⟨31100724968476983066754589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82935266582605288178012237 31100724968476983066754589)
            ·
              refine ⟨11662771863178868650032971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31100724968476983066754589 11662771863178868650032971)
              ·
                refine ⟨17494157794768302975049457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11662771863178868650032971 17494157794768302975049457)
                ·
                  refine ⟨13120618346076227231287093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17494157794768302975049457 13120618346076227231287093)
                  ·
                    refine ⟨1230057969944646302933165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13120618346076227231287093 1230057969944646302933165)
                    ·
                      rfl

theorem cell22_3593294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3593294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593294 prefixEnd_3593294 := by exact prefixLift 3593294
  have htrace : WordTrace (prefixWord ++ tailWord_3593294) baseStart_3593294 baseEnd_3593294 := by
    simpa [prefixWord, tailWord_3593294, baseEnd_3593294] using wordTrace_append hprefix tailTrace_3593294
  have hstable : (prefixWord ++ tailWord_3593294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593294).length < 2 ^ (prefixWord ++ tailWord_3593294).sum := by decide
  have hdescent : baseEnd_3593294 < baseStart_3593294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593341 : List Nat := [1, 4, 1, 1, 3, 1, 1, 6, 4]
def baseStart_3593341 : Nat := 118140960795 + 3593341 * 2 ^ 59
def prefixEnd_3593341 : Nat := 4983230072969 + 3 ^ 40 * 3593341 * 2
def baseEnd_3593341 : Nat := 410024686335051282336007

theorem tailTrace_3593341 : CollatzResearch.WordTrace tailWord_3593341 prefixEnd_3593341 410024686335051282336007 := by
  unfold tailWord_3593341
  simp only [CollatzResearch.WordTrace]
  refine ⟨131059913274946725629251877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87373275516631150419501251 131059913274946725629251877)
  ·
    refine ⟨24573733739052511055484727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131059913274946725629251877 24573733739052511055484727)
    ·
      refine ⟨36860600608578766583227091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24573733739052511055484727 36860600608578766583227091)
      ·
        refine ⟨55290900912868149874840637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36860600608578766583227091 55290900912868149874840637)
        ·
          refine ⟨20734087842325556203065239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55290900912868149874840637 20734087842325556203065239)
          ·
            refine ⟨31101131763488334304597859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20734087842325556203065239 31101131763488334304597859)
            ·
              refine ⟨46651697645232501456896789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31101131763488334304597859 46651697645232501456896789)
              ·
                refine ⟨2186798327120273505792037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46651697645232501456896789 2186798327120273505792037)
                ·
                  refine ⟨410024686335051282336007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2186798327120273505792037 410024686335051282336007)
                  ·
                    rfl

theorem cell22_3593341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_3593341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593341 prefixEnd_3593341 := by exact prefixLift 3593341
  have htrace : WordTrace (prefixWord ++ tailWord_3593341) baseStart_3593341 baseEnd_3593341 := by
    simpa [prefixWord, tailWord_3593341, baseEnd_3593341] using wordTrace_append hprefix tailTrace_3593341
  have hstable : (prefixWord ++ tailWord_3593341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593341).length < 2 ^ (prefixWord ++ tailWord_3593341).sum := by decide
  have hdescent : baseEnd_3593341 < baseStart_3593341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593354 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_3593354 : Nat := 118140960795 + 3593354 * 2 ^ 59
def prefixEnd_3593354 : Nat := 4983230072969 + 3 ^ 40 * 3593354 * 2
def baseEnd_3593354 : Nat := 1230078509170826146432981

theorem tailTrace_3593354 : CollatzResearch.WordTrace tailWord_3593354 prefixEnd_3593354 1230078509170826146432981 := by
  unfold tailWord_3593354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32765096855974907212368779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87373591615933085899650077 32765096855974907212368779)
  ·
    refine ⟨49147645283962360818553169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32765096855974907212368779 49147645283962360818553169)
    ·
      refine ⟨36860733962971770613914877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49147645283962360818553169 36860733962971770613914877)
      ·
        refine ⟨13822775236114413980218079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36860733962971770613914877 13822775236114413980218079)
        ·
          refine ⟨20734162854171620970327119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13822775236114413980218079 20734162854171620970327119)
          ·
            refine ⟨31101244281257431455490679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20734162854171620970327119 31101244281257431455490679)
            ·
              refine ⟨46651866421886147183236019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31101244281257431455490679 46651866421886147183236019)
              ·
                refine ⟨69977799632829220774854029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46651866421886147183236019 69977799632829220774854029)
                ·
                  refine ⟨26241674862310957790570261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69977799632829220774854029 26241674862310957790570261)
                  ·
                    refine ⟨1230078509170826146432981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26241674862310957790570261 1230078509170826146432981)
                    ·
                      rfl

theorem cell22_3593354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_3593354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593354 prefixEnd_3593354 := by exact prefixLift 3593354
  have htrace : WordTrace (prefixWord ++ tailWord_3593354) baseStart_3593354 baseEnd_3593354 := by
    simpa [prefixWord, tailWord_3593354, baseEnd_3593354] using wordTrace_append hprefix tailTrace_3593354
  have hstable : (prefixWord ++ tailWord_3593354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593354).length < 2 ^ (prefixWord ++ tailWord_3593354).sum := by decide
  have hdescent : baseEnd_3593354 < baseStart_3593354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593356 : List Nat := [2, 2, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_3593356 : Nat := 118140960795 + 3593356 * 2 ^ 59
def prefixEnd_3593356 : Nat := 4983230072969 + 3 ^ 40 * 3593356 * 2
def baseEnd_3593356 : Nat := 1230079193811698807882975

theorem tailTrace_3593356 : CollatzResearch.WordTrace tailWord_3593356 prefixEnd_3593356 1230079193811698807882975 := by
  unfold tailWord_3593356
  simp only [CollatzResearch.WordTrace]
  refine ⟨65530230184946191595523961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87373640246594922127365281 65530230184946191595523961)
  ·
    refine ⟨49147672638709643696642971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65530230184946191595523961 49147672638709643696642971)
    ·
      refine ⟨73721508958064465544964457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49147672638709643696642971 73721508958064465544964457)
      ·
        refine ⟨55291131718548349158723343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73721508958064465544964457 55291131718548349158723343)
        ·
          refine ⟨82936697577822523738085015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55291131718548349158723343 82936697577822523738085015)
          ·
            refine ⟨124405046366733785607127523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82936697577822523738085015 124405046366733785607127523)
            ·
              refine ⟨186607569550100678410691285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124405046366733785607127523 186607569550100678410691285)
              ·
                refine ⟨4373614911330484650250577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 186607569550100678410691285 4373614911330484650250577)
                ·
                  refine ⟨3280211183497863487687933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4373614911330484650250577 3280211183497863487687933)
                  ·
                    refine ⟨1230079193811698807882975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280211183497863487687933 1230079193811698807882975)
                    ·
                      rfl

theorem cell22_3593356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_3593356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593356 prefixEnd_3593356 := by exact prefixLift 3593356
  have htrace : WordTrace (prefixWord ++ tailWord_3593356) baseStart_3593356 baseEnd_3593356 := by
    simpa [prefixWord, tailWord_3593356, baseEnd_3593356] using wordTrace_append hprefix tailTrace_3593356
  have hstable : (prefixWord ++ tailWord_3593356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593356).length < 2 ^ (prefixWord ++ tailWord_3593356).sum := by decide
  have hdescent : baseEnd_3593356 < baseStart_3593356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593375 : List Nat := [1, 1, 2, 6, 2, 2, 1, 3, 4]
def baseStart_3593375 : Nat := 118140960795 + 3593375 * 2 ^ 59
def prefixEnd_3593375 : Nat := 4983230072969 + 3 ^ 40 * 3593375 * 2
def baseEnd_3593375 : Nat := 410028565966663030552639

theorem tailTrace_3593375 : CollatzResearch.WordTrace tailWord_3593375 prefixEnd_3593375 410028565966663030552639 := by
  unfold tailWord_3593375
  simp only [CollatzResearch.WordTrace]
  refine ⟨131061153356823549435989579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87374102237882366290659719 131061153356823549435989579)
  ·
    refine ⟨196591730035235324153984369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131061153356823549435989579 196591730035235324153984369)
    ·
      refine ⟨147443797526426493115488277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196591730035235324153984369 147443797526426493115488277)
      ·
        refine ⟨6911428009051241864788513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147443797526426493115488277 6911428009051241864788513)
        ·
          refine ⟨5183571006788431398591385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6911428009051241864788513 5183571006788431398591385)
          ·
            refine ⟨3887678255091323548943539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5183571006788431398591385 3887678255091323548943539)
            ·
              refine ⟨5831517382636985323415309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3887678255091323548943539 5831517382636985323415309)
              ·
                refine ⟨2186819018488869496280741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5831517382636985323415309 2186819018488869496280741)
                ·
                  refine ⟨410028565966663030552639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2186819018488869496280741 410028565966663030552639)
                  ·
                    rfl

theorem cell22_3593375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3, 4].length) (baseStart_3593375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593375 prefixEnd_3593375 := by exact prefixLift 3593375
  have htrace : WordTrace (prefixWord ++ tailWord_3593375) baseStart_3593375 baseEnd_3593375 := by
    simpa [prefixWord, tailWord_3593375, baseEnd_3593375] using wordTrace_append hprefix tailTrace_3593375
  have hstable : (prefixWord ++ tailWord_3593375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593375).length < 2 ^ (prefixWord ++ tailWord_3593375).sum := by decide
  have hdescent : baseEnd_3593375 < baseStart_3593375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593386 : List Nat := [3, 1, 5, 1, 1, 1, 10]
def baseStart_3593386 : Nat := 118140960795 + 3593386 * 2 ^ 59
def prefixEnd_3593386 : Nat := 4983230072969 + 3 ^ 40 * 3593386 * 2
def baseEnd_3593386 : Nat := 45558869015732915912329

theorem tailTrace_3593386 : CollatzResearch.WordTrace tailWord_3593386 prefixEnd_3593386 45558869015732915912329 := by
  unfold tailWord_3593386
  simp only [CollatzResearch.WordTrace]
  refine ⟨32765388639945924578660003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87374369706522465543093341 32765388639945924578660003)
  ·
    refine ⟨49148082959918886867990005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32765388639945924578660003 49148082959918886867990005)
    ·
      refine ⟨4607632777492395643874063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49148082959918886867990005 4607632777492395643874063)
      ·
        refine ⟨6911449166238593465811095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4607632777492395643874063 6911449166238593465811095)
        ·
          refine ⟨10367173749357890198716643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911449166238593465811095 10367173749357890198716643)
          ·
            refine ⟨15550760624036835298074965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367173749357890198716643 15550760624036835298074965)
            ·
              refine ⟨45558869015732915912329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15550760624036835298074965 45558869015732915912329)
              ·
                rfl

theorem cell22_3593386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 10].length) (baseStart_3593386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593386 prefixEnd_3593386 := by exact prefixLift 3593386
  have htrace : WordTrace (prefixWord ++ tailWord_3593386) baseStart_3593386 baseEnd_3593386 := by
    simpa [prefixWord, tailWord_3593386, baseEnd_3593386] using wordTrace_append hprefix tailTrace_3593386
  have hstable : (prefixWord ++ tailWord_3593386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593386).length < 2 ^ (prefixWord ++ tailWord_3593386).sum := by decide
  have hdescent : baseEnd_3593386 < baseStart_3593386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593399 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3593399 : Nat := 118140960795 + 3593399 * 2 ^ 59
def prefixEnd_3593399 : Nat := 4983230072969 + 3 ^ 40 * 3593399 * 2
def baseEnd_3593399 : Nat := 1230093913590461029057843

theorem tailTrace_3593399 : CollatzResearch.WordTrace tailWord_3593399 prefixEnd_3593399 1230093913590461029057843 := by
  unfold tailWord_3593399
  simp only [CollatzResearch.WordTrace]
  refine ⟨131062028708736601534863251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87374685805824401023242167 131062028708736601534863251)
  ·
    refine ⟨196593043063104902302294877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131062028708736601534863251 196593043063104902302294877)
    ·
      refine ⟨73722391148664338363360579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196593043063104902302294877 73722391148664338363360579)
      ·
        refine ⟨110583586722996507545040869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73722391148664338363360579 110583586722996507545040869)
        ·
          refine ⟨20734422510561845164695163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110583586722996507545040869 20734422510561845164695163)
          ·
            refine ⟨31101633765842767747042745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20734422510561845164695163 31101633765842767747042745)
            ·
              refine ⟨23326225324382075810282059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31101633765842767747042745 23326225324382075810282059)
              ·
                refine ⟨34989337986573113715423089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23326225324382075810282059 34989337986573113715423089)
                ·
                  refine ⟨26242003489929835286567317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34989337986573113715423089 26242003489929835286567317)
                  ·
                    refine ⟨1230093913590461029057843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26242003489929835286567317 1230093913590461029057843)
                    ·
                      rfl

theorem cell22_3593399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3593399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593399 prefixEnd_3593399 := by exact prefixLift 3593399
  have htrace : WordTrace (prefixWord ++ tailWord_3593399) baseStart_3593399 baseEnd_3593399 := by
    simpa [prefixWord, tailWord_3593399, baseEnd_3593399] using wordTrace_append hprefix tailTrace_3593399
  have hstable : (prefixWord ++ tailWord_3593399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593399).length < 2 ^ (prefixWord ++ tailWord_3593399).sum := by decide
  have hdescent : baseEnd_3593399 < baseStart_3593399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593452 : List Nat := [2, 2, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_3593452 : Nat := 118140960795 + 3593452 * 2 ^ 59
def prefixEnd_3593452 : Nat := 4983230072969 + 3 ^ 40 * 3593452 * 2
def baseEnd_3593452 : Nat := 1230112056573586557482681

theorem tailTrace_3593452 : CollatzResearch.WordTrace tailWord_3593452 prefixEnd_3593452 1230112056573586557482681 := by
  unfold tailWord_3593452
  simp only [CollatzResearch.WordTrace]
  refine ⟨65531980888772295793271305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87375974518363061057695073 65531980888772295793271305)
  ·
    refine ⟨49148985666579221844953479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65531980888772295793271305 49148985666579221844953479)
    ·
      refine ⟨73723478499868832767430219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49148985666579221844953479 73723478499868832767430219)
      ·
        refine ⟨110585217749803249151145329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73723478499868832767430219 110585217749803249151145329)
        ·
          refine ⟨82938913312352436863358997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110585217749803249151145329 82938913312352436863358997)
          ·
            refine ⟨3887761561516520477969953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82938913312352436863358997 3887761561516520477969953)
            ·
              refine ⟨2915821171137390358477465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3887761561516520477969953 2915821171137390358477465)
              ·
                refine ⟨2186865878353042768858099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2915821171137390358477465 2186865878353042768858099)
                ·
                  refine ⟨3280298817529564153287149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2186865878353042768858099 3280298817529564153287149)
                  ·
                    refine ⟨1230112056573586557482681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280298817529564153287149 1230112056573586557482681)
                    ·
                      rfl

theorem cell22_3593452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_3593452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593452 prefixEnd_3593452 := by exact prefixLift 3593452
  have htrace : WordTrace (prefixWord ++ tailWord_3593452) baseStart_3593452 baseEnd_3593452 := by
    simpa [prefixWord, tailWord_3593452, baseEnd_3593452] using wordTrace_append hprefix tailTrace_3593452
  have hstable : (prefixWord ++ tailWord_3593452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593452).length < 2 ^ (prefixWord ++ tailWord_3593452).sum := by decide
  have hdescent : baseEnd_3593452 < baseStart_3593452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593476 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 8]
def baseStart_3593476 : Nat := 118140960795 + 3593476 * 2 ^ 59
def prefixEnd_3593476 : Nat := 4983230072969 + 3 ^ 40 * 3593476 * 2
def baseEnd_3593476 : Nat := 410040090754686164960869

theorem tailTrace_3593476 : CollatzResearch.WordTrace tailWord_3593476 prefixEnd_3593476 410040090754686164960869 := by
  unfold tailWord_3593476
  simp only [CollatzResearch.WordTrace]
  refine ⟨65532418564728821842708141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87376558086305095790277521 65532418564728821842708141)
  ·
    refine ⟨24574656961773308191015553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65532418564728821842708141 24574656961773308191015553)
    ·
      refine ⟨18430992721329981143261665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24574656961773308191015553 18430992721329981143261665)
      ·
        refine ⟨13823244540997485857446249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18430992721329981143261665 13823244540997485857446249)
        ·
          refine ⟨10367433405748114393084687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13823244540997485857446249 10367433405748114393084687)
          ·
            refine ⟨15551150108622171589627031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10367433405748114393084687 15551150108622171589627031)
            ·
              refine ⟨23326725162933257384440547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15551150108622171589627031 23326725162933257384440547)
              ·
                refine ⟨34990087744399886076660821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23326725162933257384440547 34990087744399886076660821)
                ·
                  refine ⟨410040090754686164960869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34990087744399886076660821 410040090754686164960869)
                  ·
                    rfl

theorem cell22_3593476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_3593476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593476 prefixEnd_3593476 := by exact prefixLift 3593476
  have htrace : WordTrace (prefixWord ++ tailWord_3593476) baseStart_3593476 baseEnd_3593476 := by
    simpa [prefixWord, tailWord_3593476, baseEnd_3593476] using wordTrace_append hprefix tailTrace_3593476
  have hstable : (prefixWord ++ tailWord_3593476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593476).length < 2 ^ (prefixWord ++ tailWord_3593476).sum := by decide
  have hdescent : baseEnd_3593476 < baseStart_3593476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593508 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 4, 3]
def baseStart_3593508 : Nat := 118140960795 + 3593508 * 2 ^ 59
def prefixEnd_3593508 : Nat := 4983230072969 + 3 ^ 40 * 3593508 * 2
def baseEnd_3593508 : Nat := 1230131226518021078082509

theorem tailTrace_3593508 : CollatzResearch.WordTrace tailWord_3593508 prefixEnd_3593508 1230131226518021078082509 := by
  unfold tailWord_3593508
  simp only [CollatzResearch.WordTrace]
  refine ⟨65533002132670856575290589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87377336176894475433720785 65533002132670856575290589)
  ·
    refine ⟨24574875799751571215733971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65533002132670856575290589 24574875799751571215733971)
    ·
      refine ⟨36862313699627356823600957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24574875799751571215733971 36862313699627356823600957)
      ·
        refine ⟨13823367637360258808850359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36862313699627356823600957 13823367637360258808850359)
        ·
          refine ⟨20735051456040388213275539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13823367637360258808850359 20735051456040388213275539)
          ·
            refine ⟨31102577184060582319913309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20735051456040388213275539 31102577184060582319913309)
            ·
              refine ⟨11663466444022718369967491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31102577184060582319913309 11663466444022718369967491)
              ·
                refine ⟨17495199666034077554951237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11663466444022718369967491 17495199666034077554951237)
                ·
                  refine ⟨3280349937381389541553357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17495199666034077554951237 3280349937381389541553357)
                  ·
                    refine ⟨1230131226518021078082509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280349937381389541553357 1230131226518021078082509)
                    ·
                      rfl

theorem cell22_3593508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_3593508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593508 prefixEnd_3593508 := by exact prefixLift 3593508
  have htrace : WordTrace (prefixWord ++ tailWord_3593508) baseStart_3593508 baseEnd_3593508 := by
    simpa [prefixWord, tailWord_3593508, baseEnd_3593508] using wordTrace_append hprefix tailTrace_3593508
  have hstable : (prefixWord ++ tailWord_3593508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593508).length < 2 ^ (prefixWord ++ tailWord_3593508).sum := by decide
  have hdescent : baseEnd_3593508 < baseStart_3593508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593645 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 6]
def baseStart_3593645 : Nat := 118140960795 + 3593645 * 2 ^ 59
def prefixEnd_3593645 : Nat := 4983230072969 + 3 ^ 40 * 3593645 * 2
def baseEnd_3593645 : Nat := 410059374805932795802363

theorem tailTrace_3593645 : CollatzResearch.WordTrace tailWord_3593645 prefixEnd_3593645 410059374805932795802363 := by
  unfold tailWord_3593645
  simp only [CollatzResearch.WordTrace]
  refine ⟨131071001065845385548318389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87380667377230257032212259 131071001065845385548318389)
  ·
    refine ⟨12287906349923004895154849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131071001065845385548318389 12287906349923004895154849)
    ·
      refine ⟨9215929762442253671366137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12287906349923004895154849 9215929762442253671366137)
      ·
        refine ⟨6911947321831690253524603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9215929762442253671366137 6911947321831690253524603)
        ·
          refine ⟨10367920982747535380286905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6911947321831690253524603 10367920982747535380286905)
          ·
            refine ⟨7775940737060651535215179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10367920982747535380286905 7775940737060651535215179)
            ·
              refine ⟨11663911105590977302822769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7775940737060651535215179 11663911105590977302822769)
              ·
                refine ⟨8747933329193232977117077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11663911105590977302822769 8747933329193232977117077)
                ·
                  refine ⟨410059374805932795802363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8747933329193232977117077 410059374805932795802363)
                  ·
                    rfl

theorem cell22_3593645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_3593645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593645 prefixEnd_3593645 := by exact prefixLift 3593645
  have htrace : WordTrace (prefixWord ++ tailWord_3593645) baseStart_3593645 baseEnd_3593645 := by
    simpa [prefixWord, tailWord_3593645, baseEnd_3593645] using wordTrace_append hprefix tailTrace_3593645
  have hstable : (prefixWord ++ tailWord_3593645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593645).length < 2 ^ (prefixWord ++ tailWord_3593645).sum := by decide
  have hdescent : baseEnd_3593645 < baseStart_3593645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593656 : List Nat := [2, 1, 2, 1, 2, 2, 2, 10]
def baseStart_3593656 : Nat := 118140960795 + 3593656 * 2 ^ 59
def prefixEnd_3593656 : Nat := 4983230072969 + 3 ^ 40 * 3593656 * 2
def baseEnd_3593656 : Nat := 136686876660288669486895

theorem tailTrace_3593656 : CollatzResearch.WordTrace tailWord_3593656 prefixEnd_3593656 136686876660288669486895 := by
  unfold tailWord_3593656
  simp only [CollatzResearch.WordTrace]
  refine ⟨65535701134402767213484411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87380934845870356284645881 65535701134402767213484411)
  ·
    refine ⟨98303551701604150820226617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65535701134402767213484411 98303551701604150820226617)
    ·
      refine ⟨73727663776203113115169963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98303551701604150820226617 73727663776203113115169963)
      ·
        refine ⟨110591495664304669672754945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73727663776203113115169963 110591495664304669672754945)
        ·
          refine ⟨82943621748228502254566209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110591495664304669672754945 82943621748228502254566209)
          ·
            refine ⟨62207716311171376690924657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82943621748228502254566209 62207716311171376690924657)
            ·
              refine ⟨46655787233378532518193493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62207716311171376690924657 46655787233378532518193493)
              ·
                refine ⟨136686876660288669486895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46655787233378532518193493 136686876660288669486895)
                ·
                  rfl

theorem cell22_3593656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 10].length) (baseStart_3593656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593656 prefixEnd_3593656 := by exact prefixLift 3593656
  have htrace : WordTrace (prefixWord ++ tailWord_3593656) baseStart_3593656 baseEnd_3593656 := by
    simpa [prefixWord, tailWord_3593656, baseEnd_3593656] using wordTrace_append hprefix tailTrace_3593656
  have hstable : (prefixWord ++ tailWord_3593656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593656).length < 2 ^ (prefixWord ++ tailWord_3593656).sum := by decide
  have hdescent : baseEnd_3593656 < baseStart_3593656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593739 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 3, 3]
def baseStart_3593739 : Nat := 118140960795 + 3593739 * 2 ^ 59
def prefixEnd_3593739 : Nat := 4983230072969 + 3 ^ 40 * 3593739 * 2
def baseEnd_3593739 : Nat := 1230210302538813475556801

theorem tailTrace_3593739 : CollatzResearch.WordTrace tailWord_3593739 prefixEnd_3593739 1230210302538813475556801 := by
  unfold tailWord_3593739
  simp only [CollatzResearch.WordTrace]
  refine ⟨131074429527504839602240271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87382953018336559734826847 131074429527504839602240271)
  ·
    refine ⟨196611644291257259403360407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131074429527504839602240271 196611644291257259403360407)
    ·
      refine ⟨294917466436885889105040611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196611644291257259403360407 294917466436885889105040611)
      ·
        refine ⟨442376199655328833657560917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294917466436885889105040611 442376199655328833657560917)
        ·
          refine ⟨2592048044855442384712271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 442376199655328833657560917 2592048044855442384712271)
          ·
            refine ⟨3888072067283163577068407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592048044855442384712271 3888072067283163577068407)
            ·
              refine ⟨5832108100924745365602611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888072067283163577068407 5832108100924745365602611)
              ·
                refine ⟨8748162151387118048403917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832108100924745365602611 8748162151387118048403917)
                ·
                  refine ⟨3280560806770169268151469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8748162151387118048403917 3280560806770169268151469)
                  ·
                    refine ⟨1230210302538813475556801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280560806770169268151469 1230210302538813475556801)
                    ·
                      rfl

theorem cell22_3593739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 3].length) (baseStart_3593739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593739 prefixEnd_3593739 := by exact prefixLift 3593739
  have htrace : WordTrace (prefixWord ++ tailWord_3593739) baseStart_3593739 baseEnd_3593739 := by
    simpa [prefixWord, tailWord_3593739, baseEnd_3593739] using wordTrace_append hprefix tailTrace_3593739
  have hstable : (prefixWord ++ tailWord_3593739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593739).length < 2 ^ (prefixWord ++ tailWord_3593739).sum := by decide
  have hdescent : baseEnd_3593739 < baseStart_3593739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593812 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_3593812 : Nat := 118140960795 + 3593812 * 2 ^ 59
def prefixEnd_3593812 : Nat := 4983230072969 + 3 ^ 40 * 3593812 * 2
def baseEnd_3593812 : Nat := 1230235291930665618481577

theorem tailTrace_3593812 : CollatzResearch.WordTrace tailWord_3593812 prefixEnd_3593812 1230235291930665618481577 := by
  unfold tailWord_3593812
  simp only [CollatzResearch.WordTrace]
  refine ⟨65538546028120186534823845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87384728037493582046431793 65538546028120186534823845)
  ·
    refine ⟨12288477380272534975279471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65538546028120186534823845 12288477380272534975279471)
    ·
      refine ⟨18432716070408802462919207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12288477380272534975279471 18432716070408802462919207)
      ·
        refine ⟨27649074105613203694378811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18432716070408802462919207 27649074105613203694378811)
        ·
          refine ⟨41473611158419805541568217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27649074105613203694378811 41473611158419805541568217)
          ·
            refine ⟨31105208368814854156176163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41473611158419805541568217 31105208368814854156176163)
            ·
              refine ⟨46657812553222281234264245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31105208368814854156176163 46657812553222281234264245)
              ·
                refine ⟨4374169926864588865712273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46657812553222281234264245 4374169926864588865712273)
                ·
                  refine ⟨3280627445148441649284205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4374169926864588865712273 3280627445148441649284205)
                  ·
                    refine ⟨1230235291930665618481577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280627445148441649284205 1230235291930665618481577)
                    ·
                      rfl

theorem cell22_3593812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_3593812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593812 prefixEnd_3593812 := by exact prefixLift 3593812
  have htrace : WordTrace (prefixWord ++ tailWord_3593812) baseStart_3593812 baseEnd_3593812 := by
    simpa [prefixWord, tailWord_3593812, baseEnd_3593812] using wordTrace_append hprefix tailTrace_3593812
  have hstable : (prefixWord ++ tailWord_3593812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593812).length < 2 ^ (prefixWord ++ tailWord_3593812).sum := by decide
  have hdescent : baseEnd_3593812 < baseStart_3593812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593825 : List Nat := [1, 2, 3, 1, 1, 3, 5, 6]
def baseStart_3593825 : Nat := 118140960795 + 3593825 * 2 ^ 59
def prefixEnd_3593825 : Nat := 4983230072969 + 3 ^ 40 * 3593825 * 2
def baseEnd_3593825 : Nat := 136693304677370879767393

theorem tailTrace_3593825 : CollatzResearch.WordTrace tailWord_3593825 prefixEnd_3593825 136693304677370879767393 := by
  unfold tailWord_3593825
  simp only [CollatzResearch.WordTrace]
  refine ⟨131077566205193276289870929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87385044136795517526580619 131077566205193276289870929)
  ·
    refine ⟨98308174653894957217403197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131077566205193276289870929 98308174653894957217403197)
    ·
      refine ⟨36865565495210608956526199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98308174653894957217403197 36865565495210608956526199)
      ·
        refine ⟨55298348242815913434789299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36865565495210608956526199 55298348242815913434789299)
        ·
          refine ⟨82947522364223870152183949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55298348242815913434789299 82947522364223870152183949)
          ·
            refine ⟨31105320886583951307068981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82947522364223870152183949 31105320886583951307068981)
            ·
              refine ⟨2916123833117245435037717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31105320886583951307068981 2916123833117245435037717)
              ·
                refine ⟨136693304677370879767393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2916123833117245435037717 136693304677370879767393)
                ·
                  rfl

theorem cell22_3593825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 6].length) (baseStart_3593825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593825 prefixEnd_3593825 := by exact prefixLift 3593825
  have htrace : WordTrace (prefixWord ++ tailWord_3593825) baseStart_3593825 baseEnd_3593825 := by
    simpa [prefixWord, tailWord_3593825, baseEnd_3593825] using wordTrace_append hprefix tailTrace_3593825
  have hstable : (prefixWord ++ tailWord_3593825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593825).length < 2 ^ (prefixWord ++ tailWord_3593825).sum := by decide
  have hdescent : baseEnd_3593825 < baseStart_3593825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593827 : List Nat := [1, 1, 1, 5, 1, 5, 1, 1, 2, 4]
def baseStart_3593827 : Nat := 118140960795 + 3593827 * 2 ^ 59
def prefixEnd_3593827 : Nat := 4983230072969 + 3 ^ 40 * 3593827 * 2
def baseEnd_3593827 : Nat := 1230240426737210579356531

theorem tailTrace_3593827 : CollatzResearch.WordTrace tailWord_3593827 prefixEnd_3593827 1230240426737210579356531 := by
  unfold tailWord_3593827
  simp only [CollatzResearch.WordTrace]
  refine ⟨131077639151186030631443735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87385092767457353754295823 131077639151186030631443735)
  ·
    refine ⟨196616458726779045947165603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131077639151186030631443735 196616458726779045947165603)
    ·
      refine ⟨294924688090168568920748405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196616458726779045947165603 294924688090168568920748405)
      ·
        refine ⟨27649189508453303336320163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294924688090168568920748405 27649189508453303336320163)
        ·
          refine ⟨41473784262679955004480245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27649189508453303336320163 41473784262679955004480245)
          ·
            refine ⟨3888167274626245781670023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41473784262679955004480245 3888167274626245781670023)
            ·
              refine ⟨5832250911939368672505035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888167274626245781670023 5832250911939368672505035)
              ·
                refine ⟨8748376367909053008757553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832250911939368672505035 8748376367909053008757553)
                ·
                  refine ⟨6561282275931789756568165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8748376367909053008757553 6561282275931789756568165)
                  ·
                    refine ⟨1230240426737210579356531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6561282275931789756568165 1230240426737210579356531)
                    ·
                      rfl

theorem cell22_3593827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 4].length) (baseStart_3593827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593827 prefixEnd_3593827 := by exact prefixLift 3593827
  have htrace : WordTrace (prefixWord ++ tailWord_3593827) baseStart_3593827 baseEnd_3593827 := by
    simpa [prefixWord, tailWord_3593827, baseEnd_3593827] using wordTrace_append hprefix tailTrace_3593827
  have hstable : (prefixWord ++ tailWord_3593827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593827).length < 2 ^ (prefixWord ++ tailWord_3593827).sum := by decide
  have hdescent : baseEnd_3593827 < baseStart_3593827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593846 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_3593846 : Nat := 118140960795 + 3593846 * 2 ^ 59
def prefixEnd_3593846 : Nat := 4983230072969 + 3 ^ 40 * 3593846 * 2
def baseEnd_3593846 : Nat := 1230246930825500863131473

theorem tailTrace_3593846 : CollatzResearch.WordTrace tailWord_3593846 prefixEnd_3593846 1230246930825500863131473 := by
  unfold tailWord_3593846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192395758632324804774087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87385554758744797917590261 8192395758632324804774087)
  ·
    refine ⟨12288593637948487207161131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8192395758632324804774087 12288593637948487207161131)
    ·
      refine ⟨18432890456922730810741697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12288593637948487207161131 18432890456922730810741697)
      ·
        refine ⟨13824667842692048108056273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18432890456922730810741697 13824667842692048108056273)
        ·
          refine ⟨10368500882019036081042205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13824667842692048108056273 10368500882019036081042205)
          ·
            refine ⟨3888187830757138530390827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10368500882019036081042205 3888187830757138530390827)
            ·
              refine ⟨5832281746135707795586241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888187830757138530390827 5832281746135707795586241)
              ·
                refine ⟨4374211309601780846689681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5832281746135707795586241 4374211309601780846689681)
                ·
                  refine ⟨3280658482201335635017261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4374211309601780846689681 3280658482201335635017261)
                  ·
                    refine ⟨1230246930825500863131473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280658482201335635017261 1230246930825500863131473)
                    ·
                      rfl

theorem cell22_3593846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_3593846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593846 prefixEnd_3593846 := by exact prefixLift 3593846
  have htrace : WordTrace (prefixWord ++ tailWord_3593846) baseStart_3593846 baseEnd_3593846 := by
    simpa [prefixWord, tailWord_3593846, baseEnd_3593846] using wordTrace_append hprefix tailTrace_3593846
  have hstable : (prefixWord ++ tailWord_3593846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593846).length < 2 ^ (prefixWord ++ tailWord_3593846).sum := by decide
  have hdescent : baseEnd_3593846 < baseStart_3593846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593857 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3593857 : Nat := 118140960795 + 3593857 * 2 ^ 59
def prefixEnd_3593857 : Nat := 4983230072969 + 3 ^ 40 * 3593857 * 2
def baseEnd_3593857 : Nat := 1230250696350300501106439

theorem tailTrace_3593857 : CollatzResearch.WordTrace tailWord_3593857 prefixEnd_3593857 1230250696350300501106439 := by
  unfold tailWord_3593857
  simp only [CollatzResearch.WordTrace]
  refine ⟨131078733341077345755035825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87385822227384897170023883 131078733341077345755035825)
  ·
    refine ⟨98309050005808009316276869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131078733341077345755035825 98309050005808009316276869)
    ·
      refine ⟨18432946876089001746801913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98309050005808009316276869 18432946876089001746801913)
      ·
        refine ⟨13824710157066751310101435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18432946876089001746801913 13824710157066751310101435)
        ·
          refine ⟨20737065235600126965152153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13824710157066751310101435 20737065235600126965152153)
          ·
            refine ⟨15552798926700095223864115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20737065235600126965152153 15552798926700095223864115)
            ·
              refine ⟨23329198390050142835796173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15552798926700095223864115 23329198390050142835796173)
              ·
                refine ⟨8748449396268803563423565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23329198390050142835796173 8748449396268803563423565)
                ·
                  refine ⟨3280668523600801336283837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8748449396268803563423565 3280668523600801336283837)
                  ·
                    refine ⟨1230250696350300501106439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280668523600801336283837 1230250696350300501106439)
                    ·
                      rfl

theorem cell22_3593857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3593857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593857 prefixEnd_3593857 := by exact prefixLift 3593857
  have htrace : WordTrace (prefixWord ++ tailWord_3593857) baseStart_3593857 baseEnd_3593857 := by
    simpa [prefixWord, tailWord_3593857, baseEnd_3593857] using wordTrace_append hprefix tailTrace_3593857
  have hstable : (prefixWord ++ tailWord_3593857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593857).length < 2 ^ (prefixWord ++ tailWord_3593857).sum := by decide
  have hdescent : baseEnd_3593857 < baseStart_3593857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593876 : List Nat := [2, 4, 2, 2, 3, 1, 2, 6]
def baseStart_3593876 : Nat := 118140960795 + 3593876 * 2 ^ 59
def prefixEnd_3593876 : Nat := 4983230072969 + 3 ^ 40 * 3593876 * 2
def baseEnd_3593876 : Nat := 136695244493176753875709

theorem tailTrace_3593876 : CollatzResearch.WordTrace tailWord_3593876 prefixEnd_3593876 136695244493176753875709 := by
  unfold tailWord_3593876
  simp only [CollatzResearch.WordTrace]
  refine ⟨65539713164004255999988741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87386284218672341333318321 65539713164004255999988741)
  ·
    refine ⟨12288696218250797999997889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65539713164004255999988741 12288696218250797999997889)
    ·
      refine ⟨9216522163688098499998417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12288696218250797999997889 9216522163688098499998417)
      ·
        refine ⟨6912391622766073874998813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9216522163688098499998417 6912391622766073874998813)
        ·
          refine ⟨2592146858537277703124555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6912391622766073874998813 2592146858537277703124555)
          ·
            refine ⟨3888220287805916554686833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592146858537277703124555 3888220287805916554686833)
            ·
              refine ⟨2916165215854437416015125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3888220287805916554686833 2916165215854437416015125)
              ·
                refine ⟨136695244493176753875709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2916165215854437416015125 136695244493176753875709)
                ·
                  rfl

theorem cell22_3593876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 6].length) (baseStart_3593876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593876 prefixEnd_3593876 := by exact prefixLift 3593876
  have htrace : WordTrace (prefixWord ++ tailWord_3593876) baseStart_3593876 baseEnd_3593876 := by
    simpa [prefixWord, tailWord_3593876, baseEnd_3593876] using wordTrace_append hprefix tailTrace_3593876
  have hstable : (prefixWord ++ tailWord_3593876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593876).length < 2 ^ (prefixWord ++ tailWord_3593876).sum := by decide
  have hdescent : baseEnd_3593876 < baseStart_3593876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593960 : List Nat := [2, 1, 4, 1, 3, 11]
def baseStart_3593960 : Nat := 118140960795 + 3593960 * 2 ^ 59
def prefixEnd_3593960 : Nat := 4983230072969 + 3 ^ 40 * 3593960 * 2
def baseEnd_3593960 : Nat := 15188715498212871182483

theorem tailTrace_3593960 : CollatzResearch.WordTrace tailWord_3593960 prefixEnd_3593960 15188715498212871182483 := by
  unfold tailWord_3593960
  simp only [CollatzResearch.WordTrace]
  refine ⟨65541245029852097173017667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87388326706469462897356889 65541245029852097173017667)
  ·
    refine ⟨98311867544778145759526501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65541245029852097173017667 98311867544778145759526501)
    ·
      refine ⟨18433475164645902329911219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98311867544778145759526501 18433475164645902329911219)
      ·
        refine ⟨27650212746968853494866829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18433475164645902329911219 27650212746968853494866829)
        ·
          refine ⟨10368829780113320060575061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27650212746968853494866829 10368829780113320060575061)
          ·
            refine ⟨15188715498212871182483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10368829780113320060575061 15188715498212871182483)
            ·
              rfl

theorem cell22_3593960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 11].length) (baseStart_3593960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593960 prefixEnd_3593960 := by exact prefixLift 3593960
  have htrace : WordTrace (prefixWord ++ tailWord_3593960) baseStart_3593960 baseEnd_3593960 := by
    simpa [prefixWord, tailWord_3593960, baseEnd_3593960] using wordTrace_append hprefix tailTrace_3593960
  have hstable : (prefixWord ++ tailWord_3593960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593960).length < 2 ^ (prefixWord ++ tailWord_3593960).sum := by decide
  have hdescent : baseEnd_3593960 < baseStart_3593960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3593962 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3593962 : Nat := 118140960795 + 3593962 * 2 ^ 59
def prefixEnd_3593962 : Nat := 4983230072969 + 3 ^ 40 * 3593962 * 2
def baseEnd_3593962 : Nat := 1230286639996115227231117

theorem tailTrace_3593962 : CollatzResearch.WordTrace tailWord_3593962 prefixEnd_3593962 1230286639996115227231117 := by
  unfold tailWord_3593962
  simp only [CollatzResearch.WordTrace]
  refine ⟨32770640751424237171902035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87388375337131299125072093 32770640751424237171902035)
  ·
    refine ⟨49155961127136355757853053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32770640751424237171902035 49155961127136355757853053)
    ·
      refine ⟨18433485422676133409194895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49155961127136355757853053 18433485422676133409194895)
      ·
        refine ⟨27650228134014200113792343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18433485422676133409194895 27650228134014200113792343)
        ·
          refine ⟨41475342201021300170688515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27650228134014200113792343 41475342201021300170688515)
          ·
            refine ⟨62213013301531950256032773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41475342201021300170688515 62213013301531950256032773)
            ·
              refine ⟨11664939994037240673006145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62213013301531950256032773 11664939994037240673006145)
              ·
                refine ⟨8748704995527930504754609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11664939994037240673006145 8748704995527930504754609)
                ·
                  refine ⟨6561528746645947878565957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8748704995527930504754609 6561528746645947878565957)
                  ·
                    refine ⟨1230286639996115227231117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6561528746645947878565957 1230286639996115227231117)
                    ·
                      rfl

theorem cell22_3593962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3593962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3593962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3593962 prefixEnd_3593962 := by exact prefixLift 3593962
  have htrace : WordTrace (prefixWord ++ tailWord_3593962) baseStart_3593962 baseEnd_3593962 := by
    simpa [prefixWord, tailWord_3593962, baseEnd_3593962] using wordTrace_append hprefix tailTrace_3593962
  have hstable : (prefixWord ++ tailWord_3593962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3593962).length < 2 ^ (prefixWord ++ tailWord_3593962).sum := by decide
  have hdescent : baseEnd_3593962 < baseStart_3593962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3593962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594060 : List Nat := [2, 2, 1, 3, 5, 1, 1, 3, 1, 3]
def baseStart_3594060 : Nat := 118140960795 + 3594060 * 2 ^ 59
def prefixEnd_3594060 : Nat := 4983230072969 + 3 ^ 40 * 3594060 * 2
def baseEnd_3594060 : Nat := 1230320187398875638280817

theorem tailTrace_3594060 : CollatzResearch.WordTrace tailWord_3594060 prefixEnd_3594060 1230320187398875638280817 := by
  unfold tailWord_3594060
  simp only [CollatzResearch.WordTrace]
  refine ⟨65543068679670955712337817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87390758239561274283117089 65543068679670955712337817)
  ·
    refine ⟨49157301509753216784253363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65543068679670955712337817 49157301509753216784253363)
    ·
      refine ⟨73735952264629825176380045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49157301509753216784253363 73735952264629825176380045)
      ·
        refine ⟨27650982099236184441142517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73735952264629825176380045 27650982099236184441142517)
        ·
          refine ⟨2592279571803392291357111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27650982099236184441142517 2592279571803392291357111)
          ·
            refine ⟨3888419357705088437035667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592279571803392291357111 3888419357705088437035667)
            ·
              refine ⟨5832629036557632655553501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888419357705088437035667 5832629036557632655553501)
              ·
                refine ⟨2187235888709112245832563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5832629036557632655553501 2187235888709112245832563)
                ·
                  refine ⟨3280853833063668368748845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187235888709112245832563 3280853833063668368748845)
                  ·
                    refine ⟨1230320187398875638280817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280853833063668368748845 1230320187398875638280817)
                    ·
                      rfl

theorem cell22_3594060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 3].length) (baseStart_3594060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594060 prefixEnd_3594060 := by exact prefixLift 3594060
  have htrace : WordTrace (prefixWord ++ tailWord_3594060) baseStart_3594060 baseEnd_3594060 := by
    simpa [prefixWord, tailWord_3594060, baseEnd_3594060] using wordTrace_append hprefix tailTrace_3594060
  have hstable : (prefixWord ++ tailWord_3594060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594060).length < 2 ^ (prefixWord ++ tailWord_3594060).sum := by decide
  have hdescent : baseEnd_3594060 < baseStart_3594060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594069 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3594069 : Nat := 118140960795 + 3594069 * 2 ^ 59
def prefixEnd_3594069 : Nat := 4983230072969 + 3 ^ 40 * 3594069 * 2
def baseEnd_3594069 : Nat := 1230323268282802614805789

theorem tailTrace_3594069 : CollatzResearch.WordTrace tailWord_3594069 prefixEnd_3594069 1230323268282802614805789 := by
  unfold tailWord_3594069
  simp only [CollatzResearch.WordTrace]
  refine ⟨131086465616309305961753261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87390977077539537307835507 131086465616309305961753261)
  ·
    refine ⟨49157424606115989735657473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131086465616309305961753261 49157424606115989735657473)
    ·
      refine ⟨36868068454586992301743105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49157424606115989735657473 36868068454586992301743105)
      ·
        refine ⟨27651051340940244226307329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36868068454586992301743105 27651051340940244226307329)
        ·
          refine ⟨20738288505705183169730497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27651051340940244226307329 20738288505705183169730497)
          ·
            refine ⟨15553716379278887377297873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20738288505705183169730497 15553716379278887377297873)
            ·
              refine ⟨11665287284459165532973405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15553716379278887377297873 11665287284459165532973405)
              ·
                refine ⟨4374482731672187074865027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11665287284459165532973405 4374482731672187074865027)
                ·
                  refine ⟨6561724097508280612297541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374482731672187074865027 6561724097508280612297541)
                  ·
                    refine ⟨1230323268282802614805789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6561724097508280612297541 1230323268282802614805789)
                    ·
                      rfl

theorem cell22_3594069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3594069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594069 prefixEnd_3594069 := by exact prefixLift 3594069
  have htrace : WordTrace (prefixWord ++ tailWord_3594069) baseStart_3594069 baseEnd_3594069 := by
    simpa [prefixWord, tailWord_3594069, baseEnd_3594069] using wordTrace_append hprefix tailTrace_3594069
  have hstable : (prefixWord ++ tailWord_3594069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594069).length < 2 ^ (prefixWord ++ tailWord_3594069).sum := by decide
  have hdescent : baseEnd_3594069 < baseStart_3594069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594090 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 5]
def baseStart_3594090 : Nat := 118140960795 + 3594090 * 2 ^ 59
def prefixEnd_3594090 : Nat := 4983230072969 + 3 ^ 40 * 3594090 * 2
def baseEnd_3594090 : Nat := 410110152337321853343575

theorem tailTrace_3594090 : CollatzResearch.WordTrace tailWord_3594090 prefixEnd_3594090 410110152337321853343575 := by
  unfold tailWord_3594090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32771807887308306637066931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87391487699488817698845149 32771807887308306637066931)
  ·
    refine ⟨49157711830962459955600397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32771807887308306637066931 49157711830962459955600397)
    ·
      refine ⟨18434141936610922483350149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49157711830962459955600397 18434141936610922483350149)
      ·
        refine ⟨3456401613114547965628153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18434141936610922483350149 3456401613114547965628153)
        ·
          refine ⟨2592301209835910974221115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3456401613114547965628153 2592301209835910974221115)
          ·
            refine ⟨3888451814753866461331673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592301209835910974221115 3888451814753866461331673)
            ·
              refine ⟨2916338861065399845998755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3888451814753866461331673 2916338861065399845998755)
              ·
                refine ⟨4374508291598099768998133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2916338861065399845998755 4374508291598099768998133)
                ·
                  refine ⟨410110152337321853343575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4374508291598099768998133 410110152337321853343575)
                  ·
                    rfl

theorem cell22_3594090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_3594090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594090 prefixEnd_3594090 := by exact prefixLift 3594090
  have htrace : WordTrace (prefixWord ++ tailWord_3594090) baseStart_3594090 baseEnd_3594090 := by
    simpa [prefixWord, tailWord_3594090, baseEnd_3594090] using wordTrace_append hprefix tailTrace_3594090
  have hstable : (prefixWord ++ tailWord_3594090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594090).length < 2 ^ (prefixWord ++ tailWord_3594090).sum := by decide
  have hdescent : baseEnd_3594090 < baseStart_3594090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594097 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 4, 4]
def baseStart_3594097 : Nat := 118140960795 + 3594097 * 2 ^ 59
def prefixEnd_3594097 : Nat := 4983230072969 + 3 ^ 40 * 3594097 * 2
def baseEnd_3594097 : Nat := 1230332853255019875105703

theorem tailTrace_3594097 : CollatzResearch.WordTrace tailWord_3594097 prefixEnd_3594097 1230332853255019875105703 := by
  unfold tailWord_3594097
  simp only [CollatzResearch.WordTrace]
  refine ⟨131087486860207866743772545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87391657906805244495848363 131087486860207866743772545)
  ·
    refine ⟨98315615145155900057829409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131087486860207866743772545 98315615145155900057829409)
    ·
      refine ⟨73736711358866925043372057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98315615145155900057829409 73736711358866925043372057)
      ·
        refine ⟨55302533519150193782529043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73736711358866925043372057 55302533519150193782529043)
        ·
          refine ⟨82953800278725290673793565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55302533519150193782529043 82953800278725290673793565)
          ·
            refine ⟨31107675104521984002672587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82953800278725290673793565 31107675104521984002672587)
            ·
              refine ⟨46661512656782976004008881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31107675104521984002672587 46661512656782976004008881)
              ·
                refine ⟨34996134492587232003006661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46661512656782976004008881 34996134492587232003006661)
                ·
                  refine ⟨6561775217360106000563749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34996134492587232003006661 6561775217360106000563749)
                  ·
                    refine ⟨1230332853255019875105703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6561775217360106000563749 1230332853255019875105703)
                    ·
                      rfl

theorem cell22_3594097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_3594097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594097 prefixEnd_3594097 := by exact prefixLift 3594097
  have htrace : WordTrace (prefixWord ++ tailWord_3594097) baseStart_3594097 baseEnd_3594097 := by
    simpa [prefixWord, tailWord_3594097, baseEnd_3594097] using wordTrace_append hprefix tailTrace_3594097
  have hstable : (prefixWord ++ tailWord_3594097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594097).length < 2 ^ (prefixWord ++ tailWord_3594097).sum := by decide
  have hdescent : baseEnd_3594097 < baseStart_3594097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594144 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 3, 3]
def baseStart_3594144 : Nat := 118140960795 + 3594144 * 2 ^ 59
def prefixEnd_3594144 : Nat := 4983230072969 + 3 ^ 40 * 3594144 * 2
def baseEnd_3594144 : Nat := 1230348942315527419180559

theorem tailTrace_3594144 : CollatzResearch.WordTrace tailWord_3594144 prefixEnd_3594144 1230348942315527419180559 := by
  unfold tailWord_3594144
  simp only [CollatzResearch.WordTrace]
  refine ⟨65544600545518796885366743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87392800727358395847155657 65544600545518796885366743)
  ·
    refine ⟨98316900818278195328050115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65544600545518796885366743 98316900818278195328050115)
    ·
      refine ⟨147475351227417292992075173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98316900818278195328050115 147475351227417292992075173)
      ·
        refine ⟨27651628355140742436014095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147475351227417292992075173 27651628355140742436014095)
        ·
          refine ⟨41477442532711113654021143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27651628355140742436014095 41477442532711113654021143)
          ·
            refine ⟨62216163799066670481031715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41477442532711113654021143 62216163799066670481031715)
            ·
              refine ⟨93324245698600005721547573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62216163799066670481031715 93324245698600005721547573)
              ·
                refine ⟨8749148034243750536395085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93324245698600005721547573 8749148034243750536395085)
                ·
                  refine ⟨3280930512841406451148157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8749148034243750536395085 3280930512841406451148157)
                  ·
                    refine ⟨1230348942315527419180559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280930512841406451148157 1230348942315527419180559)
                    ·
                      rfl

theorem cell22_3594144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_3594144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594144 prefixEnd_3594144 := by exact prefixLift 3594144
  have htrace : WordTrace (prefixWord ++ tailWord_3594144) baseStart_3594144 baseEnd_3594144 := by
    simpa [prefixWord, tailWord_3594144, baseEnd_3594144] using wordTrace_append hprefix tailTrace_3594144
  have hstable : (prefixWord ++ tailWord_3594144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594144).length < 2 ^ (prefixWord ++ tailWord_3594144).sum := by decide
  have hdescent : baseEnd_3594144 < baseStart_3594144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594146 : List Nat := [3, 3, 1, 2, 3, 2, 1, 7]
def baseStart_3594146 : Nat := 118140960795 + 3594146 * 2 ^ 59
def prefixEnd_3594146 : Nat := 4983230072969 + 3 ^ 40 * 3594146 * 2
def baseEnd_3594146 : Nat := 136705514106266675625617

theorem tailTrace_3594146 : CollatzResearch.WordTrace tailWord_3594146 prefixEnd_3594146 136705514106266675625617 := by
  unfold tailWord_3594146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32772318509257587028076573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87392849358020232074870861 32772318509257587028076573)
  ·
    refine ⟨12289619440971595135528715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32772318509257587028076573 12289619440971595135528715)
    ·
      refine ⟨18434429161457392703293073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12289619440971595135528715 18434429161457392703293073)
      ·
        refine ⟨13825821871093044527469805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18434429161457392703293073 13825821871093044527469805)
        ·
          refine ⟨5184683201659891697801177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13825821871093044527469805 5184683201659891697801177)
          ·
            refine ⟨3888512401244918773350883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5184683201659891697801177 3888512401244918773350883)
            ·
              refine ⟨5832768601867378160026325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888512401244918773350883 5832768601867378160026325)
              ·
                refine ⟨136705514106266675625617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5832768601867378160026325 136705514106266675625617)
                ·
                  rfl

theorem cell22_3594146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_3594146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594146 prefixEnd_3594146 := by exact prefixLift 3594146
  have htrace : WordTrace (prefixWord ++ tailWord_3594146) baseStart_3594146 baseEnd_3594146 := by
    simpa [prefixWord, tailWord_3594146, baseEnd_3594146] using wordTrace_append hprefix tailTrace_3594146
  have hstable : (prefixWord ++ tailWord_3594146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594146).length < 2 ^ (prefixWord ++ tailWord_3594146).sum := by decide
  have hdescent : baseEnd_3594146 < baseStart_3594146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594161 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 3, 3]
def baseStart_3594161 : Nat := 118140960795 + 3594161 * 2 ^ 59
def prefixEnd_3594161 : Nat := 4983230072969 + 3 ^ 40 * 3594161 * 2
def baseEnd_3594161 : Nat := 1230354761762945041505507

theorem tailTrace_3594161 : CollatzResearch.WordTrace tailWord_3594161 prefixEnd_3594161 1230354761762945041505507 := by
  unfold tailWord_3594161
  simp only [CollatzResearch.WordTrace]
  refine ⟨131089821131976005674102337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87393214087984003782734891 131089821131976005674102337)
  ·
    refine ⟨98317365848982004255576753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131089821131976005674102337 98317365848982004255576753)
    ·
      refine ⟨73738024386736503191682565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98317365848982004255576753 73738024386736503191682565)
      ·
        refine ⟨13825879572513094348440481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73738024386736503191682565 13825879572513094348440481)
        ·
          refine ⟨10369409679384820761330361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13825879572513094348440481 10369409679384820761330361)
          ·
            refine ⟨7777057259538615570997771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10369409679384820761330361 7777057259538615570997771)
            ·
              refine ⟨11665585889307923356496657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777057259538615570997771 11665585889307923356496657)
              ·
                refine ⟨8749189416980942517372493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11665585889307923356496657 8749189416980942517372493)
                ·
                  refine ⟨3280946031367853444014685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8749189416980942517372493 3280946031367853444014685)
                  ·
                    refine ⟨1230354761762945041505507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3280946031367853444014685 1230354761762945041505507)
                    ·
                      rfl

theorem cell22_3594161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 3, 3].length) (baseStart_3594161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594161 prefixEnd_3594161 := by exact prefixLift 3594161
  have htrace : WordTrace (prefixWord ++ tailWord_3594161) baseStart_3594161 baseEnd_3594161 := by
    simpa [prefixWord, tailWord_3594161, baseEnd_3594161] using wordTrace_append hprefix tailTrace_3594161
  have hstable : (prefixWord ++ tailWord_3594161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594161).length < 2 ^ (prefixWord ++ tailWord_3594161).sum := by decide
  have hdescent : baseEnd_3594161 < baseStart_3594161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594238 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3594238 : Nat := 118140960795 + 3594238 * 2 ^ 59
def prefixEnd_3594238 : Nat := 4983230072969 + 3 ^ 40 * 3594238 * 2
def baseEnd_3594238 : Nat := 1230381120436542507330271

theorem tailTrace_3594238 : CollatzResearch.WordTrace tailWord_3594238 prefixEnd_3594238 1230381120436542507330271 := by
  unfold tailWord_3594238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16386578694087130978081921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87395086368464698549770245 16386578694087130978081921)
  ·
    refine ⟨12289934020565348233561441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16386578694087130978081921 12289934020565348233561441)
    ·
      refine ⟨9217450515424011175171081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12289934020565348233561441 9217450515424011175171081)
      ·
        refine ⟨6913087886568008381378311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9217450515424011175171081 6913087886568008381378311)
        ·
          refine ⟨10369631829852012572067467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6913087886568008381378311 10369631829852012572067467)
          ·
            refine ⟨15554447744778018858101201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10369631829852012572067467 15554447744778018858101201)
            ·
              refine ⟨11665835808583514143575901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15554447744778018858101201 11665835808583514143575901)
              ·
                refine ⟨4374688428218817803840963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11665835808583514143575901 4374688428218817803840963)
                ·
                  refine ⟨6562032642328226705761445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4374688428218817803840963 6562032642328226705761445)
                  ·
                    refine ⟨1230381120436542507330271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6562032642328226705761445 1230381120436542507330271)
                    ·
                      rfl

theorem cell22_3594238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3594238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594238 prefixEnd_3594238 := by exact prefixLift 3594238
  have htrace : WordTrace (prefixWord ++ tailWord_3594238) baseStart_3594238 baseEnd_3594238 := by
    simpa [prefixWord, tailWord_3594238, baseEnd_3594238] using wordTrace_append hprefix tailTrace_3594238
  have hstable : (prefixWord ++ tailWord_3594238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594238).length < 2 ^ (prefixWord ++ tailWord_3594238).sum := by decide
  have hdescent : baseEnd_3594238 < baseStart_3594238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594246 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3594246 : Nat := 118140960795 + 3594246 * 2 ^ 59
def prefixEnd_3594246 : Nat := 4983230072969 + 3 ^ 40 * 3594246 * 2
def baseEnd_3594246 : Nat := 1230383859000033153130247

theorem tailTrace_3594246 : CollatzResearch.WordTrace tailWord_3594246 prefixEnd_3594246 1230383859000033153130247 := by
  unfold tailWord_3594246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096653791770877037217081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87395280891112043460631061 4096653791770877037217081)
  ·
    refine ⟨3072490343828157777912811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4096653791770877037217081 3072490343828157777912811)
    ·
      refine ⟨4608735515742236666869217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3072490343828157777912811 4608735515742236666869217)
      ·
        refine ⟨3456551636806677500151913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4608735515742236666869217 3456551636806677500151913)
        ·
          refine ⟨2592413727605008125113935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3456551636806677500151913 2592413727605008125113935)
          ·
            refine ⟨3888620591407512187670903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592413727605008125113935 3888620591407512187670903)
            ·
              refine ⟨5832930887111268281506355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888620591407512187670903 5832930887111268281506355)
              ·
                refine ⟨8749396330666902422259533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5832930887111268281506355 8749396330666902422259533)
                ·
                  refine ⟨3281023624000088408347325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8749396330666902422259533 3281023624000088408347325)
                  ·
                    refine ⟨1230383859000033153130247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3281023624000088408347325 1230383859000033153130247)
                    ·
                      rfl

theorem cell22_3594246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3594246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594246 prefixEnd_3594246 := by exact prefixLift 3594246
  have htrace : WordTrace (prefixWord ++ tailWord_3594246) baseStart_3594246 baseEnd_3594246 := by
    simpa [prefixWord, tailWord_3594246, baseEnd_3594246] using wordTrace_append hprefix tailTrace_3594246
  have hstable : (prefixWord ++ tailWord_3594246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594246).length < 2 ^ (prefixWord ++ tailWord_3594246).sum := by decide
  have hdescent : baseEnd_3594246 < baseStart_3594246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594251 : List Nat := [1, 1, 1, 1, 6, 1, 2, 4, 2, 3]
def baseStart_3594251 : Nat := 118140960795 + 3594251 * 2 ^ 59
def prefixEnd_3594251 : Nat := 4983230072969 + 3 ^ 40 * 3594251 * 2
def baseEnd_3594251 : Nat := 1230385570602214806755231

theorem tailTrace_3594251 : CollatzResearch.WordTrace tailWord_3594251 prefixEnd_3594251 1230385570602214806755231 := by
  unfold tailWord_3594251
  simp only [CollatzResearch.WordTrace]
  refine ⟨131093103701649951044878607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87395402467766634029919071 131093103701649951044878607)
  ·
    refine ⟨196639655552474926567317911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131093103701649951044878607 196639655552474926567317911)
    ·
      refine ⟨294959483328712389850976867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196639655552474926567317911 294959483328712389850976867)
      ·
        refine ⟨442439224993068584776465301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294959483328712389850976867 442439224993068584776465301)
        ·
          refine ⟨20739338671550089911396811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 442439224993068584776465301 20739338671550089911396811)
          ·
            refine ⟨31109008007325134867095217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20739338671550089911396811 31109008007325134867095217)
            ·
              refine ⟨23331756005493851150321413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31109008007325134867095217 23331756005493851150321413)
              ·
                refine ⟨4374704251030097090685265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23331756005493851150321413 4374704251030097090685265)
                ·
                  refine ⟨3281028188272572818013949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4374704251030097090685265 3281028188272572818013949)
                  ·
                    refine ⟨1230385570602214806755231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3281028188272572818013949 1230385570602214806755231)
                    ·
                      rfl

theorem cell22_3594251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 3].length) (baseStart_3594251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594251 prefixEnd_3594251 := by exact prefixLift 3594251
  have htrace : WordTrace (prefixWord ++ tailWord_3594251) baseStart_3594251 baseEnd_3594251 := by
    simpa [prefixWord, tailWord_3594251, baseEnd_3594251] using wordTrace_append hprefix tailTrace_3594251
  have hstable : (prefixWord ++ tailWord_3594251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594251).length < 2 ^ (prefixWord ++ tailWord_3594251).sum := by decide
  have hdescent : baseEnd_3594251 < baseStart_3594251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594264 : List Nat := [2, 1, 2, 3, 2, 1, 4, 7]
def baseStart_3594264 : Nat := 118140960795 + 3594264 * 2 ^ 59
def prefixEnd_3594264 : Nat := 4983230072969 + 3 ^ 40 * 3594264 * 2
def baseEnd_3594264 : Nat := 136710002307543011797799

theorem tailTrace_3594264 : CollatzResearch.WordTrace tailWord_3594264 prefixEnd_3594264 136710002307543011797799 := by
  unfold tailWord_3594264
  simp only [CollatzResearch.WordTrace]
  refine ⟨65546788925301427132550923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87395718567068569510067897 65546788925301427132550923)
  ·
    refine ⟨98320183387952140698826385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65546788925301427132550923 98320183387952140698826385)
    ·
      refine ⟨73740137540964105524119789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98320183387952140698826385 73740137540964105524119789)
      ·
        refine ⟨27652551577861539571544921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73740137540964105524119789 27652551577861539571544921)
        ·
          refine ⟨20739413683396154678658691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27652551577861539571544921 20739413683396154678658691)
          ·
            refine ⟨31109120525094232017988037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20739413683396154678658691 31109120525094232017988037)
            ·
              refine ⟨5832960098455168503372757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31109120525094232017988037 5832960098455168503372757)
              ·
                refine ⟨136710002307543011797799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5832960098455168503372757 136710002307543011797799)
                ·
                  rfl

theorem cell22_3594264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 7].length) (baseStart_3594264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594264 prefixEnd_3594264 := by exact prefixLift 3594264
  have htrace : WordTrace (prefixWord ++ tailWord_3594264) baseStart_3594264 baseEnd_3594264 := by
    simpa [prefixWord, tailWord_3594264, baseEnd_3594264] using wordTrace_append hprefix tailTrace_3594264
  have hstable : (prefixWord ++ tailWord_3594264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594264).length < 2 ^ (prefixWord ++ tailWord_3594264).sum := by decide
  have hdescent : baseEnd_3594264 < baseStart_3594264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594268 : List Nat := [2, 2, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_3594268 : Nat := 118140960795 + 3594268 * 2 ^ 59
def prefixEnd_3594268 : Nat := 4983230072969 + 3 ^ 40 * 3594268 * 2
def baseEnd_3594268 : Nat := 1230391390049632429080179

theorem tailTrace_3594268 : CollatzResearch.WordTrace tailWord_3594268 prefixEnd_3594268 1230391390049632429080179 := by
  unfold tailWord_3594268
  simp only [CollatzResearch.WordTrace]
  refine ⟨65546861871294181474123729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87395815828392241965498305 65546861871294181474123729)
  ·
    refine ⟨49160146403470636105592797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65546861871294181474123729 49160146403470636105592797)
    ·
      refine ⟨18435054901301488539597299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49160146403470636105592797 18435054901301488539597299)
      ·
        refine ⟨27652582351952232809395949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18435054901301488539597299 27652582351952232809395949)
        ·
          refine ⟨10369718381982087303523481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27652582351952232809395949 10369718381982087303523481)
          ·
            refine ⟨7777288786486565477642611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10369718381982087303523481 7777288786486565477642611)
            ·
              refine ⟨11665933179729848216463917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777288786486565477642611 11665933179729848216463917)
              ·
                refine ⟨4374724942398693081173969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11665933179729848216463917 4374724942398693081173969)
                ·
                  refine ⟨3281043706799019810880477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4374724942398693081173969 3281043706799019810880477)
                  ·
                    refine ⟨1230391390049632429080179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3281043706799019810880477 1230391390049632429080179)
                    ·
                      rfl

theorem cell22_3594268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_3594268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594268 prefixEnd_3594268 := by exact prefixLift 3594268
  have htrace : WordTrace (prefixWord ++ tailWord_3594268) baseStart_3594268 baseEnd_3594268 := by
    simpa [prefixWord, tailWord_3594268, baseEnd_3594268] using wordTrace_append hprefix tailTrace_3594268
  have hstable : (prefixWord ++ tailWord_3594268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594268).length < 2 ^ (prefixWord ++ tailWord_3594268).sum := by decide
  have hdescent : baseEnd_3594268 < baseStart_3594268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594313 : List Nat := [1, 2, 1, 1, 2, 2, 5, 4, 1, 3]
def baseStart_3594313 : Nat := 118140960795 + 3594313 * 2 ^ 59
def prefixEnd_3594313 : Nat := 4983230072969 + 3 ^ 40 * 3594313 * 2
def baseEnd_3594313 : Nat := 1230406794469267311705041

theorem tailTrace_3594313 : CollatzResearch.WordTrace tailWord_3594313 prefixEnd_3594313 1230406794469267311705041 := by
  unfold tailWord_3594313
  simp only [CollatzResearch.WordTrace]
  refine ⟨131095365027425335633635593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87396910018283557089090395 131095365027425335633635593)
  ·
    refine ⟨98321523770569001725226695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131095365027425335633635593 98321523770569001725226695)
    ·
      refine ⟨147482285655853502587840043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98321523770569001725226695 147482285655853502587840043)
      ·
        refine ⟨221223428483780253881760065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147482285655853502587840043 221223428483780253881760065)
        ·
          refine ⟨165917571362835190411320049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221223428483780253881760065 165917571362835190411320049)
          ·
            refine ⟨124438178522126392808490037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165917571362835190411320049 124438178522126392808490037)
            ·
              refine ⟨11666079236449349325795941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124438178522126392808490037 11666079236449349325795941)
              ·
                refine ⟨2187389856834252998586739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11666079236449349325795941 2187389856834252998586739)
                ·
                  refine ⟨3281084785251379497880109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187389856834252998586739 3281084785251379497880109)
                  ·
                    refine ⟨1230406794469267311705041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3281084785251379497880109 1230406794469267311705041)
                    ·
                      rfl

theorem cell22_3594313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 3].length) (baseStart_3594313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594313 prefixEnd_3594313 := by exact prefixLift 3594313
  have htrace : WordTrace (prefixWord ++ tailWord_3594313) baseStart_3594313 baseEnd_3594313 := by
    simpa [prefixWord, tailWord_3594313, baseEnd_3594313] using wordTrace_append hprefix tailTrace_3594313
  have hstable : (prefixWord ++ tailWord_3594313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594313).length < 2 ^ (prefixWord ++ tailWord_3594313).sum := by decide
  have hdescent : baseEnd_3594313 < baseStart_3594313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594334 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3594334 : Nat := 118140960795 + 3594334 * 2 ^ 59
def prefixEnd_3594334 : Nat := 4983230072969 + 3 ^ 40 * 3594334 * 2
def baseEnd_3594334 : Nat := 1230413983198430256929977

theorem tailTrace_3594334 : CollatzResearch.WordTrace tailWord_3594334 prefixEnd_3594334 1230413983198430256929977 := by
  unfold tailWord_3594334
  simp only [CollatzResearch.WordTrace]
  refine ⟨16387016370043657027518757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87397420640232837480100037 16387016370043657027518757)
  ·
    refine ⟨3072565569383185692659767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16387016370043657027518757 3072565569383185692659767)
    ·
      refine ⟨4608848354074778538989651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3072565569383185692659767 4608848354074778538989651)
      ·
        refine ⟨6913272531112167808484477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608848354074778538989651 6913272531112167808484477)
        ·
          refine ⟨2592477199167062928181679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6913272531112167808484477 2592477199167062928181679)
          ·
            refine ⟨3888715798750594392272519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592477199167062928181679 3888715798750594392272519)
            ·
              refine ⟨5833073698125891588408779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3888715798750594392272519 5833073698125891588408779)
              ·
                refine ⟨8749610547188837382613169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833073698125891588408779 8749610547188837382613169)
                ·
                  refine ⟨6562207910391628036959877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8749610547188837382613169 6562207910391628036959877)
                  ·
                    refine ⟨1230413983198430256929977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6562207910391628036959877 1230413983198430256929977)
                    ·
                      rfl

theorem cell22_3594334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3594334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594334 prefixEnd_3594334 := by exact prefixLift 3594334
  have htrace : WordTrace (prefixWord ++ tailWord_3594334) baseStart_3594334 baseEnd_3594334 := by
    simpa [prefixWord, tailWord_3594334, baseEnd_3594334] using wordTrace_append hprefix tailTrace_3594334
  have hstable : (prefixWord ++ tailWord_3594334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594334).length < 2 ^ (prefixWord ++ tailWord_3594334).sum := by decide
  have hdescent : baseEnd_3594334 < baseStart_3594334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594371 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 6]
def baseStart_3594371 : Nat := 118140960795 + 3594371 * 2 ^ 59
def prefixEnd_3594371 : Nat := 4983230072969 + 3 ^ 40 * 3594371 * 2
def baseEnd_3594371 : Nat := 410142216351524831251621

theorem tailTrace_3594371 : CollatzResearch.WordTrace tailWord_3594371 prefixEnd_3594371 410142216351524831251621 := by
  unfold tailWord_3594371
  simp only [CollatzResearch.WordTrace]
  refine ⟨131097480461215211539246967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87398320307476807692831311 131097480461215211539246967)
  ·
    refine ⟨196646220691822817308870451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131097480461215211539246967 196646220691822817308870451)
    ·
      refine ⟨294969331037734225963305677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196646220691822817308870451 294969331037734225963305677)
      ·
        refine ⟨110613499139150334736239629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294969331037734225963305677 110613499139150334736239629)
        ·
          refine ⟨41480062177181375526089861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110613499139150334736239629 41480062177181375526089861)
          ·
            refine ⟨7777511658221507911141849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41480062177181375526089861 7777511658221507911141849)
            ·
              refine ⟨5833133743666130933356387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7777511658221507911141849 5833133743666130933356387)
              ·
                refine ⟨8749700615499196400034581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5833133743666130933356387 8749700615499196400034581)
                ·
                  refine ⟨410142216351524831251621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8749700615499196400034581 410142216351524831251621)
                  ·
                    rfl

theorem cell22_3594371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 6].length) (baseStart_3594371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594371 prefixEnd_3594371 := by exact prefixLift 3594371
  have htrace : WordTrace (prefixWord ++ tailWord_3594371) baseStart_3594371 baseEnd_3594371 := by
    simpa [prefixWord, tailWord_3594371, baseEnd_3594371] using wordTrace_append hprefix tailTrace_3594371
  have hstable : (prefixWord ++ tailWord_3594371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594371).length < 2 ^ (prefixWord ++ tailWord_3594371).sum := by decide
  have hdescent : baseEnd_3594371 < baseStart_3594371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594384 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 3, 6]
def baseStart_3594384 : Nat := 118140960795 + 3594384 * 2 ^ 59
def prefixEnd_3594384 : Nat := 4983230072969 + 3 ^ 40 * 3594384 * 2
def baseEnd_3594384 : Nat := 1230431099220246793179823

theorem tailTrace_3594384 : CollatzResearch.WordTrace tailWord_3594384 prefixEnd_3594384 1230431099220246793179823 := by
  unfold tailWord_3594384
  simp only [CollatzResearch.WordTrace]
  refine ⟨65548977305084057379735103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87398636406778743172980137 65548977305084057379735103)
  ·
    refine ⟨98323465957626086069602655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65548977305084057379735103 98323465957626086069602655)
    ·
      refine ⟨147485198936439129104403983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98323465957626086069602655 147485198936439129104403983)
      ·
        refine ⟨221227798404658693656605975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147485198936439129104403983 221227798404658693656605975)
        ·
          refine ⟨331841697606988040484908963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221227798404658693656605975 331841697606988040484908963)
          ·
            refine ⟨497762546410482060727363445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331841697606988040484908963 497762546410482060727363445)
            ·
              refine ⟨46665238725982693193190323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 497762546410482060727363445 46665238725982693193190323)
              ·
                refine ⟨69997858088974039789785485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46665238725982693193190323 69997858088974039789785485)
                ·
                  refine ⟨26249196783365264921169557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69997858088974039789785485 26249196783365264921169557)
                  ·
                    refine ⟨1230431099220246793179823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26249196783365264921169557 1230431099220246793179823)
                    ·
                      rfl

theorem cell22_3594384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_3594384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594384 prefixEnd_3594384 := by exact prefixLift 3594384
  have htrace : WordTrace (prefixWord ++ tailWord_3594384) baseStart_3594384 baseEnd_3594384 := by
    simpa [prefixWord, tailWord_3594384, baseEnd_3594384] using wordTrace_append hprefix tailTrace_3594384
  have hstable : (prefixWord ++ tailWord_3594384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594384).length < 2 ^ (prefixWord ++ tailWord_3594384).sum := by decide
  have hdescent : baseEnd_3594384 < baseStart_3594384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594401 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3594401 : Nat := 118140960795 + 3594401 * 2 ^ 59
def prefixEnd_3594401 : Nat := 4983230072969 + 3 ^ 40 * 3594401 * 2
def baseEnd_3594401 : Nat := 1230436918667664415504771

theorem tailTrace_3594401 : CollatzResearch.WordTrace tailWord_3594401 prefixEnd_3594401 1230436918667664415504771 := by
  unfold tailWord_3594401
  simp only [CollatzResearch.WordTrace]
  refine ⟨131098574651106526662839057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87399049767404351108559371 131098574651106526662839057)
  ·
    refine ⟨98323930988329894997129293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131098574651106526662839057 98323930988329894997129293)
    ·
      refine ⟨36871474120623710623923485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98323930988329894997129293 36871474120623710623923485)
      ·
        refine ⟨13826802795233891483971307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36871474120623710623923485 13826802795233891483971307)
        ·
          refine ⟨20740204192850837225956961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13826802795233891483971307 20740204192850837225956961)
          ·
            refine ⟨15555153144638127919467721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20740204192850837225956961 15555153144638127919467721)
            ·
              refine ⟨11666364858478595939600791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15555153144638127919467721 11666364858478595939600791)
              ·
                refine ⟨17499547287717893909401187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11666364858478595939600791 17499547287717893909401187)
                ·
                  refine ⟨26249320931576840864101781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17499547287717893909401187 26249320931576840864101781)
                  ·
                    refine ⟨1230436918667664415504771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26249320931576840864101781 1230436918667664415504771)
                    ·
                      rfl

theorem cell22_3594401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3594401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594401 prefixEnd_3594401 := by exact prefixLift 3594401
  have htrace : WordTrace (prefixWord ++ tailWord_3594401) baseStart_3594401 baseEnd_3594401 := by
    simpa [prefixWord, tailWord_3594401, baseEnd_3594401] using wordTrace_append hprefix tailTrace_3594401
  have hstable : (prefixWord ++ tailWord_3594401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594401).length < 2 ^ (prefixWord ++ tailWord_3594401).sum := by decide
  have hdescent : baseEnd_3594401 < baseStart_3594401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594465 : List Nat := [1, 2, 3, 1, 3, 1, 2, 5, 1, 3]
def baseStart_3594465 : Nat := 118140960795 + 3594465 * 2 ^ 59
def prefixEnd_3594465 : Nat := 4983230072969 + 3 ^ 40 * 3594465 * 2
def baseEnd_3594465 : Nat := 1230458827175589581904575

theorem tailTrace_3594465 : CollatzResearch.WordTrace tailWord_3594465 prefixEnd_3594465 1230458827175589581904575 := by
  unfold tailWord_3594465
  simp only [CollatzResearch.WordTrace]
  refine ⟨131100908922874665593168849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87400605948583110395445899 131100908922874665593168849)
  ·
    refine ⟨98325681692155999194876637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131100908922874665593168849 98325681692155999194876637)
    ·
      refine ⟨36872130634558499698078739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98325681692155999194876637 36872130634558499698078739)
      ·
        refine ⟨55308195951837749547118109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36872130634558499698078739 55308195951837749547118109)
        ·
          refine ⟨20740573481939156080169291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55308195951837749547118109 20740573481939156080169291)
          ·
            refine ⟨31110860222908734120253937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20740573481939156080169291 31110860222908734120253937)
            ·
              refine ⟨23333145167181550590190453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31110860222908734120253937 23333145167181550590190453)
              ·
                refine ⟨2187482359423270367830355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23333145167181550590190453 2187482359423270367830355)
                ·
                  refine ⟨3281223539134905551745533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187482359423270367830355 3281223539134905551745533)
                  ·
                    refine ⟨1230458827175589581904575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3281223539134905551745533 1230458827175589581904575)
                    ·
                      rfl

theorem cell22_3594465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_3594465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594465 prefixEnd_3594465 := by exact prefixLift 3594465
  have htrace : WordTrace (prefixWord ++ tailWord_3594465) baseStart_3594465 baseEnd_3594465 := by
    simpa [prefixWord, tailWord_3594465, baseEnd_3594465] using wordTrace_append hprefix tailTrace_3594465
  have hstable : (prefixWord ++ tailWord_3594465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594465).length < 2 ^ (prefixWord ++ tailWord_3594465).sum := by decide
  have hdescent : baseEnd_3594465 < baseStart_3594465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594476 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_3594476 : Nat := 118140960795 + 3594476 * 2 ^ 59
def prefixEnd_3594476 : Nat := 4983230072969 + 3 ^ 40 * 3594476 * 2
def baseEnd_3594476 : Nat := 1230462592700389219879541

theorem tailTrace_3594476 : CollatzResearch.WordTrace tailWord_3594476 prefixEnd_3594476 1230462592700389219879541 := by
  unfold tailWord_3594476
  simp only [CollatzResearch.WordTrace]
  refine ⟨65550655062917407235909641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87400873417223209647879521 65550655062917407235909641)
  ·
    refine ⟨49162991297188055426932231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65550655062917407235909641 49162991297188055426932231)
    ·
      refine ⟨73744486945782083140398347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49162991297188055426932231 73744486945782083140398347)
      ·
        refine ⟨110616730418673124710597521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73744486945782083140398347 110616730418673124710597521)
        ·
          refine ⟨82962547814004843532948141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110616730418673124710597521 82962547814004843532948141)
          ·
            refine ⟨31110955430251816324855553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82962547814004843532948141 31110955430251816324855553)
            ·
              refine ⟨23333216572688862243641665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31110955430251816324855553 23333216572688862243641665)
              ·
                refine ⟨17499912429516646682731249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23333216572688862243641665 17499912429516646682731249)
                ·
                  refine ⟨13124934322137485012048437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17499912429516646682731249 13124934322137485012048437)
                  ·
                    refine ⟨1230462592700389219879541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13124934322137485012048437 1230462592700389219879541)
                    ·
                      rfl

theorem cell22_3594476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_3594476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594476 prefixEnd_3594476 := by exact prefixLift 3594476
  have htrace : WordTrace (prefixWord ++ tailWord_3594476) baseStart_3594476 baseEnd_3594476 := by
    simpa [prefixWord, tailWord_3594476, baseEnd_3594476] using wordTrace_append hprefix tailTrace_3594476
  have hstable : (prefixWord ++ tailWord_3594476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594476).length < 2 ^ (prefixWord ++ tailWord_3594476).sum := by decide
  have hdescent : baseEnd_3594476 < baseStart_3594476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594482 : List Nat := [3, 2, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_3594482 : Nat := 118140960795 + 3594482 * 2 ^ 59
def prefixEnd_3594482 : Nat := 4983230072969 + 3 ^ 40 * 3594482 * 2
def baseEnd_3594482 : Nat := 1230464646623007204229523

theorem tailTrace_3594482 : CollatzResearch.WordTrace tailWord_3594482 prefixEnd_3594482 1230464646623007204229523 := by
  unfold tailWord_3594482
  simp only [CollatzResearch.WordTrace]
  refine ⟨32775382240953269374134425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87401019309208718331025133 32775382240953269374134425)
  ·
    refine ⟨24581536680714952030600819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32775382240953269374134425 24581536680714952030600819)
    ·
      refine ⟨36872305021072428045901229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24581536680714952030600819 36872305021072428045901229)
      ·
        refine ⟨13827114382902160517212961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36872305021072428045901229 13827114382902160517212961)
        ·
          refine ⟨10370335787176620387909721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13827114382902160517212961 10370335787176620387909721)
          ·
            refine ⟨7777751840382465290932291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10370335787176620387909721 7777751840382465290932291)
            ·
              refine ⟨11666627760573697936398437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7777751840382465290932291 11666627760573697936398437)
              ·
                refine ⟨2187492705107568363074707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11666627760573697936398437 2187492705107568363074707)
                ·
                  refine ⟨3281239057661352544612061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187492705107568363074707 3281239057661352544612061)
                  ·
                    refine ⟨1230464646623007204229523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3281239057661352544612061 1230464646623007204229523)
                    ·
                      rfl

theorem cell22_3594482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_3594482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594482 prefixEnd_3594482 := by exact prefixLift 3594482
  have htrace : WordTrace (prefixWord ++ tailWord_3594482) baseStart_3594482 baseEnd_3594482 := by
    simpa [prefixWord, tailWord_3594482, baseEnd_3594482] using wordTrace_append hprefix tailTrace_3594482
  have hstable : (prefixWord ++ tailWord_3594482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594482).length < 2 ^ (prefixWord ++ tailWord_3594482).sum := by decide
  have hdescent : baseEnd_3594482 < baseStart_3594482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594506 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_3594506 : Nat := 118140960795 + 3594506 * 2 ^ 59
def prefixEnd_3594506 : Nat := 4983230072969 + 3 ^ 40 * 3594506 * 2
def baseEnd_3594506 : Nat := 410157620771159713876483

theorem tailTrace_3594506 : CollatzResearch.WordTrace tailWord_3594506 prefixEnd_3594506 410157620771159713876483 := by
  unfold tailWord_3594506
  simp only [CollatzResearch.WordTrace]
  refine ⟨32775601078931532398852843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87401602877150753063607581 32775601078931532398852843)
  ·
    refine ⟨49163401618397298598279265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32775601078931532398852843 49163401618397298598279265)
    ·
      refine ⟨36872551213797973948709449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49163401618397298598279265 36872551213797973948709449)
      ·
        refine ⟨27654413410348480461532087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36872551213797973948709449 27654413410348480461532087)
        ·
          refine ⟨41481620115522720692298131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27654413410348480461532087 41481620115522720692298131)
          ·
            refine ⟨62222430173284081038447197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41481620115522720692298131 62222430173284081038447197)
            ·
              refine ⟨23333411314981530389417699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62222430173284081038447197 23333411314981530389417699)
              ·
                refine ⟨35000116972472295584126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23333411314981530389417699 35000116972472295584126549)
                ·
                  refine ⟨410157620771159713876483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35000116972472295584126549 410157620771159713876483)
                  ·
                    rfl

theorem cell22_3594506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_3594506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594506 prefixEnd_3594506 := by exact prefixLift 3594506
  have htrace : WordTrace (prefixWord ++ tailWord_3594506) baseStart_3594506 baseEnd_3594506 := by
    simpa [prefixWord, tailWord_3594506, baseEnd_3594506] using wordTrace_append hprefix tailTrace_3594506
  have hstable : (prefixWord ++ tailWord_3594506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594506).length < 2 ^ (prefixWord ++ tailWord_3594506).sum := by decide
  have hdescent : baseEnd_3594506 < baseStart_3594506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594508 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_3594508 : Nat := 118140960795 + 3594508 * 2 ^ 59
def prefixEnd_3594508 : Nat := 4983230072969 + 3 ^ 40 * 3594508 * 2
def baseEnd_3594508 : Nat := 1230473546954351803079443

theorem tailTrace_3594508 : CollatzResearch.WordTrace tailWord_3594508 prefixEnd_3594508 1230473546954351803079443 := by
  unfold tailWord_3594508
  simp only [CollatzResearch.WordTrace]
  refine ⟨65551238630859441968492089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87401651507812589291322785 65551238630859441968492089)
  ·
    refine ⟨49163428973144581476369067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65551238630859441968492089 49163428973144581476369067)
    ·
      refine ⟨73745143459716872214553601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49163428973144581476369067 73745143459716872214553601)
      ·
        refine ⟨55308857594787654160915201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73745143459716872214553601 55308857594787654160915201)
        ·
          refine ⟨41481643196090740620686401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55308857594787654160915201 41481643196090740620686401)
          ·
            refine ⟨31111232397068055465514801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41481643196090740620686401 31111232397068055465514801)
            ·
              refine ⟨23333424297801041599136101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31111232397068055465514801 23333424297801041599136101)
              ·
                refine ⟨4375017055837695299838019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23333424297801041599136101 4375017055837695299838019)
                ·
                  refine ⟨6562525583756542949757029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4375017055837695299838019 6562525583756542949757029)
                  ·
                    refine ⟨1230473546954351803079443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6562525583756542949757029 1230473546954351803079443)
                    ·
                      rfl

theorem cell22_3594508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_3594508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594508 prefixEnd_3594508 := by exact prefixLift 3594508
  have htrace : WordTrace (prefixWord ++ tailWord_3594508) baseStart_3594508 baseEnd_3594508 := by
    simpa [prefixWord, tailWord_3594508, baseEnd_3594508] using wordTrace_append hprefix tailTrace_3594508
  have hstable : (prefixWord ++ tailWord_3594508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594508).length < 2 ^ (prefixWord ++ tailWord_3594508).sum := by decide
  have hdescent : baseEnd_3594508 < baseStart_3594508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594523 : List Nat := [1, 1, 1, 1, 1, 1, 7, 5, 4]
def baseStart_3594523 : Nat := 118140960795 + 3594523 * 2 ^ 59
def prefixEnd_3594523 : Nat := 4983230072969 + 3 ^ 40 * 3594523 * 2
def baseEnd_3594523 : Nat := 410159560586965587984799

theorem tailTrace_3594523 : CollatzResearch.WordTrace tailWord_3594523 prefixEnd_3594523 410159560586965587984799 := by
  unfold tailWord_3594523
  simp only [CollatzResearch.WordTrace]
  refine ⟨131103024356664541498780223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87402016237776360999186815 131103024356664541498780223)
  ·
    refine ⟨196654536534996812248170335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131103024356664541498780223 196654536534996812248170335)
    ·
      refine ⟨294981804802495218372255503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196654536534996812248170335 294981804802495218372255503)
      ·
        refine ⟨442472707203742827558383255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294981804802495218372255503 442472707203742827558383255)
        ·
          refine ⟨663709060805614241337574883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442472707203742827558383255 663709060805614241337574883)
          ·
            refine ⟨995563591208421362006362325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663709060805614241337574883 995563591208421362006362325)
            ·
              refine ⟨23333521668947375672024117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 995563591208421362006362325 23333521668947375672024117)
              ·
                refine ⟨2187517656463816469252261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23333521668947375672024117 2187517656463816469252261)
                ·
                  refine ⟨410159560586965587984799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2187517656463816469252261 410159560586965587984799)
                  ·
                    rfl

theorem cell22_3594523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 4].length) (baseStart_3594523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594523 prefixEnd_3594523 := by exact prefixLift 3594523
  have htrace : WordTrace (prefixWord ++ tailWord_3594523) baseStart_3594523 baseEnd_3594523 := by
    simpa [prefixWord, tailWord_3594523, baseEnd_3594523] using wordTrace_append hprefix tailTrace_3594523
  have hstable : (prefixWord ++ tailWord_3594523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594523).length < 2 ^ (prefixWord ++ tailWord_3594523).sum := by decide
  have hdescent : baseEnd_3594523 < baseStart_3594523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594553 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_3594553 : Nat := 118140960795 + 3594553 * 2 ^ 59
def prefixEnd_3594553 : Nat := 4983230072969 + 3 ^ 40 * 3594553 * 2
def baseEnd_3594553 : Nat := 1230488951373986685704305

theorem tailTrace_3594553 : CollatzResearch.WordTrace tailWord_3594553 prefixEnd_3594553 1230488951373986685704305 := by
  unfold tailWord_3594553
  simp only [CollatzResearch.WordTrace]
  refine ⟨131104118546555856622372313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87402745697703904414914875 131104118546555856622372313)
  ·
    refine ⟨98328088909916892466779235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131104118546555856622372313 98328088909916892466779235)
    ·
      refine ⟨147492133364875338700168853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98328088909916892466779235 147492133364875338700168853)
      ·
        refine ⟨6913693751478531501570415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147492133364875338700168853 6913693751478531501570415)
        ·
          refine ⟨10370540627217797252355623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6913693751478531501570415 10370540627217797252355623)
          ·
            refine ⟨15555810940826695878533435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10370540627217797252355623 15555810940826695878533435)
            ·
              refine ⟨23333716411240043817800153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15555810940826695878533435 23333716411240043817800153)
              ·
                refine ⟨17500287308430032863350115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23333716411240043817800153 17500287308430032863350115)
                ·
                  refine ⟨26250430962645049295025173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17500287308430032863350115 26250430962645049295025173)
                  ·
                    refine ⟨1230488951373986685704305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26250430962645049295025173 1230488951373986685704305)
                    ·
                      rfl

theorem cell22_3594553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_3594553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594553 prefixEnd_3594553 := by exact prefixLift 3594553
  have htrace : WordTrace (prefixWord ++ tailWord_3594553) baseStart_3594553 baseEnd_3594553 := by
    simpa [prefixWord, tailWord_3594553, baseEnd_3594553] using wordTrace_append hprefix tailTrace_3594553
  have hstable : (prefixWord ++ tailWord_3594553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594553).length < 2 ^ (prefixWord ++ tailWord_3594553).sum := by decide
  have hdescent : baseEnd_3594553 < baseStart_3594553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594568 : List Nat := [2, 1, 3, 1, 1, 2, 6, 6]
def baseStart_3594568 : Nat := 118140960795 + 3594568 * 2 ^ 59
def prefixEnd_3594568 : Nat := 4983230072969 + 3 ^ 40 * 3594568 * 2
def baseEnd_3594568 : Nat := 136721565131170182953251

theorem tailTrace_3594568 : CollatzResearch.WordTrace tailWord_3594568 prefixEnd_3594568 136721565131170182953251 := by
  unfold tailWord_3594568
  simp only [CollatzResearch.WordTrace]
  refine ⟨65552332820750757092084179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87403110427667676122778905 65552332820750757092084179)
  ·
    refine ⟨98328499231126135638126269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65552332820750757092084179 98328499231126135638126269)
    ·
      refine ⟨36873187211672300864297351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98328499231126135638126269 36873187211672300864297351)
      ·
        refine ⟨55309780817508451296446027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36873187211672300864297351 55309780817508451296446027)
        ·
          refine ⟨82964671226262676944669041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55309780817508451296446027 82964671226262676944669041)
          ·
            refine ⟨62223503419697007708501781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82964671226262676944669041 62223503419697007708501781)
            ·
              refine ⟨2916726722798297236336021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62223503419697007708501781 2916726722798297236336021)
              ·
                refine ⟨136721565131170182953251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2916726722798297236336021 136721565131170182953251)
                ·
                  rfl

theorem cell22_3594568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 6].length) (baseStart_3594568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594568 prefixEnd_3594568 := by exact prefixLift 3594568
  have htrace : WordTrace (prefixWord ++ tailWord_3594568) baseStart_3594568 baseEnd_3594568 := by
    simpa [prefixWord, tailWord_3594568, baseEnd_3594568] using wordTrace_append hprefix tailTrace_3594568
  have hstable : (prefixWord ++ tailWord_3594568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594568).length < 2 ^ (prefixWord ++ tailWord_3594568).sum := by decide
  have hdescent : baseEnd_3594568 < baseStart_3594568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594754 : List Nat := [3, 4, 1, 2, 3, 1, 8]
def baseStart_3594754 : Nat := 118140960795 + 3594754 * 2 ^ 59
def prefixEnd_3594754 : Nat := 4983230072969 + 3 ^ 40 * 3594754 * 2
def baseEnd_3594754 : Nat := 45576213251173672645507

theorem tailTrace_3594754 : CollatzResearch.WordTrace tailWord_3594754 prefixEnd_3594754 45576213251173672645507 := by
  unfold tailWord_3594754
  simp only [CollatzResearch.WordTrace]
  refine ⟨32777862404706916987609829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87407633079218445300292877 32777862404706916987609829)
  ·
    refine ⟨6145849200882546935176843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32777862404706916987609829 6145849200882546935176843)
    ·
      refine ⟨9218773801323820402765265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6145849200882546935176843 9218773801323820402765265)
      ·
        refine ⟨6914080350992865302073949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9218773801323820402765265 6914080350992865302073949)
        ·
          refine ⟨2592780131622324488277731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6914080350992865302073949 2592780131622324488277731)
          ·
            refine ⟨3889170197433486732416597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592780131622324488277731 3889170197433486732416597)
            ·
              refine ⟨45576213251173672645507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3889170197433486732416597 45576213251173672645507)
              ·
                rfl

theorem cell22_3594754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 8].length) (baseStart_3594754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594754 prefixEnd_3594754 := by exact prefixLift 3594754
  have htrace : WordTrace (prefixWord ++ tailWord_3594754) baseStart_3594754 baseEnd_3594754 := by
    simpa [prefixWord, tailWord_3594754, baseEnd_3594754] using wordTrace_append hprefix tailTrace_3594754
  have hstable : (prefixWord ++ tailWord_3594754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594754).length < 2 ^ (prefixWord ++ tailWord_3594754).sum := by decide
  have hdescent : baseEnd_3594754 < baseStart_3594754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594820 : List Nat := [2, 3, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3594820 : Nat := 118140960795 + 3594820 * 2 ^ 59
def prefixEnd_3594820 : Nat := 4983230072969 + 3 ^ 40 * 3594820 * 2
def baseEnd_3594820 : Nat := 1230580350930486989278487

theorem tailTrace_3594820 : CollatzResearch.WordTrace tailWord_3594820 prefixEnd_3594820 1230580350930486989278487 := by
  unfold tailWord_3594820
  simp only [CollatzResearch.WordTrace]
  refine ⟨65556928418294280611170957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87409237891059040814894609 65556928418294280611170957)
  ·
    refine ⟨24583848156860355229189109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65556928418294280611170957 24583848156860355229189109)
    ·
      refine ⟨2304735764705658302736479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24583848156860355229189109 2304735764705658302736479)
      ·
        refine ⟨3457103647058487454104719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2304735764705658302736479 3457103647058487454104719)
        ·
          refine ⟨5185655470587731181157079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457103647058487454104719 5185655470587731181157079)
          ·
            refine ⟨7778483205881596771735619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5185655470587731181157079 7778483205881596771735619)
            ·
              refine ⟨11667724808822395157603429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7778483205881596771735619 11667724808822395157603429)
              ·
                refine ⟨2187698401654199092050643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11667724808822395157603429 2187698401654199092050643)
                ·
                  refine ⟨3281547602481298638075965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2187698401654199092050643 3281547602481298638075965)
                  ·
                    refine ⟨1230580350930486989278487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3281547602481298638075965 1230580350930486989278487)
                    ·
                      rfl

theorem cell22_3594820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3594820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594820 prefixEnd_3594820 := by exact prefixLift 3594820
  have htrace : WordTrace (prefixWord ++ tailWord_3594820) baseStart_3594820 baseEnd_3594820 := by
    simpa [prefixWord, tailWord_3594820, baseEnd_3594820] using wordTrace_append hprefix tailTrace_3594820
  have hstable : (prefixWord ++ tailWord_3594820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594820).length < 2 ^ (prefixWord ++ tailWord_3594820).sum := by decide
  have hdescent : baseEnd_3594820 < baseStart_3594820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594840 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_3594840 : Nat := 118140960795 + 3594840 * 2 ^ 59
def prefixEnd_3594840 : Nat := 4983230072969 + 3 ^ 40 * 3594840 * 2
def baseEnd_3594840 : Nat := 1230587197339213603778425

theorem tailTrace_3594840 : CollatzResearch.WordTrace tailWord_3594840 prefixEnd_3594840 1230587197339213603778425 := by
  unfold tailWord_3594840
  simp only [CollatzResearch.WordTrace]
  refine ⟨65557293148258052319034987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87409724197677403092046649 65557293148258052319034987)
  ·
    refine ⟨98335939722387078478552481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65557293148258052319034987 98335939722387078478552481)
    ·
      refine ⟨73751954791790308858914361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98335939722387078478552481 73751954791790308858914361)
      ·
        refine ⟨55313966093842731644185771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73751954791790308858914361 55313966093842731644185771)
        ·
          refine ⟨82970949140764097466278657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55313966093842731644185771 82970949140764097466278657)
          ·
            refine ⟨62228211855573073099708993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82970949140764097466278657 62228211855573073099708993)
            ·
              refine ⟨46671158891679804824781745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62228211855573073099708993 46671158891679804824781745)
              ·
                refine ⟨35003369168759853618586309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46671158891679804824781745 35003369168759853618586309)
                ·
                  refine ⟨6563131719142472553484933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35003369168759853618586309 6563131719142472553484933)
                  ·
                    refine ⟨1230587197339213603778425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6563131719142472553484933 1230587197339213603778425)
                    ·
                      rfl

theorem cell22_3594840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_3594840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594840 prefixEnd_3594840 := by exact prefixLift 3594840
  have htrace : WordTrace (prefixWord ++ tailWord_3594840) baseStart_3594840 baseEnd_3594840 := by
    simpa [prefixWord, tailWord_3594840, baseEnd_3594840] using wordTrace_append hprefix tailTrace_3594840
  have hstable : (prefixWord ++ tailWord_3594840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594840).length < 2 ^ (prefixWord ++ tailWord_3594840).sum := by decide
  have hdescent : baseEnd_3594840 < baseStart_3594840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3594906 : List Nat := [3, 1, 1, 6, 1, 2, 2, 6]
def baseStart_3594906 : Nat := 118140960795 + 3594906 * 2 ^ 59
def prefixEnd_3594906 : Nat := 4983230072969 + 3 ^ 40 * 3594906 * 2
def baseEnd_3594906 : Nat := 136734421165334603514247

theorem tailTrace_3594906 : CollatzResearch.WordTrace tailWord_3594906 prefixEnd_3594906 136734421165334603514247 := by
  unfold tailWord_3594906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32779248378569249477493143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87411329009517998606648381 32779248378569249477493143)
  ·
    refine ⟨49168872567853874216239715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32779248378569249477493143 49168872567853874216239715)
    ·
      refine ⟨73753308851780811324359573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49168872567853874216239715 73753308851780811324359573)
      ·
        refine ⟨3457186352427225530829355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73753308851780811324359573 3457186352427225530829355)
        ·
          refine ⟨5185779528640838296244033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3457186352427225530829355 5185779528640838296244033)
          ·
            refine ⟨3889334646480628722183025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5185779528640838296244033 3889334646480628722183025)
            ·
              refine ⟨2917000984860471541637269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3889334646480628722183025 2917000984860471541637269)
              ·
                refine ⟨136734421165334603514247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2917000984860471541637269 136734421165334603514247)
                ·
                  rfl

theorem cell22_3594906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 2, 6].length) (baseStart_3594906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3594906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3594906 prefixEnd_3594906 := by exact prefixLift 3594906
  have htrace : WordTrace (prefixWord ++ tailWord_3594906) baseStart_3594906 baseEnd_3594906 := by
    simpa [prefixWord, tailWord_3594906, baseEnd_3594906] using wordTrace_append hprefix tailTrace_3594906
  have hstable : (prefixWord ++ tailWord_3594906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3594906).length < 2 ^ (prefixWord ++ tailWord_3594906).sum := by decide
  have hdescent : baseEnd_3594906 < baseStart_3594906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3594906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
