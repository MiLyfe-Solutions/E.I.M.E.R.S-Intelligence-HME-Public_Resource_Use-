import V185TrunkScan23Chunk1043

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6180451 : List Nat := [1, 1, 1, 5, 1, 3, 1, 3, 1, 6]
def baseStart_6180451 : Nat := 118140960795 + 6180451 * 2 ^ 59
def prefixEnd_6180451 : Nat := 4983230072969 + 3 ^ 40 * 6180451 * 2
def baseEnd_6180451 : Nat := 1057847341520367896913043

theorem tailTrace_6180451 : CollatzResearch.WordTrace tailWord_6180451 prefixEnd_6180451 1057847341520367896913043 := by
  unfold tailWord_6180451
  simp only [CollatzResearch.WordTrace]
  refine ⟨225419566932289038840317207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150279711288192692560211471 225419566932289038840317207)
  ·
    refine ⟨338129350398433558260475811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225419566932289038840317207 338129350398433558260475811)
    ·
      refine ⟨507194025597650337390713717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338129350398433558260475811 507194025597650337390713717)
      ·
        refine ⟨47549439899779719130379411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 507194025597650337390713717 47549439899779719130379411)
        ·
          refine ⟨71324159849669578695569117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47549439899779719130379411 71324159849669578695569117)
          ·
            refine ⟨26746559943626092010838419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71324159849669578695569117 26746559943626092010838419)
            ·
              refine ⟨40119839915439138016257629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26746559943626092010838419 40119839915439138016257629)
              ·
                refine ⟨15044939968289676756096611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40119839915439138016257629 15044939968289676756096611)
                ·
                  refine ⟨22567409952434515134144917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15044939968289676756096611 22567409952434515134144917)
                  ·
                    refine ⟨1057847341520367896913043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22567409952434515134144917 1057847341520367896913043)
                    ·
                      rfl

theorem cell23_6180451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 6].length) (baseStart_6180451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180451 prefixEnd_6180451 := by exact prefixLift 6180451
  have htrace : WordTrace (prefixWord ++ tailWord_6180451) baseStart_6180451 baseEnd_6180451 := by
    simpa [prefixWord, tailWord_6180451, baseEnd_6180451] using wordTrace_append hprefix tailTrace_6180451
  have hstable : (prefixWord ++ tailWord_6180451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180451).length < 2 ^ (prefixWord ++ tailWord_6180451).sum := by decide
  have hdescent : baseEnd_6180451 < baseStart_6180451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180458 : List Nat := [3, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6180458 : Nat := 118140960795 + 6180458 * 2 ^ 59
def prefixEnd_6180458 : Nat := 4983230072969 + 3 ^ 40 * 6180458 * 2
def baseEnd_6180458 : Nat := 3173545618925685163351597

theorem tailTrace_6180458 : CollatzResearch.WordTrace tailWord_6180458 prefixEnd_6180458 3173545618925685163351597 := by
  unfold tailWord_6180458
  simp only [CollatzResearch.WordTrace]
  refine ⟨56354955560815919758955507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150279881495509119357214685 56354955560815919758955507)
  ·
    refine ⟨84532433341223879638433261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56354955560815919758955507 84532433341223879638433261)
    ·
      refine ⟨31699662502958954864412473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84532433341223879638433261 31699662502958954864412473)
      ·
        refine ⟨23774746877219216148309355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31699662502958954864412473 23774746877219216148309355)
        ·
          refine ⟨35662120315828824222464033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23774746877219216148309355 35662120315828824222464033)
          ·
            refine ⟨26746590236871618166848025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35662120315828824222464033 26746590236871618166848025)
            ·
              refine ⟨20059942677653713625136019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26746590236871618166848025 20059942677653713625136019)
              ·
                refine ⟨30089914016480570437704029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20059942677653713625136019 30089914016480570437704029)
                ·
                  refine ⟨11283717756180213914139011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30089914016480570437704029 11283717756180213914139011)
                  ·
                    refine ⟨16925576634270320871208517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11283717756180213914139011 16925576634270320871208517)
                    ·
                      refine ⟨3173545618925685163351597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16925576634270320871208517 3173545618925685163351597)
                      ·
                        rfl

theorem cell23_6180458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6180458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180458 prefixEnd_6180458 := by exact prefixLift 6180458
  have htrace : WordTrace (prefixWord ++ tailWord_6180458) baseStart_6180458 baseEnd_6180458 := by
    simpa [prefixWord, tailWord_6180458, baseEnd_6180458] using wordTrace_append hprefix tailTrace_6180458
  have hstable : (prefixWord ++ tailWord_6180458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180458).length < 2 ^ (prefixWord ++ tailWord_6180458).sum := by decide
  have hdescent : baseEnd_6180458 < baseStart_6180458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180469 : List Nat := [1, 3, 4, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6180469 : Nat := 118140960795 + 6180469 * 2 ^ 59
def prefixEnd_6180469 : Nat := 4983230072969 + 3 ^ 40 * 6180469 * 2
def baseEnd_6180469 : Nat := 3173551267212884620314047

theorem tailTrace_6180469 : CollatzResearch.WordTrace tailWord_6180469 prefixEnd_6180469 3173551267212884620314047 := by
  unfold tailWord_6180469
  simp only [CollatzResearch.WordTrace]
  refine ⟨225420223446223827914472461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150280148964149218609648307 225420223446223827914472461)
  ·
    refine ⟨84532583792333935467927173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225420223446223827914472461 84532583792333935467927173)
    ·
      refine ⟨15849859461062612900236345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84532583792333935467927173 15849859461062612900236345)
      ·
        refine ⟨11887394595796959675177259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15849859461062612900236345 11887394595796959675177259)
        ·
          refine ⟨17831091893695439512765889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11887394595796959675177259 17831091893695439512765889)
          ·
            refine ⟨13373318920271579634574417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17831091893695439512765889 13373318920271579634574417)
            ·
              refine ⟨10029989190203684725930813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13373318920271579634574417 10029989190203684725930813)
              ·
                refine ⟨3761245946326381772224055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10029989190203684725930813 3761245946326381772224055)
                ·
                  refine ⟨5641868919489572658336083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761245946326381772224055 5641868919489572658336083)
                  ·
                    refine ⟨8462803379234358987504125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5641868919489572658336083 8462803379234358987504125)
                    ·
                      refine ⟨3173551267212884620314047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462803379234358987504125 3173551267212884620314047)
                      ·
                        rfl

theorem cell23_6180469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6180469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180469 prefixEnd_6180469 := by exact prefixLift 6180469
  have htrace : WordTrace (prefixWord ++ tailWord_6180469) baseStart_6180469 baseEnd_6180469 := by
    simpa [prefixWord, tailWord_6180469, baseEnd_6180469] using wordTrace_append hprefix tailTrace_6180469
  have hstable : (prefixWord ++ tailWord_6180469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180469).length < 2 ^ (prefixWord ++ tailWord_6180469).sum := by decide
  have hdescent : baseEnd_6180469 < baseStart_6180469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180481 : List Nat := [1, 2, 4, 2, 1, 3, 10]
def baseStart_6180481 : Nat := 118140960795 + 6180481 * 2 ^ 59
def prefixEnd_6180481 : Nat := 4983230072969 + 3 ^ 40 * 6180481 * 2
def baseEnd_6180481 : Nat := 39179721345441216955111

theorem tailTrace_6180481 : CollatzResearch.WordTrace tailWord_6180481 prefixEnd_6180481 39179721345441216955111 := by
  unfold tailWord_6180481
  simp only [CollatzResearch.WordTrace]
  refine ⟨225420661122180353963909297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150280440748120235975939531 225420661122180353963909297)
  ·
    refine ⟨169065495841635265472931973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225420661122180353963909297 169065495841635265472931973)
    ·
      refine ⟨31699780470306612276174745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169065495841635265472931973 31699780470306612276174745)
      ·
        refine ⟨23774835352729959207131059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31699780470306612276174745 23774835352729959207131059)
        ·
          refine ⟨35662253029094938810696589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23774835352729959207131059 35662253029094938810696589)
          ·
            refine ⟨13373344885910602054011221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35662253029094938810696589 13373344885910602054011221)
            ·
              refine ⟨39179721345441216955111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13373344885910602054011221 39179721345441216955111)
              ·
                rfl

theorem cell23_6180481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 10].length) (baseStart_6180481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180481 prefixEnd_6180481 := by exact prefixLift 6180481
  have htrace : WordTrace (prefixWord ++ tailWord_6180481) baseStart_6180481 baseEnd_6180481 := by
    simpa [prefixWord, tailWord_6180481, baseEnd_6180481] using wordTrace_append hprefix tailTrace_6180481
  have hstable : (prefixWord ++ tailWord_6180481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180481).length < 2 ^ (prefixWord ++ tailWord_6180481).sum := by decide
  have hdescent : baseEnd_6180481 < baseStart_6180481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180492 : List Nat := [2, 2, 1, 2, 1, 1, 3, 6, 1, 2, 2]
def baseStart_6180492 : Nat := 118140960795 + 6180492 * 2 ^ 59
def prefixEnd_6180492 : Nat := 4983230072969 + 3 ^ 40 * 6180492 * 2
def baseEnd_6180492 : Nat := 3173563077267938030326441

theorem tailTrace_6180492 : CollatzResearch.WordTrace tailWord_6180492 prefixEnd_6180492 3173563077267938030326441 := by
  unfold tailWord_6180492
  simp only [CollatzResearch.WordTrace]
  refine ⟨112710531162570251421279865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150280708216760335228373153 112710531162570251421279865)
  ·
    refine ⟨84532898371927688565959899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112710531162570251421279865 84532898371927688565959899)
    ·
      refine ⟨126799347557891532848939849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84532898371927688565959899 126799347557891532848939849)
      ·
        refine ⟨95099510668418649636704887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126799347557891532848939849 95099510668418649636704887)
        ·
          refine ⟨142649266002627974455057331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95099510668418649636704887 142649266002627974455057331)
          ·
            refine ⟨213973899003941961682585997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142649266002627974455057331 213973899003941961682585997)
            ·
              refine ⟨80240212126478235630969749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213973899003941961682585997 80240212126478235630969749)
              ·
                refine ⟨3761259943428667295201707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80240212126478235630969749 3761259943428667295201707)
                ·
                  refine ⟨5641889915143000942802561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761259943428667295201707 5641889915143000942802561)
                  ·
                    refine ⟨4231417436357250707101921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5641889915143000942802561 4231417436357250707101921)
                    ·
                      refine ⟨3173563077267938030326441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231417436357250707101921 3173563077267938030326441)
                      ·
                        rfl

theorem cell23_6180492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_6180492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180492 prefixEnd_6180492 := by exact prefixLift 6180492
  have htrace : WordTrace (prefixWord ++ tailWord_6180492) baseStart_6180492 baseEnd_6180492 := by
    simpa [prefixWord, tailWord_6180492, baseEnd_6180492] using wordTrace_append hprefix tailTrace_6180492
  have hstable : (prefixWord ++ tailWord_6180492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180492).length < 2 ^ (prefixWord ++ tailWord_6180492).sum := by decide
  have hdescent : baseEnd_6180492 < baseStart_6180492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180520 : List Nat := [2, 1, 7, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6180520 : Nat := 118140960795 + 6180520 * 2 ^ 59
def prefixEnd_6180520 : Nat := 4983230072969 + 3 ^ 40 * 6180520 * 2
def baseEnd_6180520 : Nat := 3173577454726263920776313

theorem tailTrace_6180520 : CollatzResearch.WordTrace tailWord_6180520 prefixEnd_6180520 3173577454726263920776313 := by
  unfold tailWord_6180520
  simp only [CollatzResearch.WordTrace]
  refine ⟨112711041784519531812289507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150281389046026042416386009 112711041784519531812289507)
  ·
    refine ⟨169066562676779297718434261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112711041784519531812289507 169066562676779297718434261)
    ·
      refine ⟨3962497562737014790275803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 169066562676779297718434261 3962497562737014790275803)
      ·
        refine ⟨5943746344105522185413705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3962497562737014790275803 5943746344105522185413705)
        ·
          refine ⟨4457809758079141639060279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5943746344105522185413705 4457809758079141639060279)
          ·
            refine ⟨6686714637118712458590419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457809758079141639060279 6686714637118712458590419)
            ·
              refine ⟨10030071955678068687885629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686714637118712458590419 10030071955678068687885629)
              ·
                refine ⟨3761276983379275757957111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10030071955678068687885629 3761276983379275757957111)
                ·
                  refine ⟨5641915475068913636935667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761276983379275757957111 5641915475068913636935667)
                  ·
                    refine ⟨8462873212603370455403501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5641915475068913636935667 8462873212603370455403501)
                    ·
                      refine ⟨3173577454726263920776313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462873212603370455403501 3173577454726263920776313)
                      ·
                        rfl

theorem cell23_6180520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6180520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180520 prefixEnd_6180520 := by exact prefixLift 6180520
  have htrace : WordTrace (prefixWord ++ tailWord_6180520) baseStart_6180520 baseEnd_6180520 := by
    simpa [prefixWord, tailWord_6180520, baseEnd_6180520] using wordTrace_append hprefix tailTrace_6180520
  have hstable : (prefixWord ++ tailWord_6180520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180520).length < 2 ^ (prefixWord ++ tailWord_6180520).sum := by decide
  have hdescent : baseEnd_6180520 < baseStart_6180520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180525 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_6180525 : Nat := 118140960795 + 6180525 * 2 ^ 59
def prefixEnd_6180525 : Nat := 4983230072969 + 3 ^ 40 * 6180525 * 2
def baseEnd_6180525 : Nat := 3173580022129536401213789

theorem tailTrace_6180525 : CollatzResearch.WordTrace tailWord_6180525 prefixEnd_6180525 3173580022129536401213789 := by
  unfold tailWord_6180525
  simp only [CollatzResearch.WordTrace]
  refine ⟨225422265934020949478511029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150281510622680632985674019 225422265934020949478511029)
  ·
    refine ⟨21133337431314464013610409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225422265934020949478511029 21133337431314464013610409)
    ·
      refine ⟨15850003073485848010207807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21133337431314464013610409 15850003073485848010207807)
      ·
        refine ⟨23775004610228772015311711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15850003073485848010207807 23775004610228772015311711)
        ·
          refine ⟨35662506915343158022967567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23775004610228772015311711 35662506915343158022967567)
          ·
            refine ⟨53493760373014737034451351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35662506915343158022967567 53493760373014737034451351)
            ·
              refine ⟨80240640559522105551677027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53493760373014737034451351 80240640559522105551677027)
              ·
                refine ⟨120360960839283158327515541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80240640559522105551677027 120360960839283158327515541)
                ·
                  refine ⟨5641920039341398046602291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120360960839283158327515541 5641920039341398046602291)
                  ·
                    refine ⟨8462880059012097069903437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5641920039341398046602291 8462880059012097069903437)
                    ·
                      refine ⟨3173580022129536401213789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8462880059012097069903437 3173580022129536401213789)
                      ·
                        rfl

theorem cell23_6180525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_6180525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180525 prefixEnd_6180525 := by exact prefixLift 6180525
  have htrace : WordTrace (prefixWord ++ tailWord_6180525) baseStart_6180525 baseEnd_6180525 := by
    simpa [prefixWord, tailWord_6180525, baseEnd_6180525] using wordTrace_append hprefix tailTrace_6180525
  have hstable : (prefixWord ++ tailWord_6180525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180525).length < 2 ^ (prefixWord ++ tailWord_6180525).sum := by decide
  have hdescent : baseEnd_6180525 < baseStart_6180525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180548 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6180548 : Nat := 118140960795 + 6180548 * 2 ^ 59
def prefixEnd_6180548 : Nat := 4983230072969 + 3 ^ 40 * 6180548 * 2
def baseEnd_6180548 : Nat := 3173591832184589811226183

theorem tailTrace_6180548 : CollatzResearch.WordTrace tailWord_6180548 prefixEnd_6180548 3173591832184589811226183 := by
  unfold tailWord_6180548
  simp only [CollatzResearch.WordTrace]
  refine ⟨112711552406468812203299149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150282069875291749604398865 112711552406468812203299149)
  ·
    refine ⟨42266832152425804576237181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112711552406468812203299149 42266832152425804576237181)
    ·
      refine ⟨15850062057159676716088943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42266832152425804576237181 15850062057159676716088943)
      ·
        refine ⟨23775093085739515074133415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15850062057159676716088943 23775093085739515074133415)
        ·
          refine ⟨35662639628609272611200123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23775093085739515074133415 35662639628609272611200123)
          ·
            refine ⟨53493959442913908916800185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35662639628609272611200123 53493959442913908916800185)
            ·
              refine ⟨40120469582185431687600139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53493959442913908916800185 40120469582185431687600139)
              ·
                refine ⟨60180704373278147531400209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40120469582185431687600139 60180704373278147531400209)
                ·
                  refine ⟨45135528279958610648550157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60180704373278147531400209 45135528279958610648550157)
                  ·
                    refine ⟨16925823104984478993206309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45135528279958610648550157 16925823104984478993206309)
                    ·
                      refine ⟨3173591832184589811226183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16925823104984478993206309 3173591832184589811226183)
                      ·
                        rfl

theorem cell23_6180548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6180548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180548 prefixEnd_6180548 := by exact prefixLift 6180548
  have htrace : WordTrace (prefixWord ++ tailWord_6180548) baseStart_6180548 baseEnd_6180548 := by
    simpa [prefixWord, tailWord_6180548, baseEnd_6180548] using wordTrace_append hprefix tailTrace_6180548
  have hstable : (prefixWord ++ tailWord_6180548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180548).length < 2 ^ (prefixWord ++ tailWord_6180548).sum := by decide
  have hdescent : baseEnd_6180548 < baseStart_6180548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180551 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 5]
def baseStart_6180551 : Nat := 118140960795 + 6180551 * 2 ^ 59
def prefixEnd_6180551 : Nat := 4983230072969 + 3 ^ 40 * 6180551 * 2
def baseEnd_6180551 : Nat := 3173593372626553299488669

theorem tailTrace_6180551 : CollatzResearch.WordTrace tailWord_6180551 prefixEnd_6180551 3173593372626553299488669 := by
  unfold tailWord_6180551
  simp only [CollatzResearch.WordTrace]
  refine ⟨225423214231926755918957507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150282142821284503945971671 225423214231926755918957507)
  ·
    refine ⟨338134821347890133878436261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225423214231926755918957507 338134821347890133878436261)
    ·
      refine ⟨63400279002729400102206799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338134821347890133878436261 63400279002729400102206799)
      ·
        refine ⟨95100418504094100153310199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63400279002729400102206799 95100418504094100153310199)
        ·
          refine ⟨142650627756141150229965299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95100418504094100153310199 142650627756141150229965299)
          ·
            refine ⟨213975941634211725344947949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142650627756141150229965299 213975941634211725344947949)
            ·
              refine ⟨80240978112829397004355481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 213975941634211725344947949 80240978112829397004355481)
              ·
                refine ⟨60180733584622047753266611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80240978112829397004355481 60180733584622047753266611)
                ·
                  refine ⟨90271100376933071629899917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60180733584622047753266611 90271100376933071629899917)
                  ·
                    refine ⟨33851662641349901861212469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90271100376933071629899917 33851662641349901861212469)
                    ·
                      refine ⟨3173593372626553299488669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33851662641349901861212469 3173593372626553299488669)
                      ·
                        rfl

theorem cell23_6180551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_6180551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180551 prefixEnd_6180551 := by exact prefixLift 6180551
  have htrace : WordTrace (prefixWord ++ tailWord_6180551) baseStart_6180551 baseEnd_6180551 := by
    simpa [prefixWord, tailWord_6180551, baseEnd_6180551] using wordTrace_append hprefix tailTrace_6180551
  have hstable : (prefixWord ++ tailWord_6180551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180551).length < 2 ^ (prefixWord ++ tailWord_6180551).sum := by decide
  have hdescent : baseEnd_6180551 < baseStart_6180551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180601 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 5, 7]
def baseStart_6180601 : Nat := 118140960795 + 6180601 * 2 ^ 59
def prefixEnd_6180601 : Nat := 4983230072969 + 3 ^ 40 * 6180601 * 2
def baseEnd_6180601 : Nat := 1057873015553092701287813

theorem tailTrace_6180601 : CollatzResearch.WordTrace tailWord_6180601 prefixEnd_6180601 1057873015553092701287813 := by
  unfold tailWord_6180601
  simp only [CollatzResearch.WordTrace]
  refine ⟨225425037881745614458277657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150283358587830409638851771 225425037881745614458277657)
  ·
    refine ⟨169068778411309210843708243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225425037881745614458277657 169068778411309210843708243)
    ·
      refine ⟨253603167616963816265562365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169068778411309210843708243 253603167616963816265562365)
      ·
        refine ⟨95101187856361431099585887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253603167616963816265562365 95101187856361431099585887)
        ·
          refine ⟨142651781784542146649378831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95101187856361431099585887 142651781784542146649378831)
          ·
            refine ⟨213977672676813219974068247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142651781784542146649378831 213977672676813219974068247)
            ·
              refine ⟨320966509015219829961102371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213977672676813219974068247 320966509015219829961102371)
              ·
                refine ⟨481449763522829744941653557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320966509015219829961102371 481449763522829744941653557)
                ·
                  refine ⟨45135915330265288588280021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 481449763522829744941653557 45135915330265288588280021)
                  ·
                    refine ⟨1057873015553092701287813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45135915330265288588280021 1057873015553092701287813)
                    ·
                      rfl

theorem cell23_6180601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_6180601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180601 prefixEnd_6180601 := by exact prefixLift 6180601
  have htrace : WordTrace (prefixWord ++ tailWord_6180601) baseStart_6180601 baseEnd_6180601 := by
    simpa [prefixWord, tailWord_6180601, baseEnd_6180601] using wordTrace_append hprefix tailTrace_6180601
  have hstable : (prefixWord ++ tailWord_6180601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180601).length < 2 ^ (prefixWord ++ tailWord_6180601).sum := by decide
  have hdescent : baseEnd_6180601 < baseStart_6180601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180688 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3]
def baseStart_6180688 : Nat := 118140960795 + 6180688 * 2 ^ 59
def prefixEnd_6180688 : Nat := 4983230072969 + 3 ^ 40 * 6180688 * 2
def baseEnd_6180688 : Nat := 3173663719476219263475539

theorem tailTrace_6180688 : CollatzResearch.WordTrace tailWord_6180688 prefixEnd_6180688 3173663719476219263475539 := by
  unfold tailWord_6180688
  simp only [CollatzResearch.WordTrace]
  refine ⟨112714105516215214158347359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150285474021620285544463145 112714105516215214158347359)
  ·
    refine ⟨169071158274322821237521039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112714105516215214158347359 169071158274322821237521039)
    ·
      refine ⟨253606737411484231856281559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169071158274322821237521039 253606737411484231856281559)
      ·
        refine ⟨380410106117226347784422339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253606737411484231856281559 380410106117226347784422339)
        ·
          refine ⟨570615159175839521676633509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380410106117226347784422339 570615159175839521676633509)
          ·
            refine ⟨106990342345469910314368783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 570615159175839521676633509 106990342345469910314368783)
            ·
              refine ⟨160485513518204865471553175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106990342345469910314368783 160485513518204865471553175)
              ·
                refine ⟨240728270277307298207329763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160485513518204865471553175 240728270277307298207329763)
                ·
                  refine ⟨361092405415960947310994645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240728270277307298207329763 361092405415960947310994645)
                  ·
                    refine ⟨8463103251936584702601437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 361092405415960947310994645 8463103251936584702601437)
                    ·
                      refine ⟨3173663719476219263475539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8463103251936584702601437 3173663719476219263475539)
                      ·
                        rfl

theorem cell23_6180688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_6180688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180688 prefixEnd_6180688 := by exact prefixLift 6180688
  have htrace : WordTrace (prefixWord ++ tailWord_6180688) baseStart_6180688 baseEnd_6180688 := by
    simpa [prefixWord, tailWord_6180688, baseEnd_6180688] using wordTrace_append hprefix tailTrace_6180688
  have hstable : (prefixWord ++ tailWord_6180688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180688).length < 2 ^ (prefixWord ++ tailWord_6180688).sum := by decide
  have hdescent : baseEnd_6180688 < baseStart_6180688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180725 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_6180725 : Nat := 118140960795 + 6180725 * 2 ^ 59
def prefixEnd_6180725 : Nat := 4983230072969 + 3 ^ 40 * 6180725 * 2
def baseEnd_6180725 : Nat := 1057894239420145206237623

theorem tailTrace_6180725 : CollatzResearch.WordTrace tailWord_6180725 prefixEnd_6180725 1057894239420145206237623 := by
  unfold tailWord_6180725
  simp only [CollatzResearch.WordTrace]
  refine ⟨225429560533296383635791629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150286373688864255757194419 225429560533296383635791629)
  ·
    refine ⟨84536085199986143863421861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225429560533296383635791629 84536085199986143863421861)
    ·
      refine ⟨15850515974997401974391599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84536085199986143863421861 15850515974997401974391599)
      ·
        refine ⟨23775773962496102961587399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15850515974997401974391599 23775773962496102961587399)
        ·
          refine ⟨35663660943744154442381099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23775773962496102961587399 35663660943744154442381099)
          ·
            refine ⟨53495491415616231663571649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35663660943744154442381099 53495491415616231663571649)
            ·
              refine ⟨40121618561712173747678737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53495491415616231663571649 40121618561712173747678737)
              ·
                refine ⟨30091213921284130310759053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40121618561712173747678737 30091213921284130310759053)
                ·
                  refine ⟨11284205220481548866534645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30091213921284130310759053 11284205220481548866534645)
                  ·
                    refine ⟨1057894239420145206237623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11284205220481548866534645 1057894239420145206237623)
                    ·
                      rfl

theorem cell23_6180725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_6180725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180725 prefixEnd_6180725 := by exact prefixLift 6180725
  have htrace : WordTrace (prefixWord ++ tailWord_6180725) baseStart_6180725 baseEnd_6180725 := by
    simpa [prefixWord, tailWord_6180725, baseEnd_6180725] using wordTrace_append hprefix tailTrace_6180725
  have hstable : (prefixWord ++ tailWord_6180725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180725).length < 2 ^ (prefixWord ++ tailWord_6180725).sum := by decide
  have hdescent : baseEnd_6180725 < baseStart_6180725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180745 : List Nat := [1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_6180745 : Nat := 118140960795 + 6180745 * 2 ^ 59
def prefixEnd_6180745 : Nat := 4983230072969 + 3 ^ 40 * 6180745 * 2
def baseEnd_6180745 : Nat := 3173692987873525540462777

theorem tailTrace_6180745 : CollatzResearch.WordTrace tailWord_6180745 prefixEnd_6180745 3173692987873525540462777 := by
  unfold tailWord_6180745
  simp only [CollatzResearch.WordTrace]
  refine ⟨225430289993223927051519689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150286859995482618034346459 225430289993223927051519689)
  ·
    refine ⟨169072717494917945288639767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225430289993223927051519689 169072717494917945288639767)
    ·
      refine ⟨253609076242376917932959651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169072717494917945288639767 253609076242376917932959651)
      ·
        refine ⟨380413614363565376899439477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253609076242376917932959651 380413614363565376899439477)
        ·
          refine ⟨35663776346584254084322451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 380413614363565376899439477 35663776346584254084322451)
          ·
            refine ⟨53495664519876381126483677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35663776346584254084322451 53495664519876381126483677)
            ·
              refine ⟨20060874194953642922431379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53495664519876381126483677 20060874194953642922431379)
              ·
                refine ⟨30091311292430464383647069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20060874194953642922431379 30091311292430464383647069)
                ·
                  refine ⟨11284241734661424143867651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30091311292430464383647069 11284241734661424143867651)
                  ·
                    refine ⟨16926362601992136215801477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11284241734661424143867651 16926362601992136215801477)
                    ·
                      refine ⟨3173692987873525540462777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16926362601992136215801477 3173692987873525540462777)
                      ·
                        rfl

theorem cell23_6180745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_6180745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180745 prefixEnd_6180745 := by exact prefixLift 6180745
  have htrace : WordTrace (prefixWord ++ tailWord_6180745) baseStart_6180745 baseEnd_6180745 := by
    simpa [prefixWord, tailWord_6180745, baseEnd_6180745] using wordTrace_append hprefix tailTrace_6180745
  have hstable : (prefixWord ++ tailWord_6180745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180745).length < 2 ^ (prefixWord ++ tailWord_6180745).sum := by decide
  have hdescent : baseEnd_6180745 < baseStart_6180745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180772 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 2, 4]
def baseStart_6180772 : Nat := 118140960795 + 6180772 * 2 ^ 59
def prefixEnd_6180772 : Nat := 4983230072969 + 3 ^ 40 * 6180772 * 2
def baseEnd_6180772 : Nat := 1057902283950398978275051

theorem tailTrace_6180772 : CollatzResearch.WordTrace tailWord_6180772 prefixEnd_6180772 1057902283950398978275051 := by
  unfold tailWord_6180772
  simp only [CollatzResearch.WordTrace]
  refine ⟨112715637382063055331376285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150287516509417407108501713 112715637382063055331376285)
  ·
    refine ⟨42268364018273645749266107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112715637382063055331376285 42268364018273645749266107)
    ·
      refine ⟨63402546027410468623899161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42268364018273645749266107 63402546027410468623899161)
      ·
        refine ⟨47551909520557851467924371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63402546027410468623899161 47551909520557851467924371)
        ·
          refine ⟨71327864280836777201886557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47551909520557851467924371 71327864280836777201886557)
          ·
            refine ⟨26747949105313791450707459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71327864280836777201886557 26747949105313791450707459)
            ·
              refine ⟨40121923657970687176061189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26747949105313791450707459 40121923657970687176061189)
              ·
                refine ⟨7522860685869503845511473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40121923657970687176061189 7522860685869503845511473)
                ·
                  refine ⟨5642145514402127884133605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7522860685869503845511473 5642145514402127884133605)
                  ·
                    refine ⟨1057902283950398978275051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5642145514402127884133605 1057902283950398978275051)
                    ·
                      rfl

theorem cell23_6180772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_6180772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180772 prefixEnd_6180772 := by exact prefixLift 6180772
  have htrace : WordTrace (prefixWord ++ tailWord_6180772) baseStart_6180772 baseEnd_6180772 := by
    simpa [prefixWord, tailWord_6180772, baseEnd_6180772] using wordTrace_append hprefix tailTrace_6180772
  have hstable : (prefixWord ++ tailWord_6180772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180772).length < 2 ^ (prefixWord ++ tailWord_6180772).sum := by decide
  have hdescent : baseEnd_6180772 < baseStart_6180772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180785 : List Nat := [1, 2, 2, 4, 2, 1, 3, 8]
def baseStart_6180785 : Nat := 118140960795 + 6180785 * 2 ^ 59
def prefixEnd_6180785 : Nat := 4983230072969 + 3 ^ 40 * 6180785 * 2
def baseEnd_6180785 : Nat := 117544945448137236443059

theorem tailTrace_6180785 : CollatzResearch.WordTrace tailWord_6180785 prefixEnd_6180785 117544945448137236443059 := by
  unfold tailWord_6180785
  simp only [CollatzResearch.WordTrace]
  refine ⟨225431748913079013882975809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150287832608719342588650539 225431748913079013882975809)
  ·
    refine ⟨169073811684809260412231857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225431748913079013882975809 169073811684809260412231857)
    ·
      refine ⟨126805358763606945309173893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169073811684809260412231857 126805358763606945309173893)
      ·
        refine ⟨23776004768176302245470105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126805358763606945309173893 23776004768176302245470105)
        ·
          refine ⟨17832003576132226684102579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23776004768176302245470105 17832003576132226684102579)
          ·
            refine ⟨26748005364198340026153869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17832003576132226684102579 26748005364198340026153869)
            ·
              refine ⟨10030502011574377509807701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26748005364198340026153869 10030502011574377509807701)
              ·
                refine ⟨117544945448137236443059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10030502011574377509807701 117544945448137236443059)
                ·
                  rfl

theorem cell23_6180785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 8].length) (baseStart_6180785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180785 prefixEnd_6180785 := by exact prefixLift 6180785
  have htrace : WordTrace (prefixWord ++ tailWord_6180785) baseStart_6180785 baseEnd_6180785 := by
    simpa [prefixWord, tailWord_6180785, baseEnd_6180785] using wordTrace_append hprefix tailTrace_6180785
  have hstable : (prefixWord ++ tailWord_6180785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180785).length < 2 ^ (prefixWord ++ tailWord_6180785).sum := by decide
  have hdescent : baseEnd_6180785 < baseStart_6180785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180795 : List Nat := [1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 3]
def baseStart_6180795 : Nat := 118140960795 + 6180795 * 2 ^ 59
def prefixEnd_6180795 : Nat := 4983230072969 + 3 ^ 40 * 6180795 * 2
def baseEnd_6180795 : Nat := 3173718661906250344837547

theorem tailTrace_6180795 : CollatzResearch.WordTrace tailWord_6180795 prefixEnd_6180795 3173718661906250344837547 := by
  unfold tailWord_6180795
  simp only [CollatzResearch.WordTrace]
  refine ⟨225432113643042785590839839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150288075762028523727226559 225432113643042785590839839)
  ·
    refine ⟨338148170464564178386259759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225432113643042785590839839 338148170464564178386259759)
    ·
      refine ⟨507222255696846267579389639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338148170464564178386259759 507222255696846267579389639)
      ·
        refine ⟨760833383545269401369084459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507222255696846267579389639 760833383545269401369084459)
        ·
          refine ⟨1141250075317904102053626689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760833383545269401369084459 1141250075317904102053626689)
          ·
            refine ⟨855937556488428076540220017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141250075317904102053626689 855937556488428076540220017)
            ·
              refine ⟨641953167366321057405165013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855937556488428076540220017 641953167366321057405165013)
              ·
                refine ⟨15045777360148149782933555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 641953167366321057405165013 15045777360148149782933555)
                ·
                  refine ⟨22568666040222224674400333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15045777360148149782933555 22568666040222224674400333)
                  ·
                    refine ⟨8463249765083334252900125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22568666040222224674400333 8463249765083334252900125)
                    ·
                      refine ⟨3173718661906250344837547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8463249765083334252900125 3173718661906250344837547)
                      ·
                        rfl

theorem cell23_6180795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 3].length) (baseStart_6180795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180795 prefixEnd_6180795 := by exact prefixLift 6180795
  have htrace : WordTrace (prefixWord ++ tailWord_6180795) baseStart_6180795 baseEnd_6180795 := by
    simpa [prefixWord, tailWord_6180795, baseEnd_6180795] using wordTrace_append hprefix tailTrace_6180795
  have hstable : (prefixWord ++ tailWord_6180795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180795).length < 2 ^ (prefixWord ++ tailWord_6180795).sum := by decide
  have hdescent : baseEnd_6180795 < baseStart_6180795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180812 : List Nat := [2, 2, 1, 4, 1, 2, 2, 2, 1, 3, 3]
def baseStart_6180812 : Nat := 118140960795 + 6180812 * 2 ^ 59
def prefixEnd_6180812 : Nat := 4983230072969 + 3 ^ 40 * 6180812 * 2
def baseEnd_6180812 : Nat := 3173727391077376778324969

theorem tailTrace_6180812 : CollatzResearch.WordTrace tailWord_6180812 prefixEnd_6180812 3173727391077376778324969 := by
  unfold tailWord_6180812
  simp only [CollatzResearch.WordTrace]
  refine ⟨112716366841990598747104345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150288489122654131662805793 112716366841990598747104345)
  ·
    refine ⟨84537275131492949060328259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112716366841990598747104345 84537275131492949060328259)
    ·
      refine ⟨126805912697239423590492389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84537275131492949060328259 126805912697239423590492389)
      ·
        refine ⟨23776108630732391923217323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126805912697239423590492389 23776108630732391923217323)
        ·
          refine ⟨35664162946098587884825985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23776108630732391923217323 35664162946098587884825985)
          ·
            refine ⟨26748122209573940913619489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35664162946098587884825985 26748122209573940913619489)
            ·
              refine ⟨20061091657180455685214617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26748122209573940913619489 20061091657180455685214617)
              ·
                refine ⟨15045818742885341763910963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20061091657180455685214617 15045818742885341763910963)
                ·
                  refine ⟨22568728114328012645866445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15045818742885341763910963 22568728114328012645866445)
                  ·
                    refine ⟨8463273042873004742199917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22568728114328012645866445 8463273042873004742199917)
                    ·
                      refine ⟨3173727391077376778324969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8463273042873004742199917 3173727391077376778324969)
                      ·
                        rfl

theorem cell23_6180812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_6180812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180812 prefixEnd_6180812 := by exact prefixLift 6180812
  have htrace : WordTrace (prefixWord ++ tailWord_6180812) baseStart_6180812 baseEnd_6180812 := by
    simpa [prefixWord, tailWord_6180812, baseEnd_6180812] using wordTrace_append hprefix tailTrace_6180812
  have hstable : (prefixWord ++ tailWord_6180812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180812).length < 2 ^ (prefixWord ++ tailWord_6180812).sum := by decide
  have hdescent : baseEnd_6180812 < baseStart_6180812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180869 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 4, 2, 2]
def baseStart_6180869 : Nat := 118140960795 + 6180869 * 2 ^ 59
def prefixEnd_6180869 : Nat := 4983230072969 + 3 ^ 40 * 6180869 * 2
def baseEnd_6180869 : Nat := 3173756659474683055312207

theorem tailTrace_6180869 : CollatzResearch.WordTrace tailWord_6180869 prefixEnd_6180869 3173756659474683055312207 := by
  unfold tailWord_6180869
  simp only [CollatzResearch.WordTrace]
  refine ⟨225434812644774696229033661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150289875096516464152689107 225434812644774696229033661)
  ·
    refine ⟨84538054741790511085887623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225434812644774696229033661 84538054741790511085887623)
    ·
      refine ⟨126807082112685766628831435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84538054741790511085887623 126807082112685766628831435)
      ·
        refine ⟨190210623169028649943247153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126807082112685766628831435 190210623169028649943247153)
        ·
          refine ⟨142657967376771487457435365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190210623169028649943247153 142657967376771487457435365)
          ·
            refine ⟨26748368883144653898269131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142657967376771487457435365 26748368883144653898269131)
            ·
              refine ⟨40122553324716980847403697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26748368883144653898269131 40122553324716980847403697)
              ·
                refine ⟨30091914993537735635552773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40122553324716980847403697 30091914993537735635552773)
                ·
                  refine ⟨5642234061288325431666145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30091914993537735635552773 5642234061288325431666145)
                  ·
                    refine ⟨4231675545966244073749609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5642234061288325431666145 4231675545966244073749609)
                    ·
                      refine ⟨3173756659474683055312207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231675545966244073749609 3173756659474683055312207)
                      ·
                        rfl

theorem cell23_6180869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_6180869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180869 prefixEnd_6180869 := by exact prefixLift 6180869
  have htrace : WordTrace (prefixWord ++ tailWord_6180869) baseStart_6180869 baseEnd_6180869 := by
    simpa [prefixWord, tailWord_6180869, baseEnd_6180869] using wordTrace_append hprefix tailTrace_6180869
  have hstable : (prefixWord ++ tailWord_6180869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180869).length < 2 ^ (prefixWord ++ tailWord_6180869).sum := by decide
  have hdescent : baseEnd_6180869 < baseStart_6180869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180892 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 7]
def baseStart_6180892 : Nat := 118140960795 + 6180892 * 2 ^ 59
def prefixEnd_6180892 : Nat := 4983230072969 + 3 ^ 40 * 6180892 * 2
def baseEnd_6180892 : Nat := 352640941058859607258289

theorem tailTrace_6180892 : CollatzResearch.WordTrace tailWord_6180892 prefixEnd_6180892 352640941058859607258289 := by
  unfold tailWord_6180892
  simp only [CollatzResearch.WordTrace]
  refine ⟨112717825761845685578560465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150290434349127580771413953 112717825761845685578560465)
  ·
    refine ⟨84538369321384264183920349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112717825761845685578560465 84538369321384264183920349)
    ·
      refine ⟨31701888495519099068970131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84538369321384264183920349 31701888495519099068970131)
      ·
        refine ⟨47552832743278648603455197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31701888495519099068970131 47552832743278648603455197)
        ·
          refine ⟨17832312278729493226295699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47552832743278648603455197 17832312278729493226295699)
          ·
            refine ⟨26748468418094239839443549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17832312278729493226295699 26748468418094239839443549)
            ·
              refine ⟨10030675656785339939791331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26748468418094239839443549 10030675656785339939791331)
              ·
                refine ⟨15046013485178009909686997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10030675656785339939791331 15046013485178009909686997)
                ·
                  refine ⟨352640941058859607258289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15046013485178009909686997 352640941058859607258289)
                  ·
                    rfl

theorem cell23_6180892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_6180892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180892 prefixEnd_6180892 := by exact prefixLift 6180892
  have htrace : WordTrace (prefixWord ++ tailWord_6180892) baseStart_6180892 baseEnd_6180892 := by
    simpa [prefixWord, tailWord_6180892, baseEnd_6180892] using wordTrace_append hprefix tailTrace_6180892
  have hstable : (prefixWord ++ tailWord_6180892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180892).length < 2 ^ (prefixWord ++ tailWord_6180892).sum := by decide
  have hdescent : baseEnd_6180892 < baseStart_6180892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6180945 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_6180945 : Nat := 118140960795 + 6180945 * 2 ^ 59
def prefixEnd_6180945 : Nat := 4983230072969 + 3 ^ 40 * 6180945 * 2
def baseEnd_6180945 : Nat := 3173795684004424757961857

theorem tailTrace_6180945 : CollatzResearch.WordTrace tailWord_6180945 prefixEnd_6180945 3173795684004424757961857 := by
  unfold tailWord_6180945
  simp only [CollatzResearch.WordTrace]
  refine ⟨225437584592499361208800289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150291723061666240805866859 225437584592499361208800289)
  ·
    refine ⟨169078188444374520906600217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225437584592499361208800289 169078188444374520906600217)
    ·
      refine ⟨126808641333280890679950163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169078188444374520906600217 126808641333280890679950163)
      ·
        refine ⟨190212961999921336019925245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126808641333280890679950163 190212961999921336019925245)
        ·
          refine ⟨71329860749970501007471967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190212961999921336019925245 71329860749970501007471967)
          ·
            refine ⟨106994791124955751511207951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71329860749970501007471967 106994791124955751511207951)
            ·
              refine ⟨160492186687433627266811927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106994791124955751511207951 160492186687433627266811927)
              ·
                refine ⟨240738280031150440900217891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160492186687433627266811927 240738280031150440900217891)
                ·
                  refine ⟨361107420046725661350326837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240738280031150440900217891 361107420046725661350326837)
                  ·
                    refine ⟨33853820629380530751593141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 361107420046725661350326837 33853820629380530751593141)
                    ·
                      refine ⟨3173795684004424757961857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33853820629380530751593141 3173795684004424757961857)
                      ·
                        rfl

theorem cell23_6180945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_6180945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6180945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6180945 prefixEnd_6180945 := by exact prefixLift 6180945
  have htrace : WordTrace (prefixWord ++ tailWord_6180945) baseStart_6180945 baseEnd_6180945 := by
    simpa [prefixWord, tailWord_6180945, baseEnd_6180945] using wordTrace_append hprefix tailTrace_6180945
  have hstable : (prefixWord ++ tailWord_6180945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6180945).length < 2 ^ (prefixWord ++ tailWord_6180945).sum := by decide
  have hdescent : baseEnd_6180945 < baseStart_6180945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6180945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181002 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6181002 : Nat := 118140960795 + 6181002 * 2 ^ 59
def prefixEnd_6181002 : Nat := 4983230072969 + 3 ^ 40 * 6181002 * 2
def baseEnd_6181002 : Nat := 3173824952401731034949095

theorem tailTrace_6181002 : CollatzResearch.WordTrace tailWord_6181002 prefixEnd_6181002 3173824952401731034949095 := by
  unfold tailWord_6181002
  simp only [CollatzResearch.WordTrace]
  refine ⟨56359915888323214985906315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150293109035528573295750173 56359915888323214985906315)
  ·
    refine ⟨84539873832484822478859473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56359915888323214985906315 84539873832484822478859473)
    ·
      refine ⟨63404905374363616859144605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84539873832484822478859473 63404905374363616859144605)
      ·
        refine ⟨23776839515386356322179227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63404905374363616859144605 23776839515386356322179227)
        ·
          refine ⟨35665259273079534483268841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23776839515386356322179227 35665259273079534483268841)
          ·
            refine ⟨26748944454809650862451631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35665259273079534483268841 26748944454809650862451631)
            ·
              refine ⟨40123416682214476293677447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26748944454809650862451631 40123416682214476293677447)
              ·
                refine ⟨60185125023321714440516171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40123416682214476293677447 60185125023321714440516171)
                ·
                  refine ⟨90277687534982571660774257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60185125023321714440516171 90277687534982571660774257)
                  ·
                    refine ⟨67708265651236928745580693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90277687534982571660774257 67708265651236928745580693)
                    ·
                      refine ⟨3173824952401731034949095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67708265651236928745580693 3173824952401731034949095)
                      ·
                        rfl

theorem cell23_6181002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6181002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181002 prefixEnd_6181002 := by exact prefixLift 6181002
  have htrace : WordTrace (prefixWord ++ tailWord_6181002) baseStart_6181002 baseEnd_6181002 := by
    simpa [prefixWord, tailWord_6181002, baseEnd_6181002] using wordTrace_append hprefix tailTrace_6181002
  have hstable : (prefixWord ++ tailWord_6181002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181002).length < 2 ^ (prefixWord ++ tailWord_6181002).sum := by decide
  have hdescent : baseEnd_6181002 < baseStart_6181002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181016 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 6]
def baseStart_6181016 : Nat := 118140960795 + 6181016 * 2 ^ 59
def prefixEnd_6181016 : Nat := 4983230072969 + 3 ^ 40 * 6181016 * 2
def baseEnd_6181016 : Nat := 352648015681210442241559

theorem tailTrace_6181016 : CollatzResearch.WordTrace tailWord_6181016 prefixEnd_6181016 352648015681210442241559 := by
  unfold tailWord_6181016
  simp only [CollatzResearch.WordTrace]
  refine ⟨112720087087621070167317451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150293449450161426889756601 112720087087621070167317451)
  ·
    refine ⟨169080130631431605250976177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112720087087621070167317451 169080130631431605250976177)
    ·
      refine ⟨126810097973573703938232133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169080130631431605250976177 126810097973573703938232133)
      ·
        refine ⟨23776893370045069488418525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126810097973573703938232133 23776893370045069488418525)
        ·
          refine ⟨8916335013766901058156947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23776893370045069488418525 8916335013766901058156947)
          ·
            refine ⟨13374502520650351587235421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8916335013766901058156947 13374502520650351587235421)
            ·
              refine ⟨5015438445243881845213283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13374502520650351587235421 5015438445243881845213283)
              ·
                refine ⟨7523157667865822767819925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015438445243881845213283 7523157667865822767819925)
                ·
                  refine ⟨352648015681210442241559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7523157667865822767819925 352648015681210442241559)
                  ·
                    rfl

theorem cell23_6181016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 6].length) (baseStart_6181016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181016 prefixEnd_6181016 := by exact prefixLift 6181016
  have htrace : WordTrace (prefixWord ++ tailWord_6181016) baseStart_6181016 baseEnd_6181016 := by
    simpa [prefixWord, tailWord_6181016, baseEnd_6181016] using wordTrace_append hprefix tailTrace_6181016
  have hstable : (prefixWord ++ tailWord_6181016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181016).length < 2 ^ (prefixWord ++ tailWord_6181016).sum := by decide
  have hdescent : baseEnd_6181016 < baseStart_6181016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181029 : List Nat := [1, 3, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_6181029 : Nat := 118140960795 + 6181029 * 2 ^ 59
def prefixEnd_6181029 : Nat := 4983230072969 + 3 ^ 40 * 6181029 * 2
def baseEnd_6181029 : Nat := 1057946272126467476437157

theorem tailTrace_6181029 : CollatzResearch.WordTrace tailWord_6181029 prefixEnd_6181029 1057946272126467476437157 := by
  unfold tailWord_6181029
  simp only [CollatzResearch.WordTrace]
  refine ⟨225440648324195043554858141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150293765549463362369905427 225440648324195043554858141)
  ·
    refine ⟨84540243121573141333071803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225440648324195043554858141 84540243121573141333071803)
    ·
      refine ⟨126810364682359711999607705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84540243121573141333071803 126810364682359711999607705)
      ·
        refine ⟨95107773511769783999705779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126810364682359711999607705 95107773511769783999705779)
        ·
          refine ⟨142661660267654675999558669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95107773511769783999705779 142661660267654675999558669)
          ·
            refine ⟨53498122600370503499834501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142661660267654675999558669 53498122600370503499834501)
            ·
              refine ⟨10030897987569469406218969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53498122600370503499834501 10030897987569469406218969)
              ·
                refine ⟨7523173490677102054664227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10030897987569469406218969 7523173490677102054664227)
                ·
                  refine ⟨11284760236015653081996341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523173490677102054664227 11284760236015653081996341)
                  ·
                    refine ⟨1057946272126467476437157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11284760236015653081996341 1057946272126467476437157)
                    ·
                      rfl

theorem cell23_6181029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_6181029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181029 prefixEnd_6181029 := by exact prefixLift 6181029
  have htrace : WordTrace (prefixWord ++ tailWord_6181029) baseStart_6181029 baseEnd_6181029 := by
    simpa [prefixWord, tailWord_6181029, baseEnd_6181029] using wordTrace_append hprefix tailTrace_6181029
  have hstable : (prefixWord ++ tailWord_6181029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181029).length < 2 ^ (prefixWord ++ tailWord_6181029).sum := by decide
  have hdescent : baseEnd_6181029 < baseStart_6181029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181042 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_6181042 : Nat := 118140960795 + 6181042 * 2 ^ 59
def prefixEnd_6181042 : Nat := 4983230072969 + 3 ^ 40 * 6181042 * 2
def baseEnd_6181042 : Nat := 1057948497209303626149637

theorem tailTrace_6181042 : CollatzResearch.WordTrace tailWord_6181042 prefixEnd_6181042 1057948497209303626149637 := by
  unfold tailWord_6181042
  simp only [CollatzResearch.WordTrace]
  refine ⟨56360280618286986693770345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150294081648765297850054253 56360280618286986693770345)
  ·
    refine ⟨42270210463715240020327759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56360280618286986693770345 42270210463715240020327759)
    ·
      refine ⟨63405315695572860030491639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42270210463715240020327759 63405315695572860030491639)
      ·
        refine ⟨95107973543359290045737459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63405315695572860030491639 95107973543359290045737459)
        ·
          refine ⟨142661960315038935068606189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95107973543359290045737459 142661960315038935068606189)
          ·
            refine ⟨53498235118139600650727321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142661960315038935068606189 53498235118139600650727321)
            ·
              refine ⟨40123676338604700488045491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53498235118139600650727321 40123676338604700488045491)
              ·
                refine ⟨60185514507907050732068237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40123676338604700488045491 60185514507907050732068237)
                ·
                  refine ⟨22569567940465144024525589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60185514507907050732068237 22569567940465144024525589)
                  ·
                    refine ⟨1057948497209303626149637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22569567940465144024525589 1057948497209303626149637)
                    ·
                      rfl

theorem cell23_6181042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_6181042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181042 prefixEnd_6181042 := by exact prefixLift 6181042
  have htrace : WordTrace (prefixWord ++ tailWord_6181042) baseStart_6181042 baseEnd_6181042 := by
    simpa [prefixWord, tailWord_6181042, baseEnd_6181042] using wordTrace_append hprefix tailTrace_6181042
  have hstable : (prefixWord ++ tailWord_6181042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181042).length < 2 ^ (prefixWord ++ tailWord_6181042).sum := by decide
  have hdescent : baseEnd_6181042 < baseStart_6181042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181049 : List Nat := [1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 4]
def baseStart_6181049 : Nat := 118140960795 + 6181049 * 2 ^ 59
def prefixEnd_6181049 : Nat := 4983230072969 + 3 ^ 40 * 6181049 * 2
def baseEnd_6181049 : Nat := 3173849085992492351061379

theorem tailTrace_6181049 : CollatzResearch.WordTrace tailWord_6181049 prefixEnd_6181049 3173849085992492351061379 := by
  unfold tailWord_6181049
  simp only [CollatzResearch.WordTrace]
  refine ⟨225441377784122586970586201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150294251856081724647057467 225441377784122586970586201)
  ·
    refine ⟨169081033338091940227939651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225441377784122586970586201 169081033338091940227939651)
    ·
      refine ⟨253621550007137910341909477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169081033338091940227939651 253621550007137910341909477)
      ·
        refine ⟨47554040626338358189108027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253621550007137910341909477 47554040626338358189108027)
        ·
          refine ⟨71331060939507537283662041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47554040626338358189108027 71331060939507537283662041)
          ·
            refine ⟨53498295704630652962746531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71331060939507537283662041 53498295704630652962746531)
            ·
              refine ⟨80247443556945979444119797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53498295704630652962746531 80247443556945979444119797)
              ·
                refine ⟨7523197833463685572886231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80247443556945979444119797 7523197833463685572886231)
                ·
                  refine ⟨11284796750195528359329347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523197833463685572886231 11284796750195528359329347)
                  ·
                    refine ⟨16927195125293292538994021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11284796750195528359329347 16927195125293292538994021)
                    ·
                      refine ⟨3173849085992492351061379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16927195125293292538994021 3173849085992492351061379)
                      ·
                        rfl

theorem cell23_6181049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_6181049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181049 prefixEnd_6181049 := by exact prefixLift 6181049
  have htrace : WordTrace (prefixWord ++ tailWord_6181049) baseStart_6181049 baseEnd_6181049 := by
    simpa [prefixWord, tailWord_6181049, baseEnd_6181049] using wordTrace_append hprefix tailTrace_6181049
  have hstable : (prefixWord ++ tailWord_6181049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181049).length < 2 ^ (prefixWord ++ tailWord_6181049).sum := by decide
  have hdescent : baseEnd_6181049 < baseStart_6181049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181099 : List Nat := [1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 3]
def baseStart_6181099 : Nat := 118140960795 + 6181099 * 2 ^ 59
def prefixEnd_6181099 : Nat := 4983230072969 + 3 ^ 40 * 6181099 * 2
def baseEnd_6181099 : Nat := 3173874760025217155436149

theorem tailTrace_6181099 : CollatzResearch.WordTrace tailWord_6181099 prefixEnd_6181099 3173874760025217155436149 := by
  unfold tailWord_6181099
  simp only [CollatzResearch.WordTrace]
  refine ⟨225443201433941445509906351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150295467622627630339937567 225443201433941445509906351)
  ·
    refine ⟨338164802150912168264859527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225443201433941445509906351 338164802150912168264859527)
    ·
      refine ⟨507247203226368252397289291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338164802150912168264859527 507247203226368252397289291)
      ·
        refine ⟨760870804839552378595933937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507247203226368252397289291 760870804839552378595933937)
        ·
          refine ⟨570653103629664283946950453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760870804839552378595933937 570653103629664283946950453)
          ·
            refine ⟨53498728465281026620026605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 570653103629664283946950453 53498728465281026620026605)
            ·
              refine ⟨20062023174480384982509977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53498728465281026620026605 20062023174480384982509977)
              ·
                refine ⟨15046517380860288736882483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20062023174480384982509977 15046517380860288736882483)
                ·
                  refine ⟨22569776071290433105323725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15046517380860288736882483 22569776071290433105323725)
                  ·
                    refine ⟨8463666026733912414496397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22569776071290433105323725 8463666026733912414496397)
                    ·
                      refine ⟨3173874760025217155436149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8463666026733912414496397 3173874760025217155436149)
                      ·
                        rfl

theorem cell23_6181099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 3, 3].length) (baseStart_6181099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181099 prefixEnd_6181099 := by exact prefixLift 6181099
  have htrace : WordTrace (prefixWord ++ tailWord_6181099) baseStart_6181099 baseEnd_6181099 := by
    simpa [prefixWord, tailWord_6181099, baseEnd_6181099] using wordTrace_append hprefix tailTrace_6181099
  have hstable : (prefixWord ++ tailWord_6181099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181099).length < 2 ^ (prefixWord ++ tailWord_6181099).sum := by decide
  have hdescent : baseEnd_6181099 < baseStart_6181099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181103 : List Nat := [1, 1, 2, 1, 6, 2, 3, 1, 1, 2, 3]
def baseStart_6181103 : Nat := 118140960795 + 6181103 * 2 ^ 59
def prefixEnd_6181103 : Nat := 4983230072969 + 3 ^ 40 * 6181103 * 2
def baseEnd_6181103 : Nat := 3173876813947835139786131

theorem tailTrace_6181103 : CollatzResearch.WordTrace tailWord_6181103 prefixEnd_6181103 3173876813947835139786131 := by
  unfold tailWord_6181103
  simp only [CollatzResearch.WordTrace]
  refine ⟨225443347325926954193051963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150295564883951302795367975 225443347325926954193051963)
  ·
    refine ⟨338165020988890431289577945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225443347325926954193051963 338165020988890431289577945)
    ·
      refine ⟨253623765741667823467183459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338165020988890431289577945 253623765741667823467183459)
      ·
        refine ⟨380435648612501735200775189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253623765741667823467183459 380435648612501735200775189)
        ·
          refine ⟨17832921028711018837536337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 380435648612501735200775189 17832921028711018837536337)
          ·
            refine ⟨13374690771533264128152253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17832921028711018837536337 13374690771533264128152253)
            ·
              refine ⟨5015509039324974048057095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13374690771533264128152253 5015509039324974048057095)
              ·
                refine ⟨7523263558987461072085643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5015509039324974048057095 7523263558987461072085643)
                ·
                  refine ⟨11284895338481191608128465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523263558987461072085643 11284895338481191608128465)
                  ·
                    refine ⟨8463671503860893706096349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11284895338481191608128465 8463671503860893706096349)
                    ·
                      refine ⟨3173876813947835139786131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8463671503860893706096349 3173876813947835139786131)
                      ·
                        rfl

theorem cell23_6181103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 1, 1, 2, 3].length) (baseStart_6181103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181103 prefixEnd_6181103 := by exact prefixLift 6181103
  have htrace : WordTrace (prefixWord ++ tailWord_6181103) baseStart_6181103 baseEnd_6181103 := by
    simpa [prefixWord, tailWord_6181103, baseEnd_6181103] using wordTrace_append hprefix tailTrace_6181103
  have hstable : (prefixWord ++ tailWord_6181103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181103).length < 2 ^ (prefixWord ++ tailWord_6181103).sum := by decide
  have hdescent : baseEnd_6181103 < baseStart_6181103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181112 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_6181112 : Nat := 118140960795 + 6181112 * 2 ^ 59
def prefixEnd_6181112 : Nat := 4983230072969 + 3 ^ 40 * 6181112 * 2
def baseEnd_6181112 : Nat := 3173881435273725604573589

theorem tailTrace_6181112 : CollatzResearch.WordTrace tailWord_6181112 prefixEnd_6181112 3173881435273725604573589 := by
  unfold tailWord_6181112
  simp only [CollatzResearch.WordTrace]
  refine ⟨112721837791447174365064795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150295783721929565820086393 112721837791447174365064795)
  ·
    refine ⟨169082756687170761547597193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112721837791447174365064795 169082756687170761547597193)
    ·
      refine ⟨126812067515378071160697895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169082756687170761547597193 126812067515378071160697895)
      ·
        refine ⟨190218101273067106741046843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126812067515378071160697895 190218101273067106741046843)
        ·
          refine ⟨285327151909600660111570265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190218101273067106741046843 285327151909600660111570265)
          ·
            refine ⟨213995363932200495083677699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285327151909600660111570265 213995363932200495083677699)
            ·
              refine ⟨320993045898300742625516549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213995363932200495083677699 320993045898300742625516549)
              ·
                refine ⟨60186196105931389242284353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320993045898300742625516549 60186196105931389242284353)
                ·
                  refine ⟨45139647079448541931713265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60186196105931389242284353 45139647079448541931713265)
                  ·
                    refine ⟨33854735309586406448784949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45139647079448541931713265 33854735309586406448784949)
                    ·
                      refine ⟨3173881435273725604573589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33854735309586406448784949 3173881435273725604573589)
                      ·
                        rfl

theorem cell23_6181112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_6181112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181112 prefixEnd_6181112 := by exact prefixLift 6181112
  have htrace : WordTrace (prefixWord ++ tailWord_6181112) baseStart_6181112 baseEnd_6181112 := by
    simpa [prefixWord, tailWord_6181112, baseEnd_6181112] using wordTrace_append hprefix tailTrace_6181112
  have hstable : (prefixWord ++ tailWord_6181112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181112).length < 2 ^ (prefixWord ++ tailWord_6181112).sum := by decide
  have hdescent : baseEnd_6181112 < baseStart_6181112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181160 : List Nat := [2, 1, 5, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_6181160 : Nat := 118140960795 + 6181160 * 2 ^ 59
def prefixEnd_6181160 : Nat := 4983230072969 + 3 ^ 40 * 6181160 * 2
def baseEnd_6181160 : Nat := 3173906082345141416773369

theorem tailTrace_6181160 : CollatzResearch.WordTrace tailWord_6181160 prefixEnd_6181160 3173906082345141416773369 := by
  unfold tailWord_6181160
  simp only [CollatzResearch.WordTrace]
  refine ⟨112722713143360226463938467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150296950857813635285251289 112722713143360226463938467)
  ·
    refine ⟨169084069715040339695907701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112722713143360226463938467 169084069715040339695907701)
    ·
      refine ⟨15851631535785031846491347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169084069715040339695907701 15851631535785031846491347)
      ·
        refine ⟨23777447303677547769737021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15851631535785031846491347 23777447303677547769737021)
        ·
          refine ⟨8916542738879080413651383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23777447303677547769737021 8916542738879080413651383)
          ·
            refine ⟨13374814108318620620477075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8916542738879080413651383 13374814108318620620477075)
            ·
              refine ⟨20062221162477930930715613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13374814108318620620477075 20062221162477930930715613)
              ·
                refine ⟨7523332935929224099018355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20062221162477930930715613 7523332935929224099018355)
                ·
                  refine ⟨11284999403893836148527533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523332935929224099018355 11284999403893836148527533)
                  ·
                    refine ⟨4231874776460188555697825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11284999403893836148527533 4231874776460188555697825)
                    ·
                      refine ⟨3173906082345141416773369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231874776460188555697825 3173906082345141416773369)
                      ·
                        rfl

theorem cell23_6181160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_6181160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181160 prefixEnd_6181160 := by exact prefixLift 6181160
  have htrace : WordTrace (prefixWord ++ tailWord_6181160) baseStart_6181160 baseEnd_6181160 := by
    simpa [prefixWord, tailWord_6181160, baseEnd_6181160] using wordTrace_append hprefix tailTrace_6181160
  have hstable : (prefixWord ++ tailWord_6181160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181160).length < 2 ^ (prefixWord ++ tailWord_6181160).sum := by decide
  have hdescent : baseEnd_6181160 < baseStart_6181160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181173 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_6181173 : Nat := 118140960795 + 6181173 * 2 ^ 59
def prefixEnd_6181173 : Nat := 4983230072969 + 3 ^ 40 * 6181173 * 2
def baseEnd_6181173 : Nat := 3173912757593649865910809

theorem tailTrace_6181173 : CollatzResearch.WordTrace tailWord_6181173 prefixEnd_6181173 3173912757593649865910809 := by
  unfold tailWord_6181173
  simp only [CollatzResearch.WordTrace]
  refine ⟨225445900435673356148100173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150297266957115570765400115 225445900435673356148100173)
  ·
    refine ⟨84542212663377508555537565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225445900435673356148100173 84542212663377508555537565)
    ·
      refine ⟨31703329748766565708326587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84542212663377508555537565 31703329748766565708326587)
      ·
        refine ⟨47554994623149848562489881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31703329748766565708326587 47554994623149848562489881)
        ·
          refine ⟨35666245967362386421867411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47554994623149848562489881 35666245967362386421867411)
          ·
            refine ⟨53499368951043579632801117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35666245967362386421867411 53499368951043579632801117)
            ·
              refine ⟨20062263356641342362300419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53499368951043579632801117 20062263356641342362300419)
              ·
                refine ⟨30093395034962013543450629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20062263356641342362300419 30093395034962013543450629)
                ·
                  refine ⟨5642511569055377539396993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30093395034962013543450629 5642511569055377539396993)
                  ·
                    refine ⟨4231883676791533154547745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5642511569055377539396993 4231883676791533154547745)
                    ·
                      refine ⟨3173912757593649865910809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4231883676791533154547745 3173912757593649865910809)
                      ·
                        rfl

theorem cell23_6181173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_6181173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181173 prefixEnd_6181173 := by exact prefixLift 6181173
  have htrace : WordTrace (prefixWord ++ tailWord_6181173) baseStart_6181173 baseEnd_6181173 := by
    simpa [prefixWord, tailWord_6181173, baseEnd_6181173] using wordTrace_append hprefix tailTrace_6181173
  have hstable : (prefixWord ++ tailWord_6181173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181173).length < 2 ^ (prefixWord ++ tailWord_6181173).sum := by decide
  have hdescent : baseEnd_6181173 < baseStart_6181173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181209 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 2, 5]
def baseStart_6181209 : Nat := 118140960795 + 6181209 * 2 ^ 59
def prefixEnd_6181209 : Nat := 4983230072969 + 3 ^ 40 * 6181209 * 2
def baseEnd_6181209 : Nat := 1057977080965737241686881

theorem tailTrace_6181209 : CollatzResearch.WordTrace tailWord_6181209 prefixEnd_6181209 1057977080965737241686881 := by
  unfold tailWord_6181209
  simp only [CollatzResearch.WordTrace]
  refine ⟨225447213463542934296410681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150298142309028622864273787 225447213463542934296410681)
  ·
    refine ⟨169085410097657200722308011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225447213463542934296410681 169085410097657200722308011)
    ·
      refine ⟨253628115146485801083462017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169085410097657200722308011 253628115146485801083462017)
      ·
        refine ⟨190221086359864350812596513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253628115146485801083462017 190221086359864350812596513)
        ·
          refine ⟨142665814769898263109447385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190221086359864350812596513 142665814769898263109447385)
          ·
            refine ⟨106999361077423697332085539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142665814769898263109447385 106999361077423697332085539)
            ·
              refine ⟨160499041616135545998128309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106999361077423697332085539 160499041616135545998128309)
              ·
                refine ⟨15046785151512707437324529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160499041616135545998128309 15046785151512707437324529)
                ·
                  refine ⟨11285088863634530577993397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15046785151512707437324529 11285088863634530577993397)
                  ·
                    refine ⟨1057977080965737241686881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11285088863634530577993397 1057977080965737241686881)
                    ·
                      rfl

theorem cell23_6181209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_6181209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181209 prefixEnd_6181209 := by exact prefixLift 6181209
  have htrace : WordTrace (prefixWord ++ tailWord_6181209) baseStart_6181209 baseEnd_6181209 := by
    simpa [prefixWord, tailWord_6181209, baseEnd_6181209] using wordTrace_append hprefix tailTrace_6181209
  have hstable : (prefixWord ++ tailWord_6181209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181209).length < 2 ^ (prefixWord ++ tailWord_6181209).sum := by decide
  have hdescent : baseEnd_6181209 < baseStart_6181209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181219 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5]
def baseStart_6181219 : Nat := 118140960795 + 6181219 * 2 ^ 59
def prefixEnd_6181219 : Nat := 4983230072969 + 3 ^ 40 * 6181219 * 2
def baseEnd_6181219 : Nat := 3173936377703756685935597

theorem tailTrace_6181219 : CollatzResearch.WordTrace tailWord_6181219 prefixEnd_6181219 3173936377703756685935597 := by
  unfold tailWord_6181219
  simp only [CollatzResearch.WordTrace]
  refine ⟨225447578193506706004274711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150298385462337804002849807 225447578193506706004274711)
  ·
    refine ⟨338171367290260059006412067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225447578193506706004274711 338171367290260059006412067)
    ·
      refine ⟨507257050935390088509618101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338171367290260059006412067 507257050935390088509618101)
      ·
        refine ⟨47555348525192820797776697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 507257050935390088509618101 47555348525192820797776697)
        ·
          refine ⟨35666511393894615598332523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47555348525192820797776697 35666511393894615598332523)
          ·
            refine ⟨53499767090841923397498785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35666511393894615598332523 53499767090841923397498785)
            ·
              refine ⟨40124825318131442548124089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53499767090841923397498785 40124825318131442548124089)
              ·
                refine ⟨30093618988598581911093067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40124825318131442548124089 30093618988598581911093067)
                ·
                  refine ⟨45140428482897872866639601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30093618988598581911093067 45140428482897872866639601)
                  ·
                    refine ⟨33855321362173404649979701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45140428482897872866639601 33855321362173404649979701)
                    ·
                      refine ⟨3173936377703756685935597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33855321362173404649979701 3173936377703756685935597)
                      ·
                        rfl

theorem cell23_6181219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_6181219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181219 prefixEnd_6181219 := by exact prefixLift 6181219
  have htrace : WordTrace (prefixWord ++ tailWord_6181219) baseStart_6181219 baseEnd_6181219 := by
    simpa [prefixWord, tailWord_6181219, baseEnd_6181219] using wordTrace_append hprefix tailTrace_6181219
  have hstable : (prefixWord ++ tailWord_6181219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181219).length < 2 ^ (prefixWord ++ tailWord_6181219).sum := by decide
  have hdescent : baseEnd_6181219 < baseStart_6181219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181226 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_6181226 : Nat := 118140960795 + 6181226 * 2 ^ 59
def prefixEnd_6181226 : Nat := 4983230072969 + 3 ^ 40 * 6181226 * 2
def baseEnd_6181226 : Nat := 1057979990689446052849355

theorem tailTrace_6181226 : CollatzResearch.WordTrace tailWord_6181226 prefixEnd_6181226 1057979990689446052849355 := by
  unfold tailWord_6181226
  simp only [CollatzResearch.WordTrace]
  refine ⟨56361958376120336549944883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150298555669654230799853021 56361958376120336549944883)
  ·
    refine ⟨84542937564180504824917325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56361958376120336549944883 84542937564180504824917325)
    ·
      refine ⟨31703601586567689309343997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84542937564180504824917325 31703601586567689309343997)
      ·
        refine ⟨11888850594962883491003999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31703601586567689309343997 11888850594962883491003999)
        ·
          refine ⟨17833275892444325236505999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11888850594962883491003999 17833275892444325236505999)
          ·
            refine ⟨26749913838666487854758999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17833275892444325236505999 26749913838666487854758999)
            ·
              refine ⟨40124870757999731782138499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26749913838666487854758999 40124870757999731782138499)
              ·
                refine ⟨60187306136999597673207749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40124870757999731782138499 60187306136999597673207749)
                ·
                  refine ⟨11285119900687424563726453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60187306136999597673207749 11285119900687424563726453)
                  ·
                    refine ⟨1057979990689446052849355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11285119900687424563726453 1057979990689446052849355)
                    ·
                      rfl

theorem cell23_6181226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_6181226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181226 prefixEnd_6181226 := by exact prefixLift 6181226
  have htrace : WordTrace (prefixWord ++ tailWord_6181226) baseStart_6181226 baseEnd_6181226 := by
    simpa [prefixWord, tailWord_6181226, baseEnd_6181226] using wordTrace_append hprefix tailTrace_6181226
  have hstable : (prefixWord ++ tailWord_6181226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181226).length < 2 ^ (prefixWord ++ tailWord_6181226).sum := by decide
  have hdescent : baseEnd_6181226 < baseStart_6181226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181256 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 5, 4]
def baseStart_6181256 : Nat := 118140960795 + 6181256 * 2 ^ 59
def prefixEnd_6181256 : Nat := 4983230072969 + 3 ^ 40 * 6181256 * 2
def baseEnd_6181256 : Nat := 1057985125495991013724309

theorem tailTrace_6181256 : CollatzResearch.WordTrace tailWord_6181256 prefixEnd_6181256 1057985125495991013724309 := by
  unfold tailWord_6181256
  simp only [CollatzResearch.WordTrace]
  refine ⟨112724463847186330661685811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150299285129581774215581081 112724463847186330661685811)
  ·
    refine ⟨169086695770779495992528717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112724463847186330661685811 169086695770779495992528717)
    ·
      refine ⟨63407510914042310997198269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169086695770779495992528717 63407510914042310997198269)
      ·
        refine ⟨23777816592765866623949351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63407510914042310997198269 23777816592765866623949351)
        ·
          refine ⟨35666724889148799935924027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23777816592765866623949351 35666724889148799935924027)
          ·
            refine ⟨53500087333723199903886041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35666724889148799935924027 53500087333723199903886041)
            ·
              refine ⟨40125065500292399927914531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53500087333723199903886041 40125065500292399927914531)
              ·
                refine ⟨60187598250438599891871797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40125065500292399927914531 60187598250438599891871797)
                ·
                  refine ⟨5642587335978618739862981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60187598250438599891871797 5642587335978618739862981)
                  ·
                    refine ⟨1057985125495991013724309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5642587335978618739862981 1057985125495991013724309)
                    ·
                      rfl

theorem cell23_6181256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_6181256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181256 prefixEnd_6181256 := by exact prefixLift 6181256
  have htrace : WordTrace (prefixWord ++ tailWord_6181256) baseStart_6181256 baseEnd_6181256 := by
    simpa [prefixWord, tailWord_6181256, baseEnd_6181256] using wordTrace_append hprefix tailTrace_6181256
  have hstable : (prefixWord ++ tailWord_6181256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181256).length < 2 ^ (prefixWord ++ tailWord_6181256).sum := by decide
  have hdescent : baseEnd_6181256 < baseStart_6181256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181273 : List Nat := [1, 2, 1, 2, 1, 4, 2, 5, 1, 4]
def baseStart_6181273 : Nat := 118140960795 + 6181273 * 2 ^ 59
def prefixEnd_6181273 : Nat := 4983230072969 + 3 ^ 40 * 6181273 * 2
def baseEnd_6181273 : Nat := 1057988035219699824886783

theorem tailTrace_6181273 : CollatzResearch.WordTrace tailWord_6181273 prefixEnd_6181273 1057988035219699824886783 := by
  unfold tailWord_6181273
  simp only [CollatzResearch.WordTrace]
  refine ⟨225449547735311073226740473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150299698490207382151160315 225449547735311073226740473)
  ·
    refine ⟨169087160801483304920055355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225449547735311073226740473 169087160801483304920055355)
    ·
      refine ⟨253630741202224957380083033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169087160801483304920055355 253630741202224957380083033)
      ·
        refine ⟨190223055901668718035062275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253630741202224957380083033 190223055901668718035062275)
        ·
          refine ⟨285334583852503077052593413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190223055901668718035062275 285334583852503077052593413)
          ·
            refine ⟨53500234472344326947361265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285334583852503077052593413 53500234472344326947361265)
            ·
              refine ⟨40125175854258245210520949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53500234472344326947361265 40125175854258245210520949)
              ·
                refine ⟨3761735236336710488486339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40125175854258245210520949 3761735236336710488486339)
                ·
                  refine ⟨5642602854505065732729509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761735236336710488486339 5642602854505065732729509)
                  ·
                    refine ⟨1057988035219699824886783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5642602854505065732729509 1057988035219699824886783)
                    ·
                      rfl

theorem cell23_6181273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 1, 4].length) (baseStart_6181273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181273 prefixEnd_6181273 := by exact prefixLift 6181273
  have htrace : WordTrace (prefixWord ++ tailWord_6181273) baseStart_6181273 baseEnd_6181273 := by
    simpa [prefixWord, tailWord_6181273, baseEnd_6181273] using wordTrace_append hprefix tailTrace_6181273
  have hstable : (prefixWord ++ tailWord_6181273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181273).length < 2 ^ (prefixWord ++ tailWord_6181273).sum := by decide
  have hdescent : baseEnd_6181273 < baseStart_6181273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181333 : List Nat := [1, 3, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_6181333 : Nat := 118140960795 + 6181333 * 2 ^ 59
def prefixEnd_6181333 : Nat := 4983230072969 + 3 ^ 40 * 6181333 * 2
def baseEnd_6181333 : Nat := 1057998304832789746636691

theorem tailTrace_6181333 : CollatzResearch.WordTrace tailWord_6181333 prefixEnd_6181333 1057998304832789746636691 := by
  unfold tailWord_6181333
  simp only [CollatzResearch.WordTrace]
  refine ⟨225451736115093703473924653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150301157410062468982616435 225451736115093703473924653)
  ·
    refine ⟨84544401043160138802721745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225451736115093703473924653 84544401043160138802721745)
    ·
      refine ⟨63408300782370104102041309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84544401043160138802721745 63408300782370104102041309)
      ·
        refine ⟨23778112793388789038265491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63408300782370104102041309 23778112793388789038265491)
        ·
          refine ⟨35667169190083183557398237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23778112793388789038265491 35667169190083183557398237)
          ·
            refine ⟨13375188446281193834024339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35667169190083183557398237 13375188446281193834024339)
            ·
              refine ⟨20062782669421790751036509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13375188446281193834024339 20062782669421790751036509)
              ·
                refine ⟨7523543501033171531638691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20062782669421790751036509 7523543501033171531638691)
                ·
                  refine ⟨11285315251549757297458037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523543501033171531638691 11285315251549757297458037)
                  ·
                    refine ⟨1057998304832789746636691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11285315251549757297458037 1057998304832789746636691)
                    ·
                      rfl

theorem cell23_6181333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_6181333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181333 prefixEnd_6181333 := by exact prefixLift 6181333
  have htrace : WordTrace (prefixWord ++ tailWord_6181333) baseStart_6181333 baseEnd_6181333 := by
    simpa [prefixWord, tailWord_6181333, baseEnd_6181333] using wordTrace_append hprefix tailTrace_6181333
  have hstable : (prefixWord ++ tailWord_6181333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181333).length < 2 ^ (prefixWord ++ tailWord_6181333).sum := by decide
  have hdescent : baseEnd_6181333 < baseStart_6181333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181356 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 5]
def baseStart_6181356 : Nat := 118140960795 + 6181356 * 2 ^ 59
def prefixEnd_6181356 : Nat := 4983230072969 + 3 ^ 40 * 6181356 * 2
def baseEnd_6181356 : Nat := 3174006724553422649922467

theorem tailTrace_6181356 : CollatzResearch.WordTrace tailWord_6181356 prefixEnd_6181356 3174006724553422649922467 := by
  unfold tailWord_6181356
  simp only [CollatzResearch.WordTrace]
  refine ⟨112726287497005189201005961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150301716662673585601341281 112726287497005189201005961)
  ·
    refine ⟨84544715622753891900754471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112726287497005189201005961 84544715622753891900754471)
    ·
      refine ⟨126817073434130837851131707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84544715622753891900754471 126817073434130837851131707)
      ·
        refine ⟨190225610151196256776697561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126817073434130837851131707 190225610151196256776697561)
        ·
          refine ⟨142669207613397192582523171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190225610151196256776697561 142669207613397192582523171)
          ·
            refine ⟨214003811420095788873784757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142669207613397192582523171 214003811420095788873784757)
            ·
              refine ⟨20062857320633980206917321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214003811420095788873784757 20062857320633980206917321)
              ·
                refine ⟨15047142990475485155187991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20062857320633980206917321 15047142990475485155187991)
                ·
                  refine ⟨22570714485713227732781987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15047142990475485155187991 22570714485713227732781987)
                  ·
                    refine ⟨33856071728569841599172981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22570714485713227732781987 33856071728569841599172981)
                    ·
                      refine ⟨3174006724553422649922467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33856071728569841599172981 3174006724553422649922467)
                      ·
                        rfl

theorem cell23_6181356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_6181356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181356 prefixEnd_6181356 := by exact prefixLift 6181356
  have htrace : WordTrace (prefixWord ++ tailWord_6181356) baseStart_6181356 baseEnd_6181356 := by
    simpa [prefixWord, tailWord_6181356, baseEnd_6181356] using wordTrace_append hprefix tailTrace_6181356
  have hstable : (prefixWord ++ tailWord_6181356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181356).length < 2 ^ (prefixWord ++ tailWord_6181356).sum := by decide
  have hdescent : baseEnd_6181356 < baseStart_6181356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181359 : List Nat := [1, 1, 2, 1, 4, 1, 1, 12]
def baseStart_6181359 : Nat := 118140960795 + 6181359 * 2 ^ 59
def prefixEnd_6181359 : Nat := 4983230072969 + 3 ^ 40 * 6181359 * 2
def baseEnd_6181359 : Nat := 117555861666495782895739

theorem tailTrace_6181359 : CollatzResearch.WordTrace tailWord_6181359 prefixEnd_6181359 117555861666495782895739 := by
  unfold tailWord_6181359
  simp only [CollatzResearch.WordTrace]
  refine ⟨225452684412999509914371131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150301789608666339942914087 225452684412999509914371131)
  ·
    refine ⟨338179026619499264871556697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225452684412999509914371131 338179026619499264871556697)
    ·
      refine ⟨253634269964624448653667523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338179026619499264871556697 253634269964624448653667523)
      ·
        refine ⟨380451404946936672980501285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253634269964624448653667523 380451404946936672980501285)
        ·
          refine ⟨71334638427550626183843991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380451404946936672980501285 71334638427550626183843991)
          ·
            refine ⟨107001957641325939275765987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71334638427550626183843991 107001957641325939275765987)
            ·
              refine ⟨160502936461988908913648981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107001957641325939275765987 160502936461988908913648981)
              ·
                refine ⟨117555861666495782895739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 160502936461988908913648981 117555861666495782895739)
                ·
                  rfl

theorem cell23_6181359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 12].length) (baseStart_6181359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181359 prefixEnd_6181359 := by exact prefixLift 6181359
  have htrace : WordTrace (prefixWord ++ tailWord_6181359) baseStart_6181359 baseEnd_6181359 := by
    simpa [prefixWord, tailWord_6181359, baseEnd_6181359] using wordTrace_append hprefix tailTrace_6181359
  have hstable : (prefixWord ++ tailWord_6181359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181359).length < 2 ^ (prefixWord ++ tailWord_6181359).sum := by decide
  have hdescent : baseEnd_6181359 < baseStart_6181359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181390 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_6181390 : Nat := 118140960795 + 6181390 * 2 ^ 59
def prefixEnd_6181390 : Nat := 4983230072969 + 3 ^ 40 * 6181390 * 2
def baseEnd_6181390 : Nat := 3174024182895675516897311

theorem tailTrace_6181390 : CollatzResearch.WordTrace tailWord_6181390 prefixEnd_6181390 3174024182895675516897311 := by
  unfold tailWord_6181390
  simp only [CollatzResearch.WordTrace]
  refine ⟨28181726884485900276093703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150302543383924801472499749 28181726884485900276093703)
  ·
    refine ⟨42272590326728850414140555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28181726884485900276093703 42272590326728850414140555)
    ·
      refine ⟨63408885490093275621210833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42272590326728850414140555 63408885490093275621210833)
      ·
        refine ⟨47556664117569956715908125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63408885490093275621210833 47556664117569956715908125)
        ·
          refine ⟨17833749044088733768465547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47556664117569956715908125 17833749044088733768465547)
          ·
            refine ⟨26750623566133100652698321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17833749044088733768465547 26750623566133100652698321)
            ·
              refine ⟨20062967674599825489523741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26750623566133100652698321 20062967674599825489523741)
              ·
                refine ⟨7523612877974934558571403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20062967674599825489523741 7523612877974934558571403)
                ·
                  refine ⟨11285419316962401837857105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523612877974934558571403 11285419316962401837857105)
                  ·
                    refine ⟨8464064487721801378392829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11285419316962401837857105 8464064487721801378392829)
                    ·
                      refine ⟨3174024182895675516897311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8464064487721801378392829 3174024182895675516897311)
                      ·
                        rfl

theorem cell23_6181390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_6181390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181390 prefixEnd_6181390 := by exact prefixLift 6181390
  have htrace : WordTrace (prefixWord ++ tailWord_6181390) baseStart_6181390 baseEnd_6181390 := by
    simpa [prefixWord, tailWord_6181390, baseEnd_6181390] using wordTrace_append hprefix tailTrace_6181390
  have hstable : (prefixWord ++ tailWord_6181390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181390).length < 2 ^ (prefixWord ++ tailWord_6181390).sum := by decide
  have hdescent : baseEnd_6181390 < baseStart_6181390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181421 : List Nat := [1, 5, 4, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6181421 : Nat := 118140960795 + 6181421 * 2 ^ 59
def prefixEnd_6181421 : Nat := 4983230072969 + 3 ^ 40 * 6181421 * 2
def baseEnd_6181421 : Nat := 3174040100795964895609669

theorem tailTrace_6181421 : CollatzResearch.WordTrace tailWord_6181421 prefixEnd_6181421 3174040100795964895609669 := by
  unfold tailWord_6181421
  simp only [CollatzResearch.WordTrace]
  refine ⟨225454945738774894503128117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150303297159183263002085411 225454945738774894503128117)
  ·
    refine ⟨21136401163010146359668261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225454945738774894503128117 21136401163010146359668261)
    ·
      refine ⟨3963075218064402442437799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21136401163010146359668261 3963075218064402442437799)
      ·
        refine ⟨5944612827096603663656699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963075218064402442437799 5944612827096603663656699)
        ·
          refine ⟨8916919240644905495485049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5944612827096603663656699 8916919240644905495485049)
          ·
            refine ⟨6687689430483679121613787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8916919240644905495485049 6687689430483679121613787)
            ·
              refine ⟨10031534145725518682420681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6687689430483679121613787 10031534145725518682420681)
              ·
                refine ⟨7523650609294139011815511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10031534145725518682420681 7523650609294139011815511)
                ·
                  refine ⟨11285475913941208517723267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523650609294139011815511 11285475913941208517723267)
                  ·
                    refine ⟨16928213870911812776584901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11285475913941208517723267 16928213870911812776584901)
                    ·
                      refine ⟨3174040100795964895609669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16928213870911812776584901 3174040100795964895609669)
                      ·
                        rfl

theorem cell23_6181421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6181421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181421 prefixEnd_6181421 := by exact prefixLift 6181421
  have htrace : WordTrace (prefixWord ++ tailWord_6181421) baseStart_6181421 baseEnd_6181421 := by
    simpa [prefixWord, tailWord_6181421, baseEnd_6181421] using wordTrace_append hprefix tailTrace_6181421
  have hstable : (prefixWord ++ tailWord_6181421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181421).length < 2 ^ (prefixWord ++ tailWord_6181421).sum := by decide
  have hdescent : baseEnd_6181421 < baseStart_6181421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181473 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_6181473 : Nat := 118140960795 + 6181473 * 2 ^ 59
def prefixEnd_6181473 : Nat := 4983230072969 + 3 ^ 40 * 6181473 * 2
def baseEnd_6181473 : Nat := 3174066801789998692159429

theorem tailTrace_6181473 : CollatzResearch.WordTrace tailWord_6181473 prefixEnd_6181473 3174066801789998692159429 := by
  unfold tailWord_6181473
  simp only [CollatzResearch.WordTrace]
  refine ⟨225456842334586507384021073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150304561556391004922680715 225456842334586507384021073)
  ·
    refine ⟨169092631750939880538015805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225456842334586507384021073 169092631750939880538015805)
    ·
      refine ⟨63409736906602455201755927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169092631750939880538015805 63409736906602455201755927)
      ·
        refine ⟨95114605359903682802633891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63409736906602455201755927 95114605359903682802633891)
        ·
          refine ⟨142671908039855524203950837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95114605359903682802633891 142671908039855524203950837)
          ·
            refine ⟨13375491378736455394120391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142671908039855524203950837 13375491378736455394120391)
            ·
              refine ⟨20063237068104683091180587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13375491378736455394120391 20063237068104683091180587)
              ·
                refine ⟨30094855602157024636770881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20063237068104683091180587 30094855602157024636770881)
                ·
                  refine ⟨22571141701617768477578161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30094855602157024636770881 22571141701617768477578161)
                  ·
                    refine ⟨16928356276213326358183621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22571141701617768477578161 16928356276213326358183621)
                    ·
                      refine ⟨3174066801789998692159429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16928356276213326358183621 3174066801789998692159429)
                      ·
                        rfl

theorem cell23_6181473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_6181473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181473 prefixEnd_6181473 := by exact prefixLift 6181473
  have htrace : WordTrace (prefixWord ++ tailWord_6181473) baseStart_6181473 baseEnd_6181473 := by
    simpa [prefixWord, tailWord_6181473, baseEnd_6181473] using wordTrace_append hprefix tailTrace_6181473
  have hstable : (prefixWord ++ tailWord_6181473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181473).length < 2 ^ (prefixWord ++ tailWord_6181473).sum := by decide
  have hdescent : baseEnd_6181473 < baseStart_6181473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181477 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 1, 4, 2]
def baseStart_6181477 : Nat := 118140960795 + 6181477 * 2 ^ 59
def prefixEnd_6181477 : Nat := 4983230072969 + 3 ^ 40 * 6181477 * 2
def baseEnd_6181477 : Nat := 3174068855712616676509411

theorem tailTrace_6181477 : CollatzResearch.WordTrace tailWord_6181477 prefixEnd_6181477 3174068855712616676509411 := by
  unfold tailWord_6181477
  simp only [CollatzResearch.WordTrace]
  refine ⟨225456988226572016067166685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150304658817714677378111123 225456988226572016067166685)
  ·
    refine ⟨84546370584964506025187507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225456988226572016067166685 84546370584964506025187507)
    ·
      refine ⟨126819555877446759037781261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84546370584964506025187507 126819555877446759037781261)
      ·
        refine ⟨47557333454042534639167973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126819555877446759037781261 47557333454042534639167973)
        ·
          refine ⟨8917000022632975244843995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47557333454042534639167973 8917000022632975244843995)
          ·
            refine ⟨13375500033949462867265993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917000022632975244843995 13375500033949462867265993)
            ·
              refine ⟨10031625025462097150449495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13375500033949462867265993 10031625025462097150449495)
              ·
                refine ⟨15047437538193145725674243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10031625025462097150449495 15047437538193145725674243)
                ·
                  refine ⟨22571156307289718588511365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15047437538193145725674243 22571156307289718588511365)
                  ·
                    refine ⟨4232091807616822235345881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22571156307289718588511365 4232091807616822235345881)
                    ·
                      refine ⟨3174068855712616676509411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232091807616822235345881 3174068855712616676509411)
                      ·
                        rfl

theorem cell23_6181477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_6181477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181477 prefixEnd_6181477 := by exact prefixLift 6181477
  have htrace : WordTrace (prefixWord ++ tailWord_6181477) baseStart_6181477 baseEnd_6181477 := by
    simpa [prefixWord, tailWord_6181477, baseEnd_6181477] using wordTrace_append hprefix tailTrace_6181477
  have hstable : (prefixWord ++ tailWord_6181477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181477).length < 2 ^ (prefixWord ++ tailWord_6181477).sum := by decide
  have hdescent : baseEnd_6181477 < baseStart_6181477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181496 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 1, 7]
def baseStart_6181496 : Nat := 118140960795 + 6181496 * 2 ^ 59
def prefixEnd_6181496 : Nat := 4983230072969 + 3 ^ 40 * 6181496 * 2
def baseEnd_6181496 : Nat := 1058026203948350700723941

theorem tailTrace_6181496 : CollatzResearch.WordTrace tailWord_6181496 prefixEnd_6181496 1058026203948350700723941 := by
  unfold tailWord_6181496
  simp only [CollatzResearch.WordTrace]
  refine ⟨112728840606751591156054171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150305120809002121541405561 112728840606751591156054171)
  ·
    refine ⟨169093260910127386734081257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112728840606751591156054171 169093260910127386734081257)
    ·
      refine ⟨126819945682595540050560943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169093260910127386734081257 126819945682595540050560943)
      ·
        refine ⟨190229918523893310075841415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126819945682595540050560943 190229918523893310075841415)
        ·
          refine ⟨285344877785839965113762123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190229918523893310075841415 285344877785839965113762123)
          ·
            refine ⟨428017316678759947670643185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285344877785839965113762123 428017316678759947670643185)
            ·
              refine ⟨321012987509069960752982389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428017316678759947670643185 321012987509069960752982389)
              ·
                refine ⟨30094967578975308820592099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321012987509069960752982389 30094967578975308820592099)
                ·
                  refine ⟨45142451368462963230888149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30094967578975308820592099 45142451368462963230888149)
                  ·
                    refine ⟨1058026203948350700723941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45142451368462963230888149 1058026203948350700723941)
                    ·
                      rfl

theorem cell23_6181496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_6181496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181496 prefixEnd_6181496 := by exact prefixLift 6181496
  have htrace : WordTrace (prefixWord ++ tailWord_6181496) baseStart_6181496 baseEnd_6181496 := by
    simpa [prefixWord, tailWord_6181496, baseEnd_6181496] using wordTrace_append hprefix tailTrace_6181496
  have hstable : (prefixWord ++ tailWord_6181496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181496).length < 2 ^ (prefixWord ++ tailWord_6181496).sum := by decide
  have hdescent : baseEnd_6181496 < baseStart_6181496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181503 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 1, 7, 2]
def baseStart_6181503 : Nat := 118140960795 + 6181503 * 2 ^ 59
def prefixEnd_6181503 : Nat := 4983230072969 + 3 ^ 40 * 6181503 * 2
def baseEnd_6181503 : Nat := 3174082206209633574784291

theorem tailTrace_6181503 : CollatzResearch.WordTrace tailWord_6181503 prefixEnd_6181503 3174082206209633574784291 := by
  unfold tailWord_6181503
  simp only [CollatzResearch.WordTrace]
  refine ⟨225457936524477822507613163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150305291016318548338408775 225457936524477822507613163)
  ·
    refine ⟨338186904786716733761419745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225457936524477822507613163 338186904786716733761419745)
    ·
      refine ⟨253640178590037550321064809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338186904786716733761419745 253640178590037550321064809)
      ·
        refine ⟨190230133942528162740798607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253640178590037550321064809 190230133942528162740798607)
        ·
          refine ⟨285345200913792244111197911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190230133942528162740798607 285345200913792244111197911)
          ·
            refine ⟨428017801370688366166796867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285345200913792244111197911 428017801370688366166796867)
            ·
              refine ⟨642026702056032549250195301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428017801370688366166796867 642026702056032549250195301)
              ·
                refine ⟨120380006635506102984411619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642026702056032549250195301 120380006635506102984411619)
                ·
                  refine ⟨180570009953259154476617429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120380006635506102984411619 180570009953259154476617429)
                  ·
                    refine ⟨4232109608279511433045721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 180570009953259154476617429 4232109608279511433045721)
                    ·
                      refine ⟨3174082206209633574784291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232109608279511433045721 3174082206209633574784291)
                      ·
                        rfl

theorem cell23_6181503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_6181503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181503 prefixEnd_6181503 := by exact prefixLift 6181503
  have htrace : WordTrace (prefixWord ++ tailWord_6181503) baseStart_6181503 baseEnd_6181503 := by
    simpa [prefixWord, tailWord_6181503, baseEnd_6181503] using wordTrace_append hprefix tailTrace_6181503
  have hstable : (prefixWord ++ tailWord_6181503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181503).length < 2 ^ (prefixWord ++ tailWord_6181503).sum := by decide
  have hdescent : baseEnd_6181503 < baseStart_6181503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181533 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_6181533 : Nat := 118140960795 + 6181533 * 2 ^ 59
def prefixEnd_6181533 : Nat := 4983230072969 + 3 ^ 40 * 6181533 * 2
def baseEnd_6181533 : Nat := 3174097610629268457409153

theorem tailTrace_6181533 : CollatzResearch.WordTrace tailWord_6181533 prefixEnd_6181533 3174097610629268457409153 := by
  unfold tailWord_6181533
  simp only [CollatzResearch.WordTrace]
  refine ⟨225459030714369137631205253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150306020476246091754136835 225459030714369137631205253)
  ·
    refine ⟨42273568258944213305850985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225459030714369137631205253 42273568258944213305850985)
    ·
      refine ⟨31705176194208159979388239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42273568258944213305850985 31705176194208159979388239)
      ·
        refine ⟨47557764291312239969082359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31705176194208159979388239 47557764291312239969082359)
        ·
          refine ⟨71336646436968359953623539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47557764291312239969082359 71336646436968359953623539)
          ·
            refine ⟨107004969655452539930435309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71336646436968359953623539 107004969655452539930435309)
            ·
              refine ⟨40126863620794702473913241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107004969655452539930435309 40126863620794702473913241)
              ·
                refine ⟨30095147715596026855434931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40126863620794702473913241 30095147715596026855434931)
                ·
                  refine ⟨45142721573394040283152397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30095147715596026855434931 45142721573394040283152397)
                  ·
                    refine ⟨16928520590022765106182149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45142721573394040283152397 16928520590022765106182149)
                    ·
                      refine ⟨3174097610629268457409153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16928520590022765106182149 3174097610629268457409153)
                      ·
                        rfl

theorem cell23_6181533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_6181533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181533 prefixEnd_6181533 := by exact prefixLift 6181533
  have htrace : WordTrace (prefixWord ++ tailWord_6181533) baseStart_6181533 baseEnd_6181533 := by
    simpa [prefixWord, tailWord_6181533, baseEnd_6181533] using wordTrace_append hprefix tailTrace_6181533
  have hstable : (prefixWord ++ tailWord_6181533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181533).length < 2 ^ (prefixWord ++ tailWord_6181533).sum := by decide
  have hdescent : baseEnd_6181533 < baseStart_6181533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181574 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6181574 : Nat := 118140960795 + 6181574 * 2 ^ 59
def prefixEnd_6181574 : Nat := 4983230072969 + 3 ^ 40 * 6181574 * 2
def baseEnd_6181574 : Nat := 3174118663336102796996465

theorem tailTrace_6181574 : CollatzResearch.WordTrace tailWord_6181574 prefixEnd_6181574 3174118663336102796996465 := by
  unfold tailWord_6181574
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045641440850643801045243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150307017404813734422298517 7045641440850643801045243)
  ·
    refine ⟨10568462161275965701567865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7045641440850643801045243 10568462161275965701567865)
    ·
      refine ⟨7926346620956974276175899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10568462161275965701567865 7926346620956974276175899)
      ·
        refine ⟨11889519931435461414263849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926346620956974276175899 11889519931435461414263849)
        ·
          refine ⟨8917139948576596060697887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11889519931435461414263849 8917139948576596060697887)
          ·
            refine ⟨13375709922864894091046831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917139948576596060697887 13375709922864894091046831)
            ·
              refine ⟨20063564884297341136570247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13375709922864894091046831 20063564884297341136570247)
              ·
                refine ⟨30095347326446011704855371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20063564884297341136570247 30095347326446011704855371)
                ·
                  refine ⟨45143020989669017557283057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30095347326446011704855371 45143020989669017557283057)
                  ·
                    refine ⟨33857265742251763167962293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45143020989669017557283057 33857265742251763167962293)
                    ·
                      refine ⟨3174118663336102796996465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33857265742251763167962293 3174118663336102796996465)
                      ·
                        rfl

theorem cell23_6181574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6181574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181574 prefixEnd_6181574 := by exact prefixLift 6181574
  have htrace : WordTrace (prefixWord ++ tailWord_6181574) baseStart_6181574 baseEnd_6181574 := by
    simpa [prefixWord, tailWord_6181574, baseEnd_6181574] using wordTrace_append hprefix tailTrace_6181574
  have hstable : (prefixWord ++ tailWord_6181574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181574).length < 2 ^ (prefixWord ++ tailWord_6181574).sum := by decide
  have hdescent : baseEnd_6181574 < baseStart_6181574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181600 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 5, 1, 3]
def baseStart_6181600 : Nat := 118140960795 + 6181600 * 2 ^ 59
def prefixEnd_6181600 : Nat := 4983230072969 + 3 ^ 40 * 6181600 * 2
def baseEnd_6181600 : Nat := 3174132013833119695271345

theorem tailTrace_6181600 : CollatzResearch.WordTrace tailWord_6181600 prefixEnd_6181600 3174132013833119695271345 := by
  unfold tailWord_6181600
  simp only [CollatzResearch.WordTrace]
  refine ⟨112730737202563204036947127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150307649603417605382596169 112730737202563204036947127)
  ·
    refine ⟨169096105803844806055420691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112730737202563204036947127 169096105803844806055420691)
    ·
      refine ⟨253644158705767209083131037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169096105803844806055420691 253644158705767209083131037)
      ·
        refine ⟨95116559514662703406174139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253644158705767209083131037 95116559514662703406174139)
        ·
          refine ⟨142674839271994055109261209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95116559514662703406174139 142674839271994055109261209)
          ·
            refine ⟨107006129453995541331945907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142674839271994055109261209 107006129453995541331945907)
            ·
              refine ⟨160509194180993311997918861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107006129453995541331945907 160509194180993311997918861)
              ·
                refine ⟨60190947817872491999219573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160509194180993311997918861 60190947817872491999219573)
                ·
                  refine ⟨5642901357925546124926835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60190947817872491999219573 5642901357925546124926835)
                  ·
                    refine ⟨8464352036888319187390253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5642901357925546124926835 8464352036888319187390253)
                    ·
                      refine ⟨3174132013833119695271345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8464352036888319187390253 3174132013833119695271345)
                      ·
                        rfl

theorem cell23_6181600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_6181600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181600 prefixEnd_6181600 := by exact prefixLift 6181600
  have htrace : WordTrace (prefixWord ++ tailWord_6181600) baseStart_6181600 baseEnd_6181600 := by
    simpa [prefixWord, tailWord_6181600, baseEnd_6181600] using wordTrace_append hprefix tailTrace_6181600
  have hstable : (prefixWord ++ tailWord_6181600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181600).length < 2 ^ (prefixWord ++ tailWord_6181600).sum := by decide
  have hdescent : baseEnd_6181600 < baseStart_6181600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181633 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 5, 6]
def baseStart_6181633 : Nat := 118140960795 + 6181633 * 2 ^ 59
def prefixEnd_6181633 : Nat := 4983230072969 + 3 ^ 40 * 6181633 * 2
def baseEnd_6181633 : Nat := 1058049652898239355386231

theorem tailTrace_6181633 : CollatzResearch.WordTrace tailWord_6181633 prefixEnd_6181633 1058049652898239355386231 := by
  unfold tailWord_6181633
  simp only [CollatzResearch.WordTrace]
  refine ⟨225462678014006854709845553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150308452009337903139897035 225462678014006854709845553)
  ·
    refine ⟨169097008510505141032384165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225462678014006854709845553 169097008510505141032384165)
    ·
      refine ⟨31705689095719713943572031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169097008510505141032384165 31705689095719713943572031)
      ·
        refine ⟨47558533643579570915358047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31705689095719713943572031 47558533643579570915358047)
        ·
          refine ⟨71337800465369356373037071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47558533643579570915358047 71337800465369356373037071)
          ·
            refine ⟨107006700698054034559555607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71337800465369356373037071 107006700698054034559555607)
            ·
              refine ⟨160510051047081051839333411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107006700698054034559555607 160510051047081051839333411)
              ·
                refine ⟨240765076570621577759000117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160510051047081051839333411 240765076570621577759000117)
                ·
                  refine ⟨22571725928495772914906261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 240765076570621577759000117 22571725928495772914906261)
                  ·
                    refine ⟨1058049652898239355386231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22571725928495772914906261 1058049652898239355386231)
                    ·
                      rfl

theorem cell23_6181633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_6181633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181633 prefixEnd_6181633 := by exact prefixLift 6181633
  have htrace : WordTrace (prefixWord ++ tailWord_6181633) baseStart_6181633 baseEnd_6181633 := by
    simpa [prefixWord, tailWord_6181633, baseEnd_6181633] using wordTrace_append hprefix tailTrace_6181633
  have hstable : (prefixWord ++ tailWord_6181633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181633).length < 2 ^ (prefixWord ++ tailWord_6181633).sum := by decide
  have hdescent : baseEnd_6181633 < baseStart_6181633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181640 : List Nat := [2, 1, 3, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_6181640 : Nat := 118140960795 + 6181640 * 2 ^ 59
def prefixEnd_6181640 : Nat := 4983230072969 + 3 ^ 40 * 6181640 * 2
def baseEnd_6181640 : Nat := 3174152553059299538771161

theorem tailTrace_6181640 : CollatzResearch.WordTrace tailWord_6181640 prefixEnd_6181640 3174152553059299538771161 := by
  unfold tailWord_6181640
  simp only [CollatzResearch.WordTrace]
  refine ⟨112731466662490747452675187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150308622216654329936900249 112731466662490747452675187)
  ·
    refine ⟨169097199993736121179012781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112731466662490747452675187 169097199993736121179012781)
    ·
      refine ⟨63411449997651045442129793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169097199993736121179012781 63411449997651045442129793)
      ·
        refine ⟨47558587498238284081597345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63411449997651045442129793 47558587498238284081597345)
        ·
          refine ⟨35668940623678713061198009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47558587498238284081597345 35668940623678713061198009)
          ·
            refine ⟨26751705467759034795898507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35668940623678713061198009 26751705467759034795898507)
            ·
              refine ⟨40127558201638552193847761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26751705467759034795898507 40127558201638552193847761)
              ·
                refine ⟨30095668651228914145385821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40127558201638552193847761 30095668651228914145385821)
                ·
                  refine ⟨11285875744210842804519683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30095668651228914145385821 11285875744210842804519683)
                  ·
                    refine ⟨16928813616316264206779525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11285875744210842804519683 16928813616316264206779525)
                    ·
                      refine ⟨3174152553059299538771161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16928813616316264206779525 3174152553059299538771161)
                      ·
                        rfl

theorem cell23_6181640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_6181640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181640 prefixEnd_6181640 := by exact prefixLift 6181640
  have htrace : WordTrace (prefixWord ++ tailWord_6181640) baseStart_6181640 baseEnd_6181640 := by
    simpa [prefixWord, tailWord_6181640, baseEnd_6181640] using wordTrace_append hprefix tailTrace_6181640
  have hstable : (prefixWord ++ tailWord_6181640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181640).length < 2 ^ (prefixWord ++ tailWord_6181640).sum := by decide
  have hdescent : baseEnd_6181640 < baseStart_6181640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181643 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5]
def baseStart_6181643 : Nat := 118140960795 + 6181643 * 2 ^ 59
def prefixEnd_6181643 : Nat := 4983230072969 + 3 ^ 40 * 6181643 * 2
def baseEnd_6181643 : Nat := 3174154093501263027033647

theorem tailTrace_6181643 : CollatzResearch.WordTrace tailWord_6181643 prefixEnd_6181643 3174154093501263027033647 := by
  unfold tailWord_6181643
  simp only [CollatzResearch.WordTrace]
  refine ⟨225463042743970626417709583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150308695162647084278473055 225463042743970626417709583)
  ·
    refine ⟨338194564115955939626564375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225463042743970626417709583 338194564115955939626564375)
    ·
      refine ⟨507291846173933909439846563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338194564115955939626564375 507291846173933909439846563)
      ·
        refine ⟨760937769260900864159769845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507291846173933909439846563 760937769260900864159769845)
        ·
          refine ⟨71337915868209456014978423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 760937769260900864159769845 71337915868209456014978423)
          ·
            refine ⟨107006873802314184022467635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71337915868209456014978423 107006873802314184022467635)
            ·
              refine ⟨160510310703471276033701453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107006873802314184022467635 160510310703471276033701453)
              ·
                refine ⟨60191366513801728512638045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160510310703471276033701453 60191366513801728512638045)
                ·
                  refine ⟨22571762442675648192239267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60191366513801728512638045 22571762442675648192239267)
                  ·
                    refine ⟨33857643664013472288358901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22571762442675648192239267 33857643664013472288358901)
                    ·
                      refine ⟨3174154093501263027033647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33857643664013472288358901 3174154093501263027033647)
                      ·
                        rfl

theorem cell23_6181643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_6181643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181643 prefixEnd_6181643 := by exact prefixLift 6181643
  have htrace : WordTrace (prefixWord ++ tailWord_6181643) baseStart_6181643 baseEnd_6181643 := by
    simpa [prefixWord, tailWord_6181643, baseEnd_6181643] using wordTrace_append hprefix tailTrace_6181643
  have hstable : (prefixWord ++ tailWord_6181643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181643).length < 2 ^ (prefixWord ++ tailWord_6181643).sum := by decide
  have hdescent : baseEnd_6181643 < baseStart_6181643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181684 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_6181684 : Nat := 118140960795 + 6181684 * 2 ^ 59
def prefixEnd_6181684 : Nat := 4983230072969 + 3 ^ 40 * 6181684 * 2
def baseEnd_6181684 : Nat := 1058058382069365788873653

theorem tailTrace_6181684 : CollatzResearch.WordTrace tailWord_6181684 prefixEnd_6181684 1058058382069365788873653 := by
  unfold tailWord_6181684
  simp only [CollatzResearch.WordTrace]
  refine ⟨112732269068411045209976053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150309692091214726946634737 112732269068411045209976053)
  ·
    refine ⟨10568650225163535488435255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112732269068411045209976053 10568650225163535488435255)
    ·
      refine ⟨15852975337745303232652883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10568650225163535488435255 15852975337745303232652883)
      ·
        refine ⟨23779463006617954848979325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15852975337745303232652883 23779463006617954848979325)
        ·
          refine ⟨8917298627481733068367247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23779463006617954848979325 8917298627481733068367247)
          ·
            refine ⟨13375947941222599602550871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917298627481733068367247 13375947941222599602550871)
            ·
              refine ⟨20063921911833899403826307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13375947941222599602550871 20063921911833899403826307)
              ·
                refine ⟨30095882867750849105739461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20063921911833899403826307 30095882867750849105739461)
                ·
                  refine ⟨5642978037703284207326149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30095882867750849105739461 5642978037703284207326149)
                  ·
                    refine ⟨1058058382069365788873653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5642978037703284207326149 1058058382069365788873653)
                    ·
                      rfl

theorem cell23_6181684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_6181684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181684 prefixEnd_6181684 := by exact prefixLift 6181684
  have htrace : WordTrace (prefixWord ++ tailWord_6181684) baseStart_6181684 baseEnd_6181684 := by
    simpa [prefixWord, tailWord_6181684, baseEnd_6181684] using wordTrace_append hprefix tailTrace_6181684
  have hstable : (prefixWord ++ tailWord_6181684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181684).length < 2 ^ (prefixWord ++ tailWord_6181684).sum := by decide
  have hdescent : baseEnd_6181684 < baseStart_6181684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181724 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 4, 1, 3]
def baseStart_6181724 : Nat := 118140960795 + 6181724 * 2 ^ 59
def prefixEnd_6181724 : Nat := 4983230072969 + 3 ^ 40 * 6181724 * 2
def baseEnd_6181724 : Nat := 3174195685434277210120775

theorem tailTrace_6181724 : CollatzResearch.WordTrace tailWord_6181724 prefixEnd_6181724 3174195685434277210120775 := by
  unfold tailWord_6181724
  simp only [CollatzResearch.WordTrace]
  refine ⟨112732998528338588625704113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150310664704451451500938817 112732998528338588625704113)
  ·
    refine ⟨84549748896253941469278085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112732998528338588625704113 84549748896253941469278085)
    ·
      refine ⟨15853077918047614025489641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84549748896253941469278085 15853077918047614025489641)
      ·
        refine ⟨11889808438535710519117231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15853077918047614025489641 11889808438535710519117231)
        ·
          refine ⟨17834712657803565778675847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11889808438535710519117231 17834712657803565778675847)
          ·
            refine ⟨26752068986705348668013771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17834712657803565778675847 26752068986705348668013771)
            ·
              refine ⟨40128103480058023002020657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26752068986705348668013771 40128103480058023002020657)
              ·
                refine ⟨30096077610043517251515493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40128103480058023002020657 30096077610043517251515493)
                ·
                  refine ⟨5643014551883159484659155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30096077610043517251515493 5643014551883159484659155)
                  ·
                    refine ⟨8464521827824739226988733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643014551883159484659155 8464521827824739226988733)
                    ·
                      refine ⟨3174195685434277210120775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8464521827824739226988733 3174195685434277210120775)
                      ·
                        rfl

theorem cell23_6181724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_6181724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181724 prefixEnd_6181724 := by exact prefixLift 6181724
  have htrace : WordTrace (prefixWord ++ tailWord_6181724) baseStart_6181724 baseEnd_6181724 := by
    simpa [prefixWord, tailWord_6181724, baseEnd_6181724] using wordTrace_append hprefix tailTrace_6181724
  have hstable : (prefixWord ++ tailWord_6181724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181724).length < 2 ^ (prefixWord ++ tailWord_6181724).sum := by decide
  have hdescent : baseEnd_6181724 < baseStart_6181724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181758 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6181758 : Nat := 118140960795 + 6181758 * 2 ^ 59
def prefixEnd_6181758 : Nat := 4983230072969 + 3 ^ 40 * 6181758 * 2
def baseEnd_6181758 : Nat := 3174213143776530077095619

theorem tailTrace_6181758 : CollatzResearch.WordTrace tailWord_6181758 prefixEnd_6181758 3174213143776530077095619 := by
  unfold tailWord_6181758
  simp only [CollatzResearch.WordTrace]
  refine ⟨28183404642319250132268241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150311491425702667372097285 28183404642319250132268241)
  ·
    refine ⟨21137553481739437599201181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28183404642319250132268241 21137553481739437599201181)
    ·
      refine ⟨7926582555652289099700443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21137553481739437599201181 7926582555652289099700443)
      ·
        refine ⟨11889873833478433649550665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926582555652289099700443 11889873833478433649550665)
        ·
          refine ⟨8917405375108825237162999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11889873833478433649550665 8917405375108825237162999)
          ·
            refine ⟨13376108062663237855744499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917405375108825237162999 13376108062663237855744499)
            ·
              refine ⟨20064162093994856783616749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13376108062663237855744499 20064162093994856783616749)
              ·
                refine ⟨7524060785248071293856281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20064162093994856783616749 7524060785248071293856281)
                ·
                  refine ⟨5643045588936053470392211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7524060785248071293856281 5643045588936053470392211)
                  ·
                    refine ⟨8464568383404080205588317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643045588936053470392211 8464568383404080205588317)
                    ·
                      refine ⟨3174213143776530077095619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8464568383404080205588317 3174213143776530077095619)
                      ·
                        rfl

theorem cell23_6181758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6181758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181758 prefixEnd_6181758 := by exact prefixLift 6181758
  have htrace : WordTrace (prefixWord ++ tailWord_6181758) baseStart_6181758 baseEnd_6181758 := by
    simpa [prefixWord, tailWord_6181758, baseEnd_6181758] using wordTrace_append hprefix tailTrace_6181758
  have hstable : (prefixWord ++ tailWord_6181758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181758).length < 2 ^ (prefixWord ++ tailWord_6181758).sum := by decide
  have hdescent : baseEnd_6181758 < baseStart_6181758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181857 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_6181857 : Nat := 118140960795 + 6181857 * 2 ^ 59
def prefixEnd_6181857 : Nat := 4983230072969 + 3 ^ 40 * 6181857 * 2
def baseEnd_6181857 : Nat := 3174263978361325189757663

theorem tailTrace_6181857 : CollatzResearch.WordTrace tailWord_6181857 prefixEnd_6181857 3174263978361325189757663 := by
  unfold tailWord_6181857
  simp only [CollatzResearch.WordTrace]
  refine ⟨225470847965195340965999825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150313898643463560643999883 225470847965195340965999825)
  ·
    refine ⟨169103135973896505724499869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225470847965195340965999825 169103135973896505724499869)
    ·
      refine ⟨63413675990211189646687451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169103135973896505724499869 63413675990211189646687451)
      ·
        refine ⟨95120513985316784470031177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63413675990211189646687451 95120513985316784470031177)
        ·
          refine ⟨71340385488987588352523383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95120513985316784470031177 71340385488987588352523383)
          ·
            refine ⟨107010578233481382528785075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71340385488987588352523383 107010578233481382528785075)
            ·
              refine ⟨160515867350222073793177613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107010578233481382528785075 160515867350222073793177613)
              ·
                refine ⟨60193450256333277672441605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160515867350222073793177613 60193450256333277672441605)
                ·
                  refine ⟨11286271923062489563582801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60193450256333277672441605 11286271923062489563582801)
                  ·
                    refine ⟨8464703942296867172687101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11286271923062489563582801 8464703942296867172687101)
                    ·
                      refine ⟨3174263978361325189757663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8464703942296867172687101 3174263978361325189757663)
                      ·
                        rfl

theorem cell23_6181857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_6181857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181857 prefixEnd_6181857 := by exact prefixLift 6181857
  have htrace : WordTrace (prefixWord ++ tailWord_6181857) baseStart_6181857 baseEnd_6181857 := by
    simpa [prefixWord, tailWord_6181857, baseEnd_6181857] using wordTrace_append hprefix tailTrace_6181857
  have hstable : (prefixWord ++ tailWord_6181857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181857).length < 2 ^ (prefixWord ++ tailWord_6181857).sum := by decide
  have hdescent : baseEnd_6181857 < baseStart_6181857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181880 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 6]
def baseStart_6181880 : Nat := 118140960795 + 6181880 * 2 ^ 59
def prefixEnd_6181880 : Nat := 4983230072969 + 3 ^ 40 * 6181880 * 2
def baseEnd_6181880 : Nat := 3174275788416378599770057

theorem tailTrace_6181880 : CollatzResearch.WordTrace tailWord_6181880 prefixEnd_6181880 3174275788416378599770057 := by
  unfold tailWord_6181880
  simp only [CollatzResearch.WordTrace]
  refine ⟨112735843422056007947043547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150314457896074677262724729 112735843422056007947043547)
  ·
    refine ⟨169103765133084011920565321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112735843422056007947043547 169103765133084011920565321)
    ·
      refine ⟨126827823849813008940423991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169103765133084011920565321 126827823849813008940423991)
      ·
        refine ⟨190241735774719513410635987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126827823849813008940423991 190241735774719513410635987)
        ·
          refine ⟨285362603662079270115953981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190241735774719513410635987 285362603662079270115953981)
          ·
            refine ⟨107010976373279726293482743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285362603662079270115953981 107010976373279726293482743)
            ·
              refine ⟨160516464559919589440224115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107010976373279726293482743 160516464559919589440224115)
              ·
                refine ⟨240774696839879384160336173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160516464559919589440224115 240774696839879384160336173)
                ·
                  refine ⟨90290511314954769060126065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240774696839879384160336173 90290511314954769060126065)
                  ·
                    refine ⟨67717883486216076795094549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90290511314954769060126065 67717883486216076795094549)
                    ·
                      refine ⟨3174275788416378599770057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67717883486216076795094549 3174275788416378599770057)
                      ·
                        rfl

theorem cell23_6181880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_6181880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181880 prefixEnd_6181880 := by exact prefixLift 6181880
  have htrace : WordTrace (prefixWord ++ tailWord_6181880) baseStart_6181880 baseEnd_6181880 := by
    simpa [prefixWord, tailWord_6181880, baseEnd_6181880] using wordTrace_append hprefix tailTrace_6181880
  have hstable : (prefixWord ++ tailWord_6181880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181880).length < 2 ^ (prefixWord ++ tailWord_6181880).sum := by decide
  have hdescent : baseEnd_6181880 < baseStart_6181880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181898 : List Nat := [3, 1, 2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_6181898 : Nat := 118140960795 + 6181898 * 2 ^ 59
def prefixEnd_6181898 : Nat := 4983230072969 + 3 ^ 40 * 6181898 * 2
def baseEnd_6181898 : Nat := 1058095010356053176448325

theorem tailTrace_6181898 : CollatzResearch.WordTrace tailWord_6181898 prefixEnd_6181898 1058095010356053176448325 := by
  unfold tailWord_6181898
  simp only [CollatzResearch.WordTrace]
  refine ⟨56368085839511701242060587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150314895572031203312161565 56368085839511701242060587)
  ·
    refine ⟨84552128759267551863090881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56368085839511701242060587 84552128759267551863090881)
    ·
      refine ⟨63414096569450663897318161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84552128759267551863090881 63414096569450663897318161)
      ·
        refine ⟨47560572427087997922988621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63414096569450663897318161 47560572427087997922988621)
        ·
          refine ⟨17835214660157999221120733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47560572427087997922988621 17835214660157999221120733)
          ·
            refine ⟨6688205497559249707920275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17835214660157999221120733 6688205497559249707920275)
            ·
              refine ⟨10032308246338874561880413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688205497559249707920275 10032308246338874561880413)
              ·
                refine ⟨3762115592377077960705155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10032308246338874561880413 3762115592377077960705155)
                ·
                  refine ⟨5643173388565616941057733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762115592377077960705155 5643173388565616941057733)
                  ·
                    refine ⟨1058095010356053176448325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5643173388565616941057733 1058095010356053176448325)
                    ·
                      rfl

theorem cell23_6181898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_6181898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181898 prefixEnd_6181898 := by exact prefixLift 6181898
  have htrace : WordTrace (prefixWord ++ tailWord_6181898) baseStart_6181898 baseEnd_6181898 := by
    simpa [prefixWord, tailWord_6181898, baseEnd_6181898] using wordTrace_append hprefix tailTrace_6181898
  have hstable : (prefixWord ++ tailWord_6181898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181898).length < 2 ^ (prefixWord ++ tailWord_6181898).sum := by decide
  have hdescent : baseEnd_6181898 < baseStart_6181898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181921 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_6181921 : Nat := 118140960795 + 6181921 * 2 ^ 59
def prefixEnd_6181921 : Nat := 4983230072969 + 3 ^ 40 * 6181921 * 2
def baseEnd_6181921 : Nat := 3174296841123212939357369

theorem tailTrace_6181921 : CollatzResearch.WordTrace tailWord_6181921 prefixEnd_6181921 3174296841123212939357369 := by
  unfold tailWord_6181921
  simp only [CollatzResearch.WordTrace]
  refine ⟨225473182236963479896329617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150315454824642319930886411 225473182236963479896329617)
  ·
    refine ⟨169104886677722609922247213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225473182236963479896329617 169104886677722609922247213)
    ·
      refine ⟨63414332504145978720842705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169104886677722609922247213 63414332504145978720842705)
      ·
        refine ⟨47560749378109484040632029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63414332504145978720842705 47560749378109484040632029)
        ·
          refine ⟨17835281016791056515237011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47560749378109484040632029 17835281016791056515237011)
          ·
            refine ⟨26752921525186584772855517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17835281016791056515237011 26752921525186584772855517)
            ·
              refine ⟨10032345571944969289820819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26752921525186584772855517 10032345571944969289820819)
              ·
                refine ⟨15048518357917453934731229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10032345571944969289820819 15048518357917453934731229)
                ·
                  refine ⟨5643194384219045225524211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15048518357917453934731229 5643194384219045225524211)
                  ·
                    refine ⟨8464791576328567838286317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643194384219045225524211 8464791576328567838286317)
                    ·
                      refine ⟨3174296841123212939357369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8464791576328567838286317 3174296841123212939357369)
                      ·
                        rfl

theorem cell23_6181921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_6181921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181921 prefixEnd_6181921 := by exact prefixLift 6181921
  have htrace : WordTrace (prefixWord ++ tailWord_6181921) baseStart_6181921 baseEnd_6181921 := by
    simpa [prefixWord, tailWord_6181921, baseEnd_6181921] using wordTrace_append hprefix tailTrace_6181921
  have hstable : (prefixWord ++ tailWord_6181921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181921).length < 2 ^ (prefixWord ++ tailWord_6181921).sum := by decide
  have hdescent : baseEnd_6181921 < baseStart_6181921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181937 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 1, 6]
def baseStart_6181937 : Nat := 118140960795 + 6181937 * 2 ^ 59
def prefixEnd_6181937 : Nat := 4983230072969 + 3 ^ 40 * 6181937 * 2
def baseEnd_6181937 : Nat := 1058101685604561625585765

theorem tailTrace_6181937 : CollatzResearch.WordTrace tailWord_6181937 prefixEnd_6181937 1058101685604561625585765 := by
  unfold tailWord_6181937
  simp only [CollatzResearch.WordTrace]
  refine ⟨225473765804905514628912065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150315843869937009752608043 225473765804905514628912065)
  ·
    refine ⟨169105324353679135971684049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225473765804905514628912065 169105324353679135971684049)
    ·
      refine ⟨126828993265259351978763037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169105324353679135971684049 126828993265259351978763037)
      ·
        refine ⟨47560872474472256992036139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126828993265259351978763037 47560872474472256992036139)
        ·
          refine ⟨71341308711708385488054209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47560872474472256992036139 71341308711708385488054209)
          ·
            refine ⟨53505981533781289116040657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71341308711708385488054209 53505981533781289116040657)
            ·
              refine ⟨40129486150335966837030493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53505981533781289116040657 40129486150335966837030493)
              ·
                refine ⟨15048557306375987563886435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40129486150335966837030493 15048557306375987563886435)
                ·
                  refine ⟨22572835959563981345829653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15048557306375987563886435 22572835959563981345829653)
                  ·
                    refine ⟨1058101685604561625585765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22572835959563981345829653 1058101685604561625585765)
                    ·
                      rfl

theorem cell23_6181937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_6181937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181937 prefixEnd_6181937 := by exact prefixLift 6181937
  have htrace : WordTrace (prefixWord ++ tailWord_6181937) baseStart_6181937 baseEnd_6181937 := by
    simpa [prefixWord, tailWord_6181937, baseEnd_6181937] using wordTrace_append hprefix tailTrace_6181937
  have hstable : (prefixWord ++ tailWord_6181937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181937).length < 2 ^ (prefixWord ++ tailWord_6181937).sum := by decide
  have hdescent : baseEnd_6181937 < baseStart_6181937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181944 : List Nat := [2, 1, 2, 1, 5, 2, 1, 1, 3, 1, 4]
def baseStart_6181944 : Nat := 118140960795 + 6181944 * 2 ^ 59
def prefixEnd_6181944 : Nat := 4983230072969 + 3 ^ 40 * 6181944 * 2
def baseEnd_6181944 : Nat := 3174308651178266349369763

theorem tailTrace_6181944 : CollatzResearch.WordTrace tailWord_6181944 prefixEnd_6181944 3174308651178266349369763 := by
  unfold tailWord_6181944
  simp only [CollatzResearch.WordTrace]
  refine ⟨112737010557940077412208443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150316014077253436549611257 112737010557940077412208443)
  ·
    refine ⟨169105515836910116118312665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112737010557940077412208443 169105515836910116118312665)
    ·
      refine ⟨126829136877682587088734499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169105515836910116118312665 126829136877682587088734499)
      ·
        refine ⟨190243705316523880633101749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126829136877682587088734499 190243705316523880633101749)
        ·
          refine ⟨17835347373424113809353289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190243705316523880633101749 17835347373424113809353289)
          ·
            refine ⟨13376510530068085357014967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17835347373424113809353289 13376510530068085357014967)
            ·
              refine ⟨20064765795102128035522451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13376510530068085357014967 20064765795102128035522451)
              ·
                refine ⟨30097148692653192053283677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20064765795102128035522451 30097148692653192053283677)
                ·
                  refine ⟨11286430759744947019981379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30097148692653192053283677 11286430759744947019981379)
                  ·
                    refine ⟨16929646139617420529972069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11286430759744947019981379 16929646139617420529972069)
                    ·
                      refine ⟨3174308651178266349369763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16929646139617420529972069 3174308651178266349369763)
                      ·
                        rfl

theorem cell23_6181944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_6181944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181944 prefixEnd_6181944 := by exact prefixLift 6181944
  have htrace : WordTrace (prefixWord ++ tailWord_6181944) baseStart_6181944 baseEnd_6181944 := by
    simpa [prefixWord, tailWord_6181944, baseEnd_6181944] using wordTrace_append hprefix tailTrace_6181944
  have hstable : (prefixWord ++ tailWord_6181944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181944).length < 2 ^ (prefixWord ++ tailWord_6181944).sum := by decide
  have hdescent : baseEnd_6181944 < baseStart_6181944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6181957 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 4]
def baseStart_6181957 : Nat := 118140960795 + 6181957 * 2 ^ 59
def prefixEnd_6181957 : Nat := 4983230072969 + 3 ^ 40 * 6181957 * 2
def baseEnd_6181957 : Nat := 3174315326426774798507203

theorem tailTrace_6181957 : CollatzResearch.WordTrace tailWord_6181957 prefixEnd_6181957 3174315326426774798507203 := by
  unfold tailWord_6181957
  simp only [CollatzResearch.WordTrace]
  refine ⟨225474495264833058044640125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150316330176555372029760083 225474495264833058044640125)
  ·
    refine ⟨84552935724312396766740047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225474495264833058044640125 84552935724312396766740047)
    ·
      refine ⟨126829403586468595150110071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84552935724312396766740047 126829403586468595150110071)
      ·
        refine ⟨190244105379702892725165107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126829403586468595150110071 190244105379702892725165107)
        ·
          refine ⟨285366158069554339087747661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190244105379702892725165107 285366158069554339087747661)
          ·
            refine ⟨107012309276082877157905373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285366158069554339087747661 107012309276082877157905373)
            ·
              refine ⟨40129615978531078934214515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107012309276082877157905373 40129615978531078934214515)
              ·
                refine ⟨60194423967796618401321773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40129615978531078934214515 60194423967796618401321773)
                ·
                  refine ⟨22572908987923731900495665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60194423967796618401321773 22572908987923731900495665)
                  ·
                    refine ⟨16929681740942798925371749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22572908987923731900495665 16929681740942798925371749)
                    ·
                      refine ⟨3174315326426774798507203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16929681740942798925371749 3174315326426774798507203)
                      ·
                        rfl

theorem cell23_6181957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_6181957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6181957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6181957 prefixEnd_6181957 := by exact prefixLift 6181957
  have htrace : WordTrace (prefixWord ++ tailWord_6181957) baseStart_6181957 baseEnd_6181957 := by
    simpa [prefixWord, tailWord_6181957, baseEnd_6181957] using wordTrace_append hprefix tailTrace_6181957
  have hstable : (prefixWord ++ tailWord_6181957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6181957).length < 2 ^ (prefixWord ++ tailWord_6181957).sum := by decide
  have hdescent : baseEnd_6181957 < baseStart_6181957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6181957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182007 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_6182007 : Nat := 118140960795 + 6182007 * 2 ^ 59
def prefixEnd_6182007 : Nat := 4983230072969 + 3 ^ 40 * 6182007 * 2
def baseEnd_6182007 : Nat := 3174341000459499602881973

theorem tailTrace_6182007 : CollatzResearch.WordTrace tailWord_6182007 prefixEnd_6182007 3174341000459499602881973 := by
  unfold tailWord_6182007
  simp only [CollatzResearch.WordTrace]
  refine ⟨225476318914651916583960275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150317545943101277722640183 225476318914651916583960275)
  ·
    refine ⟨338214478371977874875940413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225476318914651916583960275 338214478371977874875940413)
    ·
      refine ⟨126830429389491703078477655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338214478371977874875940413 126830429389491703078477655)
      ·
        refine ⟨190245644084237554617716483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126830429389491703078477655 190245644084237554617716483)
        ·
          refine ⟨285368466126356331926574725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190245644084237554617716483 285368466126356331926574725)
          ·
            refine ⟨53506587398691812236232761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285368466126356331926574725 53506587398691812236232761)
            ·
              refine ⟨40129940549018859177174571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53506587398691812236232761 40129940549018859177174571)
              ·
                refine ⟨60194910823528288765761857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40129940549018859177174571 60194910823528288765761857)
                ·
                  refine ⟨45146183117646216574321393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60194910823528288765761857 45146183117646216574321393)
                  ·
                    refine ⟨33859637338234662430741045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45146183117646216574321393 33859637338234662430741045)
                    ·
                      refine ⟨3174341000459499602881973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33859637338234662430741045 3174341000459499602881973)
                      ·
                        rfl

theorem cell23_6182007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_6182007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182007 prefixEnd_6182007 := by exact prefixLift 6182007
  have htrace : WordTrace (prefixWord ++ tailWord_6182007) baseStart_6182007 baseEnd_6182007 := by
    simpa [prefixWord, tailWord_6182007, baseEnd_6182007] using wordTrace_append hprefix tailTrace_6182007
  have hstable : (prefixWord ++ tailWord_6182007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182007).length < 2 ^ (prefixWord ++ tailWord_6182007).sum := by decide
  have hdescent : baseEnd_6182007 < baseStart_6182007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182037 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 5]
def baseStart_6182037 : Nat := 118140960795 + 6182037 * 2 ^ 59
def prefixEnd_6182037 : Nat := 4983230072969 + 3 ^ 40 * 6182037 * 2
def baseEnd_6182037 : Nat := 3174356404879134485506835

theorem tailTrace_6182037 : CollatzResearch.WordTrace tailWord_6182037 prefixEnd_6182037 3174356404879134485506835 := by
  unfold tailWord_6182037
  simp only [CollatzResearch.WordTrace]
  refine ⟨225477413104543231707552365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150318275403028821138368243 225477413104543231707552365)
  ·
    refine ⟨84554029914203711890332137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225477413104543231707552365 84554029914203711890332137)
    ·
      refine ⟨63415522435652783917749103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84554029914203711890332137 63415522435652783917749103)
      ·
        refine ⟨95123283653479175876623655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63415522435652783917749103 95123283653479175876623655)
        ·
          refine ⟨142684925480218763814935483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95123283653479175876623655 142684925480218763814935483)
          ·
            refine ⟨214027388220328145722403225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142684925480218763814935483 214027388220328145722403225)
            ·
              refine ⟨160520541165246109291802419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214027388220328145722403225 160520541165246109291802419)
              ·
                refine ⟨240780811747869163937703629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160520541165246109291802419 240780811747869163937703629)
                ·
                  refine ⟨90292804405450936476638861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240780811747869163937703629 90292804405450936476638861)
                  ·
                    refine ⟨33859801652044101178739573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90292804405450936476638861 33859801652044101178739573)
                    ·
                      refine ⟨3174356404879134485506835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33859801652044101178739573 3174356404879134485506835)
                      ·
                        rfl

theorem cell23_6182037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_6182037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182037 prefixEnd_6182037 := by exact prefixLift 6182037
  have htrace : WordTrace (prefixWord ++ tailWord_6182037) baseStart_6182037 baseEnd_6182037 := by
    simpa [prefixWord, tailWord_6182037, baseEnd_6182037] using wordTrace_append hprefix tailTrace_6182037
  have hstable : (prefixWord ++ tailWord_6182037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182037).length < 2 ^ (prefixWord ++ tailWord_6182037).sum := by decide
  have hdescent : baseEnd_6182037 < baseStart_6182037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182044 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 2, 6]
def baseStart_6182044 : Nat := 118140960795 + 6182044 * 2 ^ 59
def prefixEnd_6182044 : Nat := 4983230072969 + 3 ^ 40 * 6182044 * 2
def baseEnd_6182044 : Nat := 1058119999747905319373101

theorem tailTrace_6182044 : CollatzResearch.WordTrace tailWord_6182044 prefixEnd_6182044 1058119999747905319373101 := by
  unfold tailWord_6182044
  simp only [CollatzResearch.WordTrace]
  refine ⟨112738834207758935951528593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150318445610345247935371457 112738834207758935951528593)
  ·
    refine ⟨84554125655819201963646445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112738834207758935951528593 84554125655819201963646445)
    ·
      refine ⟨31707797120932200736367417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84554125655819201963646445 31707797120932200736367417)
      ·
        refine ⟨23780847840699150552275563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31707797120932200736367417 23780847840699150552275563)
        ·
          refine ⟨35671271761048725828413345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23780847840699150552275563 35671271761048725828413345)
          ·
            refine ⟨26753453820786544371310009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35671271761048725828413345 26753453820786544371310009)
            ·
              refine ⟨20065090365589908278482507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26753453820786544371310009 20065090365589908278482507)
              ·
                refine ⟨30097635548384862417723761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20065090365589908278482507 30097635548384862417723761)
                ·
                  refine ⟨22573226661288646813292821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30097635548384862417723761 22573226661288646813292821)
                  ·
                    refine ⟨1058119999747905319373101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22573226661288646813292821 1058119999747905319373101)
                    ·
                      rfl

theorem cell23_6182044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_6182044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182044 prefixEnd_6182044 := by exact prefixLift 6182044
  have htrace : WordTrace (prefixWord ++ tailWord_6182044) baseStart_6182044 baseEnd_6182044 := by
    simpa [prefixWord, tailWord_6182044, baseEnd_6182044] using wordTrace_append hprefix tailTrace_6182044
  have hstable : (prefixWord ++ tailWord_6182044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182044).length < 2 ^ (prefixWord ++ tailWord_6182044).sum := by decide
  have hdescent : baseEnd_6182044 < baseStart_6182044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182055 : List Nat := [1, 1, 6, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_6182055 : Nat := 118140960795 + 6182055 * 2 ^ 59
def prefixEnd_6182055 : Nat := 4983230072969 + 3 ^ 40 * 6182055 * 2
def baseEnd_6182055 : Nat := 3174365647530915415081753

theorem tailTrace_6182055 : CollatzResearch.WordTrace tailWord_6182055 prefixEnd_6182055 3174365647530915415081753 := by
  unfold tailWord_6182055
  simp only [CollatzResearch.WordTrace]
  refine ⟨225478069618478020781707619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150318713078985347187805079 225478069618478020781707619)
  ·
    refine ⟨338217104427717031172561429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225478069618478020781707619 338217104427717031172561429)
    ·
      refine ⟨15853926770049235836213817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 338217104427717031172561429 15853926770049235836213817)
      ·
        refine ⟨11890445077536926877160363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15853926770049235836213817 11890445077536926877160363)
        ·
          refine ⟨17835667616305390315740545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11890445077536926877160363 17835667616305390315740545)
          ·
            refine ⟨13376750712229042736805409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17835667616305390315740545 13376750712229042736805409)
            ·
              refine ⟨10032563034171782052604057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13376750712229042736805409 10032563034171782052604057)
              ·
                refine ⟨7524422275628836539453043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10032563034171782052604057 7524422275628836539453043)
                ·
                  refine ⟨11286633413443254809179565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7524422275628836539453043 11286633413443254809179565)
                  ·
                    refine ⟨4232487530041220553442337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11286633413443254809179565 4232487530041220553442337)
                    ·
                      refine ⟨3174365647530915415081753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232487530041220553442337 3174365647530915415081753)
                      ·
                        rfl

theorem cell23_6182055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_6182055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182055 prefixEnd_6182055 := by exact prefixLift 6182055
  have htrace : WordTrace (prefixWord ++ tailWord_6182055) baseStart_6182055 baseEnd_6182055 := by
    simpa [prefixWord, tailWord_6182055, baseEnd_6182055] using wordTrace_append hprefix tailTrace_6182055
  have hstable : (prefixWord ++ tailWord_6182055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182055).length < 2 ^ (prefixWord ++ tailWord_6182055).sum := by decide
  have hdescent : baseEnd_6182055 < baseStart_6182055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182144 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3]
def baseStart_6182144 : Nat := 118140960795 + 6182144 * 2 ^ 59
def prefixEnd_6182144 : Nat := 4983230072969 + 3 ^ 40 * 6182144 * 2
def baseEnd_6182144 : Nat := 3174411347309165566868843

theorem tailTrace_6182144 : CollatzResearch.WordTrace tailWord_6182144 prefixEnd_6182144 3174411347309165566868843 := by
  unfold tailWord_6182144
  simp only [CollatzResearch.WordTrace]
  refine ⟨112740657857577794490848743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150320877143437059321131657 112740657857577794490848743)
  ·
    refine ⟨169110986786366691736273115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112740657857577794490848743 169110986786366691736273115)
    ·
      refine ⟨253666480179550037604409673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169110986786366691736273115 253666480179550037604409673)
      ·
        refine ⟨190249860134662528203307255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253666480179550037604409673 190249860134662528203307255)
        ·
          refine ⟨285374790201993792304960883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190249860134662528203307255 285374790201993792304960883)
          ·
            refine ⟨428062185302990688457441325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285374790201993792304960883 428062185302990688457441325)
            ·
              refine ⟨160523319488621508171540497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428062185302990688457441325 160523319488621508171540497)
              ·
                refine ⟨120392489616466131128655373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160523319488621508171540497 120392489616466131128655373)
                ·
                  refine ⟨45147183606174799173245765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120392489616466131128655373 45147183606174799173245765)
                  ·
                    refine ⟨8465096926157774844983581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45147183606174799173245765 8465096926157774844983581)
                    ·
                      refine ⟨3174411347309165566868843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465096926157774844983581 3174411347309165566868843)
                      ·
                        rfl

theorem cell23_6182144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_6182144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182144 prefixEnd_6182144 := by exact prefixLift 6182144
  have htrace : WordTrace (prefixWord ++ tailWord_6182144) baseStart_6182144 baseEnd_6182144 := by
    simpa [prefixWord, tailWord_6182144, baseEnd_6182144] using wordTrace_append hprefix tailTrace_6182144
  have hstable : (prefixWord ++ tailWord_6182144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182144).length < 2 ^ (prefixWord ++ tailWord_6182144).sum := by decide
  have hdescent : baseEnd_6182144 < baseStart_6182144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182154 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6182154 : Nat := 118140960795 + 6182154 * 2 ^ 59
def prefixEnd_6182154 : Nat := 4983230072969 + 3 ^ 40 * 6182154 * 2
def baseEnd_6182154 : Nat := 3174416482115710527743797

theorem tailTrace_6182154 : CollatzResearch.WordTrace tailWord_6182154 prefixEnd_6182154 3174416482115710527743797 := by
  unfold tailWord_6182154
  simp only [CollatzResearch.WordTrace]
  refine ⟨56370420111279840172390379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150321120296746240459707677 56370420111279840172390379)
  ·
    refine ⟨84555630166919760258585569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56370420111279840172390379 84555630166919760258585569)
    ·
      refine ⟨63416722625189820193939177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84555630166919760258585569 63416722625189820193939177)
      ·
        refine ⟨47562541968892365145454383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63416722625189820193939177 47562541968892365145454383)
        ·
          refine ⟨71343812953338547718181575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47562541968892365145454383 71343812953338547718181575)
          ·
            refine ⟨107015719430007821577272363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71343812953338547718181575 107015719430007821577272363)
            ·
              refine ⟨160523579145011732365908545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107015719430007821577272363 160523579145011732365908545)
              ·
                refine ⟨120392684358758799274431409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160523579145011732365908545 120392684358758799274431409)
                ·
                  refine ⟨90294513269069099455823557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120392684358758799274431409 90294513269069099455823557)
                  ·
                    refine ⟨16930221237950456147966917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90294513269069099455823557 16930221237950456147966917)
                    ·
                      refine ⟨3174416482115710527743797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16930221237950456147966917 3174416482115710527743797)
                      ·
                        rfl

theorem cell23_6182154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6182154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182154 prefixEnd_6182154 := by exact prefixLift 6182154
  have htrace : WordTrace (prefixWord ++ tailWord_6182154) baseStart_6182154 baseEnd_6182154 := by
    simpa [prefixWord, tailWord_6182154, baseEnd_6182154] using wordTrace_append hprefix tailTrace_6182154
  have hstable : (prefixWord ++ tailWord_6182154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182154).length < 2 ^ (prefixWord ++ tailWord_6182154).sum := by decide
  have hdescent : baseEnd_6182154 < baseStart_6182154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182158 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2]
def baseStart_6182158 : Nat := 118140960795 + 6182158 * 2 ^ 59
def prefixEnd_6182158 : Nat := 4983230072969 + 3 ^ 40 * 6182158 * 2
def baseEnd_6182158 : Nat := 3174418536038328512093779

theorem tailTrace_6182158 : CollatzResearch.WordTrace tailWord_6182158 prefixEnd_6182158 3174418536038328512093779 := by
  unfold tailWord_6182158
  simp only [CollatzResearch.WordTrace]
  refine ⟨28185228292138108671588391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150321217558069912915138085 28185228292138108671588391)
  ·
    refine ⟨42277842438207163007382587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28185228292138108671588391 42277842438207163007382587)
    ·
      refine ⟨63416763657310744511073881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42277842438207163007382587 63416763657310744511073881)
      ·
        refine ⟨47562572742983058383305411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63416763657310744511073881 47562572742983058383305411)
        ·
          refine ⟨71343859114474587574958117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47562572742983058383305411 71343859114474587574958117)
          ·
            refine ⟨13376973583963985170304647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71343859114474587574958117 13376973583963985170304647)
            ·
              refine ⟨20065460375945977755456971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13376973583963985170304647 20065460375945977755456971)
              ·
                refine ⟨30098190563918966633185457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20065460375945977755456971 30098190563918966633185457)
                ·
                  refine ⟨22573642922939224974889093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30098190563918966633185457 22573642922939224974889093)
                  ·
                    refine ⟨4232558048051104682791705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22573642922939224974889093 4232558048051104682791705)
                    ·
                      refine ⟨3174418536038328512093779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232558048051104682791705 3174418536038328512093779)
                      ·
                        rfl

theorem cell23_6182158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_6182158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182158 prefixEnd_6182158 := by exact prefixLift 6182158
  have htrace : WordTrace (prefixWord ++ tailWord_6182158) baseStart_6182158 baseEnd_6182158 := by
    simpa [prefixWord, tailWord_6182158, baseEnd_6182158] using wordTrace_append hprefix tailTrace_6182158
  have hstable : (prefixWord ++ tailWord_6182158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182158).length < 2 ^ (prefixWord ++ tailWord_6182158).sum := by decide
  have hdescent : baseEnd_6182158 < baseStart_6182158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182175 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 2, 1, 4]
def baseStart_6182175 : Nat := 118140960795 + 6182175 * 2 ^ 59
def prefixEnd_6182175 : Nat := 4983230072969 + 3 ^ 40 * 6182175 * 2
def baseEnd_6182175 : Nat := 3174427265209454945581201

theorem tailTrace_6182175 : CollatzResearch.WordTrace tailWord_6182175 prefixEnd_6182175 3174427265209454945581201 := by
  unfold tailWord_6182175
  simp only [CollatzResearch.WordTrace]
  refine ⟨225482446378043281276075979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150321630918695520850717319 225482446378043281276075979)
  ·
    refine ⟨338223669567064921914113969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225482446378043281276075979 338223669567064921914113969)
    ·
      refine ⟨253667752175298691435585477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338223669567064921914113969 253667752175298691435585477)
      ·
        refine ⟨47562703532868504644172277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253667752175298691435585477 47562703532868504644172277)
        ·
          refine ⟨4459003456206422310391151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47562703532868504644172277 4459003456206422310391151)
          ·
            refine ⟨6688505184309633465586727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459003456206422310391151 6688505184309633465586727)
            ·
              refine ⟨10032757776464450198380091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688505184309633465586727 10032757776464450198380091)
              ·
                refine ⟨15049136664696675297570137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10032757776464450198380091 15049136664696675297570137)
                ·
                  refine ⟨11286852498522506473177603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15049136664696675297570137 11286852498522506473177603)
                  ·
                    refine ⟨16930278747783759709766405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11286852498522506473177603 16930278747783759709766405)
                    ·
                      refine ⟨3174427265209454945581201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16930278747783759709766405 3174427265209454945581201)
                      ·
                        rfl

theorem cell23_6182175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_6182175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182175 prefixEnd_6182175 := by exact prefixLift 6182175
  have htrace : WordTrace (prefixWord ++ tailWord_6182175) baseStart_6182175 baseEnd_6182175 := by
    simpa [prefixWord, tailWord_6182175, baseEnd_6182175] using wordTrace_append hprefix tailTrace_6182175
  have hstable : (prefixWord ++ tailWord_6182175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182175).length < 2 ^ (prefixWord ++ tailWord_6182175).sum := by decide
  have hdescent : baseEnd_6182175 < baseStart_6182175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182178 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_6182178 : Nat := 118140960795 + 6182178 * 2 ^ 59
def prefixEnd_6182178 : Nat := 4983230072969 + 3 ^ 40 * 6182178 * 2
def baseEnd_6182178 : Nat := 3174428805651418433843687

theorem tailTrace_6182178 : CollatzResearch.WordTrace tailWord_6182178 prefixEnd_6182178 3174428805651418433843687 := by
  unfold tailWord_6182178
  simp only [CollatzResearch.WordTrace]
  refine ⟨56370638949258103197108797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150321703864688275192290125 56370638949258103197108797)
  ·
    refine ⟨21138989605971788698915799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56370638949258103197108797 21138989605971788698915799)
    ·
      refine ⟨31708484408957683048373699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21138989605971788698915799 31708484408957683048373699)
      ·
        refine ⟨47562726613436524572560549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31708484408957683048373699 47562726613436524572560549)
        ·
          refine ⟨8918011240019348357355103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47562726613436524572560549 8918011240019348357355103)
          ·
            refine ⟨13377016860029022536032655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8918011240019348357355103 13377016860029022536032655)
            ·
              refine ⟨20065525290043533804048983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13377016860029022536032655 20065525290043533804048983)
              ·
                refine ⟨30098287935065300706073475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20065525290043533804048983 30098287935065300706073475)
                ·
                  refine ⟨45147431902597951059110213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30098287935065300706073475 45147431902597951059110213)
                  ·
                    refine ⟨8465143481737115823583165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45147431902597951059110213 8465143481737115823583165)
                    ·
                      refine ⟨3174428805651418433843687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465143481737115823583165 3174428805651418433843687)
                      ·
                        rfl

theorem cell23_6182178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_6182178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182178 prefixEnd_6182178 := by exact prefixLift 6182178
  have htrace : WordTrace (prefixWord ++ tailWord_6182178) baseStart_6182178 baseEnd_6182178 := by
    simpa [prefixWord, tailWord_6182178, baseEnd_6182178] using wordTrace_append hprefix tailTrace_6182178
  have hstable : (prefixWord ++ tailWord_6182178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182178).length < 2 ^ (prefixWord ++ tailWord_6182178).sum := by decide
  have hdescent : baseEnd_6182178 < baseStart_6182178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182191 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 3]
def baseStart_6182191 : Nat := 118140960795 + 6182191 * 2 ^ 59
def prefixEnd_6182191 : Nat := 4983230072969 + 3 ^ 40 * 6182191 * 2
def baseEnd_6182191 : Nat := 3174435480899926882981127

theorem tailTrace_6182191 : CollatzResearch.WordTrace tailWord_6182191 prefixEnd_6182191 3174435480899926882981127 := by
  unfold tailWord_6182191
  simp only [CollatzResearch.WordTrace]
  refine ⟨225483029945985316008658427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150322019963990210672438951 225483029945985316008658427)
  ·
    refine ⟨338224544918977974012987641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225483029945985316008658427 338224544918977974012987641)
    ·
      refine ⟨253668408689233480509740731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338224544918977974012987641 253668408689233480509740731)
      ·
        refine ⟨380502613033850220764611097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253668408689233480509740731 380502613033850220764611097)
        ·
          refine ⟨285376959775387665573458323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380502613033850220764611097 285376959775387665573458323)
          ·
            refine ⟨428065439663081498360187485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285376959775387665573458323 428065439663081498360187485)
            ·
              refine ⟨160524539873655561885070307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 428065439663081498360187485 160524539873655561885070307)
              ·
                refine ⟨240786809810483342827605461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160524539873655561885070307 240786809810483342827605461)
                ·
                  refine ⟨5643440854933203347522003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 240786809810483342827605461 5643440854933203347522003)
                  ·
                    refine ⟨8465161282399805021283005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643440854933203347522003 8465161282399805021283005)
                    ·
                      refine ⟨3174435480899926882981127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465161282399805021283005 3174435480899926882981127)
                      ·
                        rfl

theorem cell23_6182191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 1, 3].length) (baseStart_6182191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182191 prefixEnd_6182191 := by exact prefixLift 6182191
  have htrace : WordTrace (prefixWord ++ tailWord_6182191) baseStart_6182191 baseEnd_6182191 := by
    simpa [prefixWord, tailWord_6182191, baseEnd_6182191] using wordTrace_append hprefix tailTrace_6182191
  have hstable : (prefixWord ++ tailWord_6182191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182191).length < 2 ^ (prefixWord ++ tailWord_6182191).sum := by decide
  have hdescent : baseEnd_6182191 < baseStart_6182191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182208 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 3, 1, 3]
def baseStart_6182208 : Nat := 118140960795 + 6182208 * 2 ^ 59
def prefixEnd_6182208 : Nat := 4983230072969 + 3 ^ 40 * 6182208 * 2
def baseEnd_6182208 : Nat := 3174444210071053316468549

theorem tailTrace_6182208 : CollatzResearch.WordTrace tailWord_6182208 prefixEnd_6182208 3174444210071053316468549 := by
  unfold tailWord_6182208
  simp only [CollatzResearch.WordTrace]
  refine ⟨112741824993461863956013639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150322433324615818608018185 112741824993461863956013639)
  ·
    refine ⟨169112737490192795934020459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112741824993461863956013639 169112737490192795934020459)
    ·
      refine ⟨253669106235289193901030689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169112737490192795934020459 253669106235289193901030689)
      ·
        refine ⟨190251829676466895425773017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253669106235289193901030689 190251829676466895425773017)
        ·
          refine ⟨142688872257350171569329763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190251829676466895425773017 142688872257350171569329763)
          ·
            refine ⟨214033308386025257353994645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142688872257350171569329763 214033308386025257353994645)
            ·
              refine ⟨10032811330594933938468499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214033308386025257353994645 10032811330594933938468499)
              ·
                refine ⟨15049216995892400907702749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10032811330594933938468499 15049216995892400907702749)
                ·
                  refine ⟨5643456373459650340388531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15049216995892400907702749 5643456373459650340388531)
                  ·
                    refine ⟨8465184560189475510582797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643456373459650340388531 8465184560189475510582797)
                    ·
                      refine ⟨3174444210071053316468549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465184560189475510582797 3174444210071053316468549)
                      ·
                        rfl

theorem cell23_6182208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_6182208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182208 prefixEnd_6182208 := by exact prefixLift 6182208
  have htrace : WordTrace (prefixWord ++ tailWord_6182208) baseStart_6182208 baseEnd_6182208 := by
    simpa [prefixWord, tailWord_6182208, baseEnd_6182208] using wordTrace_append hprefix tailTrace_6182208
  have hstable : (prefixWord ++ tailWord_6182208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182208).length < 2 ^ (prefixWord ++ tailWord_6182208).sum := by decide
  have hdescent : baseEnd_6182208 < baseStart_6182208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182228 : List Nat := [2, 4, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_6182228 : Nat := 118140960795 + 6182228 * 2 ^ 59
def prefixEnd_6182228 : Nat := 4983230072969 + 3 ^ 40 * 6182228 * 2
def baseEnd_6182228 : Nat := 1058151493228047746072819

theorem tailTrace_6182228 : CollatzResearch.WordTrace tailWord_6182228 prefixEnd_6182228 1058151493228047746072819 := by
  unfold tailWord_6182228
  simp only [CollatzResearch.WordTrace]
  refine ⟨112742189723425635663877669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150322919631234180885170225 112742189723425635663877669)
  ·
    refine ⟨21139160573142306686977063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112742189723425635663877669 21139160573142306686977063)
    ·
      refine ⟨31708740859713460030465595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21139160573142306686977063 31708740859713460030465595)
      ·
        refine ⟨47563111289570190045698393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31708740859713460030465595 47563111289570190045698393)
        ·
          refine ⟨35672333467177642534273795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47563111289570190045698393 35672333467177642534273795)
          ·
            refine ⟨53508500200766463801410693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35672333467177642534273795 53508500200766463801410693)
            ·
              refine ⟨10032843787643711962764505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53508500200766463801410693 10032843787643711962764505)
              ·
                refine ⟨7524632840732783972073379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10032843787643711962764505 7524632840732783972073379)
                ·
                  refine ⟨11286949261099175958110069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7524632840732783972073379 11286949261099175958110069)
                  ·
                    refine ⟨1058151493228047746072819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11286949261099175958110069 1058151493228047746072819)
                    ·
                      rfl

theorem cell23_6182228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_6182228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182228 prefixEnd_6182228 := by exact prefixLift 6182228
  have htrace : WordTrace (prefixWord ++ tailWord_6182228) baseStart_6182228 baseEnd_6182228 := by
    simpa [prefixWord, tailWord_6182228, baseEnd_6182228] using wordTrace_append hprefix tailTrace_6182228
  have hstable : (prefixWord ++ tailWord_6182228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182228).length < 2 ^ (prefixWord ++ tailWord_6182228).sum := by decide
  have hdescent : baseEnd_6182228 < baseStart_6182228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182258 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_6182258 : Nat := 118140960795 + 6182258 * 2 ^ 59
def prefixEnd_6182258 : Nat := 4983230072969 + 3 ^ 40 * 6182258 * 2
def baseEnd_6182258 : Nat := 1058156628034592706947773

theorem tailTrace_6182258 : CollatzResearch.WordTrace tailWord_6182258 prefixEnd_6182258 1058156628034592706947773 := by
  unfold tailWord_6182258
  simp only [CollatzResearch.WordTrace]
  refine ⟨56371368409185646612836857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150323649091161724300898285 56371368409185646612836857)
  ·
    refine ⟨42278526306889234959627643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56371368409185646612836857 42278526306889234959627643)
    ·
      refine ⟨63417789460333852439441465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42278526306889234959627643 63417789460333852439441465)
      ·
        refine ⟨47563342095250389329581099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63417789460333852439441465 47563342095250389329581099)
        ·
          refine ⟨71345013142875583994371649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47563342095250389329581099 71345013142875583994371649)
          ·
            refine ⟨53508759857156687995778737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71345013142875583994371649 53508759857156687995778737)
            ·
              refine ⟨40131569892867515996834053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53508759857156687995778737 40131569892867515996834053)
              ·
                refine ⟨7524669354912659249406385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40131569892867515996834053 7524669354912659249406385)
                ·
                  refine ⟨5643502016184494437054789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7524669354912659249406385 5643502016184494437054789)
                  ·
                    refine ⟨1058156628034592706947773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5643502016184494437054789 1058156628034592706947773)
                    ·
                      rfl

theorem cell23_6182258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_6182258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182258 prefixEnd_6182258 := by exact prefixLift 6182258
  have htrace : WordTrace (prefixWord ++ tailWord_6182258) baseStart_6182258 baseEnd_6182258 := by
    simpa [prefixWord, tailWord_6182258, baseEnd_6182258] using wordTrace_append hprefix tailTrace_6182258
  have hstable : (prefixWord ++ tailWord_6182258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182258).length < 2 ^ (prefixWord ++ tailWord_6182258).sum := by decide
  have hdescent : baseEnd_6182258 < baseStart_6182258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182265 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 3, 2, 2]
def baseStart_6182265 : Nat := 118140960795 + 6182265 * 2 ^ 59
def prefixEnd_6182265 : Nat := 4983230072969 + 3 ^ 40 * 6182265 * 2
def baseEnd_6182265 : Nat := 3174473478468359593455787

theorem tailTrace_6182265 : CollatzResearch.WordTrace tailWord_6182265 prefixEnd_6182265 3174473478468359593455787 := by
  unfold tailWord_6182265
  simp only [CollatzResearch.WordTrace]
  refine ⟨225485728947717226646852249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150323819298478151097901499 225485728947717226646852249)
  ·
    refine ⟨169114296710787919985139187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225485728947717226646852249 169114296710787919985139187)
    ·
      refine ⟨253671445066181879977708781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169114296710787919985139187 253671445066181879977708781)
      ·
        refine ⟨95126791899818204991640793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253671445066181879977708781 95126791899818204991640793)
        ·
          refine ⟨71345093924863653743730595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95126791899818204991640793 71345093924863653743730595)
          ·
            refine ⟨107017640887295480615595893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71345093924863653743730595 107017640887295480615595893)
            ·
              refine ⟨10032903833183951307712115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107017640887295480615595893 10032903833183951307712115)
              ·
                refine ⟨15049355749775926961568173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10032903833183951307712115 15049355749775926961568173)
                ·
                  refine ⟨5643508406165972610588065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15049355749775926961568173 5643508406165972610588065)
                  ·
                    refine ⟨4232631304624479457941049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5643508406165972610588065 4232631304624479457941049)
                    ·
                      refine ⟨3174473478468359593455787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232631304624479457941049 3174473478468359593455787)
                      ·
                        rfl

theorem cell23_6182265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_6182265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182265 prefixEnd_6182265 := by exact prefixLift 6182265
  have htrace : WordTrace (prefixWord ++ tailWord_6182265) baseStart_6182265 baseEnd_6182265 := by
    simpa [prefixWord, tailWord_6182265, baseEnd_6182265] using wordTrace_append hprefix tailTrace_6182265
  have hstable : (prefixWord ++ tailWord_6182265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182265).length < 2 ^ (prefixWord ++ tailWord_6182265).sum := by decide
  have hdescent : baseEnd_6182265 < baseStart_6182265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182275 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 2, 4]
def baseStart_6182275 : Nat := 118140960795 + 6182275 * 2 ^ 59
def prefixEnd_6182275 : Nat := 4983230072969 + 3 ^ 40 * 6182275 * 2
def baseEnd_6182275 : Nat := 1058159537758301518110247

theorem tailTrace_6182275 : CollatzResearch.WordTrace tailWord_6182275 prefixEnd_6182275 1058159537758301518110247 := by
  unfold tailWord_6182275
  simp only [CollatzResearch.WordTrace]
  refine ⟨225486093677680998354716279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150324062451787332236477519 225486093677680998354716279)
  ·
    refine ⟨338229140516521497532074419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225486093677680998354716279 338229140516521497532074419)
    ·
      refine ⟨507343710774782246298111629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338229140516521497532074419 507343710774782246298111629)
      ·
        refine ⟨190253891540543342361791861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507343710774782246298111629 190253891540543342361791861)
        ·
          refine ⟨17836302331925938346417987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190253891540543342361791861 17836302331925938346417987)
          ·
            refine ⟨26754453497888907519626981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17836302331925938346417987 26754453497888907519626981)
            ·
              refine ⟨5016460030854170159930059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26754453497888907519626981 5016460030854170159930059)
              ·
                refine ⟨7524690046281255239895089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5016460030854170159930059 7524690046281255239895089)
                ·
                  refine ⟨5643517534710941429921317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7524690046281255239895089 5643517534710941429921317)
                  ·
                    refine ⟨1058159537758301518110247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5643517534710941429921317 1058159537758301518110247)
                    ·
                      rfl

theorem cell23_6182275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 2, 4].length) (baseStart_6182275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182275 prefixEnd_6182275 := by exact prefixLift 6182275
  have htrace : WordTrace (prefixWord ++ tailWord_6182275) baseStart_6182275 baseEnd_6182275 := by
    simpa [prefixWord, tailWord_6182275, baseEnd_6182275] using wordTrace_append hprefix tailTrace_6182275
  have hstable : (prefixWord ++ tailWord_6182275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182275).length < 2 ^ (prefixWord ++ tailWord_6182275).sum := by decide
  have hdescent : baseEnd_6182275 < baseStart_6182275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182298 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3]
def baseStart_6182298 : Nat := 118140960795 + 6182298 * 2 ^ 59
def prefixEnd_6182298 : Nat := 4983230072969 + 3 ^ 40 * 6182298 * 2
def baseEnd_6182298 : Nat := 3174490423329957964343135

theorem tailTrace_6182298 : CollatzResearch.WordTrace tailWord_6182298 prefixEnd_6182298 3174490423329957964343135 := by
  unfold tailWord_6182298
  simp only [CollatzResearch.WordTrace]
  refine ⟨56371733139149418320700887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150324621704398448855202365 56371733139149418320700887)
  ·
    refine ⟨84557599708724127481051331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56371733139149418320700887 84557599708724127481051331)
    ·
      refine ⟨126836399563086191221576997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84557599708724127481051331 126836399563086191221576997)
      ·
        refine ⟨23781824918078660854045687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126836399563086191221576997 23781824918078660854045687)
        ·
          refine ⟨35672737377117991281068531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23781824918078660854045687 35672737377117991281068531)
          ·
            refine ⟨53509106065676986921602797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35672737377117991281068531 53509106065676986921602797)
            ·
              refine ⟨20065914774628870095601049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53509106065676986921602797 20065914774628870095601049)
              ·
                refine ⟨15049436080971652571700787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20065914774628870095601049 15049436080971652571700787)
                ·
                  refine ⟨22574154121457478857551181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15049436080971652571700787 22574154121457478857551181)
                  ·
                    refine ⟨8465307795546554571581693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22574154121457478857551181 8465307795546554571581693)
                    ·
                      refine ⟨3174490423329957964343135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465307795546554571581693 3174490423329957964343135)
                      ·
                        rfl

theorem cell23_6182298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_6182298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182298 prefixEnd_6182298 := by exact prefixLift 6182298
  have htrace : WordTrace (prefixWord ++ tailWord_6182298) baseStart_6182298 baseEnd_6182298 := by
    simpa [prefixWord, tailWord_6182298, baseEnd_6182298] using wordTrace_append hprefix tailTrace_6182298
  have hstable : (prefixWord ++ tailWord_6182298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182298).length < 2 ^ (prefixWord ++ tailWord_6182298).sum := by decide
  have hdescent : baseEnd_6182298 < baseStart_6182298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182302 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6182302 : Nat := 118140960795 + 6182302 * 2 ^ 59
def prefixEnd_6182302 : Nat := 4983230072969 + 3 ^ 40 * 6182302 * 2
def baseEnd_6182302 : Nat := 3174492477252575948693117

theorem tailTrace_6182302 : CollatzResearch.WordTrace tailWord_6182302 prefixEnd_6182302 3174492477252575948693117 := by
  unfold tailWord_6182302
  simp only [CollatzResearch.WordTrace]
  refine ⟨28185884806072897745743645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150324718965722121310632773 28185884806072897745743645)
  ·
    refine ⟨10569706802277336654653867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28185884806072897745743645 10569706802277336654653867)
    ·
      refine ⟨15854560203416004981980801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10569706802277336654653867 15854560203416004981980801)
      ·
        refine ⟨11890920152562003736485601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15854560203416004981980801 11890920152562003736485601)
        ·
          refine ⟨8918190114421502802364201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11890920152562003736485601 8918190114421502802364201)
          ·
            refine ⟨6688642585816127101773151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8918190114421502802364201 6688642585816127101773151)
            ·
              refine ⟨10032963878724190652659727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688642585816127101773151 10032963878724190652659727)
              ·
                refine ⟨15049445818086285978989591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10032963878724190652659727 15049445818086285978989591)
                ·
                  refine ⟨22574168727129428968484387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15049445818086285978989591 22574168727129428968484387)
                  ·
                    refine ⟨33861253090694143452726581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22574168727129428968484387 33861253090694143452726581)
                    ·
                      refine ⟨3174492477252575948693117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33861253090694143452726581 3174492477252575948693117)
                      ·
                        rfl

theorem cell23_6182302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6182302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182302 prefixEnd_6182302 := by exact prefixLift 6182302
  have htrace : WordTrace (prefixWord ++ tailWord_6182302) baseStart_6182302 baseEnd_6182302 := by
    simpa [prefixWord, tailWord_6182302, baseEnd_6182302] using wordTrace_append hprefix tailTrace_6182302
  have hstable : (prefixWord ++ tailWord_6182302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182302).length < 2 ^ (prefixWord ++ tailWord_6182302).sum := by decide
  have hdescent : baseEnd_6182302 < baseStart_6182302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182321 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6182321 : Nat := 118140960795 + 6182321 * 2 ^ 59
def prefixEnd_6182321 : Nat := 4983230072969 + 3 ^ 40 * 6182321 * 2
def baseEnd_6182321 : Nat := 3174502233385011374355529

theorem tailTrace_6182321 : CollatzResearch.WordTrace tailWord_6182321 prefixEnd_6182321 3174502233385011374355529 := by
  unfold tailWord_6182321
  simp only [CollatzResearch.WordTrace]
  refine ⟨225487771435514348210890817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150325180957009565473927211 225487771435514348210890817)
  ·
    refine ⟨169115828576635761158168113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225487771435514348210890817 169115828576635761158168113)
    ·
      refine ⟨126836871432476820868626085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169115828576635761158168113 126836871432476820868626085)
      ·
        refine ⟨23781913393589403912867391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126836871432476820868626085 23781913393589403912867391)
        ·
          refine ⟨35672870090384105869301087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23781913393589403912867391 35672870090384105869301087)
          ·
            refine ⟨53509305135576158803951631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35672870090384105869301087 53509305135576158803951631)
            ·
              refine ⟨80263957703364238205927447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53509305135576158803951631 80263957703364238205927447)
              ·
                refine ⟨120395936555046357308891171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80263957703364238205927447 120395936555046357308891171)
                ·
                  refine ⟨180593904832569535963336757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120395936555046357308891171 180593904832569535963336757)
                  ·
                    refine ⟨16930678578053393996562821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 180593904832569535963336757 16930678578053393996562821)
                    ·
                      refine ⟨3174502233385011374355529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16930678578053393996562821 3174502233385011374355529)
                      ·
                        rfl

theorem cell23_6182321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6182321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182321 prefixEnd_6182321 := by exact prefixLift 6182321
  have htrace : WordTrace (prefixWord ++ tailWord_6182321) baseStart_6182321 baseEnd_6182321 := by
    simpa [prefixWord, tailWord_6182321, baseEnd_6182321] using wordTrace_append hprefix tailTrace_6182321
  have hstable : (prefixWord ++ tailWord_6182321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182321).length < 2 ^ (prefixWord ++ tailWord_6182321).sum := by decide
  have hdescent : baseEnd_6182321 < baseStart_6182321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182325 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 3, 3, 2]
def baseStart_6182325 : Nat := 118140960795 + 6182325 * 2 ^ 59
def prefixEnd_6182325 : Nat := 4983230072969 + 3 ^ 40 * 6182325 * 2
def baseEnd_6182325 : Nat := 3174504287307629358705511

theorem tailTrace_6182325 : CollatzResearch.WordTrace tailWord_6182325 prefixEnd_6182325 3174504287307629358705511 := by
  unfold tailWord_6182325
  simp only [CollatzResearch.WordTrace]
  refine ⟨225487917327499856894036429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150325278218333237929357619 225487917327499856894036429)
  ·
    refine ⟨84557968997812446335263661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225487917327499856894036429 84557968997812446335263661)
    ·
      refine ⟨31709238374179667375723873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84557968997812446335263661 31709238374179667375723873)
      ·
        refine ⟨23781928780634750531792905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31709238374179667375723873 23781928780634750531792905)
        ·
          refine ⟨17836446585476062898844679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23781928780634750531792905 17836446585476062898844679)
          ·
            refine ⟨26754669878214094348267019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17836446585476062898844679 26754669878214094348267019)
            ·
              refine ⟨40132004817321141522400529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26754669878214094348267019 40132004817321141522400529)
              ·
                refine ⟨30099003612990856141800397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40132004817321141522400529 30099003612990856141800397)
                ·
                  refine ⟨11287126354871571053175149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30099003612990856141800397 11287126354871571053175149)
                  ·
                    refine ⟨4232672383076839144940681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11287126354871571053175149 4232672383076839144940681)
                    ·
                      refine ⟨3174504287307629358705511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232672383076839144940681 3174504287307629358705511)
                      ·
                        rfl

theorem cell23_6182325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_6182325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182325 prefixEnd_6182325 := by exact prefixLift 6182325
  have htrace : WordTrace (prefixWord ++ tailWord_6182325) baseStart_6182325 baseEnd_6182325 := by
    simpa [prefixWord, tailWord_6182325, baseEnd_6182325] using wordTrace_append hprefix tailTrace_6182325
  have hstable : (prefixWord ++ tailWord_6182325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182325).length < 2 ^ (prefixWord ++ tailWord_6182325).sum := by decide
  have hdescent : baseEnd_6182325 < baseStart_6182325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182389 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6182389 : Nat := 118140960795 + 6182389 * 2 ^ 59
def prefixEnd_6182389 : Nat := 4983230072969 + 3 ^ 40 * 6182389 * 2
def baseEnd_6182389 : Nat := 3174537150069517108305217

theorem tailTrace_6182389 : CollatzResearch.WordTrace tailWord_6182389 prefixEnd_6182389 3174537150069517108305217 := by
  unfold tailWord_6182389
  simp only [CollatzResearch.WordTrace]
  refine ⟨225490251599267995824366221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150326834399511997216244147 225490251599267995824366221)
  ·
    refine ⟨84558844349725498434137333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225490251599267995824366221 84558844349725498434137333)
    ·
      refine ⟨7927391657786765478200375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84558844349725498434137333 7927391657786765478200375)
      ·
        refine ⟨11891087486680148217300563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7927391657786765478200375 11891087486680148217300563)
        ·
          refine ⟨17836631230020222325950845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11891087486680148217300563 17836631230020222325950845)
          ·
            refine ⟨6688736711257583372231567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17836631230020222325950845 6688736711257583372231567)
            ·
              refine ⟨10033105066886375058347351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688736711257583372231567 10033105066886375058347351)
              ·
                refine ⟨15049657600329562587521027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10033105066886375058347351 15049657600329562587521027)
                ·
                  refine ⟨22574486400494343881281541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15049657600329562587521027 22574486400494343881281541)
                  ·
                    refine ⟨4232716200092689477740289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22574486400494343881281541 4232716200092689477740289)
                    ·
                      refine ⟨3174537150069517108305217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232716200092689477740289 3174537150069517108305217)
                      ·
                        rfl

theorem cell23_6182389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6182389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182389 prefixEnd_6182389 := by exact prefixLift 6182389
  have htrace : WordTrace (prefixWord ++ tailWord_6182389) baseStart_6182389 baseEnd_6182389 := by
    simpa [prefixWord, tailWord_6182389, baseEnd_6182389] using wordTrace_append hprefix tailTrace_6182389
  have hstable : (prefixWord ++ tailWord_6182389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182389).length < 2 ^ (prefixWord ++ tailWord_6182389).sum := by decide
  have hdescent : baseEnd_6182389 < baseStart_6182389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182391 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 6, 5]
def baseStart_6182391 : Nat := 118140960795 + 6182391 * 2 ^ 59
def prefixEnd_6182391 : Nat := 4983230072969 + 3 ^ 40 * 6182391 * 2
def baseEnd_6182391 : Nat := 1058179392343608700160069

theorem tailTrace_6182391 : CollatzResearch.WordTrace tailWord_6182391 prefixEnd_6182391 1058179392343608700160069 := by
  unfold tailWord_6182391
  simp only [CollatzResearch.WordTrace]
  refine ⟨225490324545260750165939027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150326883030173833443959351 225490324545260750165939027)
  ·
    refine ⟨338235486817891125248908541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225490324545260750165939027 338235486817891125248908541)
    ·
      refine ⟨126838307556709171968340703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338235486817891125248908541 126838307556709171968340703)
      ·
        refine ⟨190257461335063757952511055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126838307556709171968340703 190257461335063757952511055)
        ·
          refine ⟨285386192002595636928766583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190257461335063757952511055 285386192002595636928766583)
          ·
            refine ⟨428079288003893455393149875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285386192002595636928766583 428079288003893455393149875)
            ·
              refine ⟨642118932005840183089724813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428079288003893455393149875 642118932005840183089724813)
              ·
                refine ⟨240794599502190068658646805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642118932005840183089724813 240794599502190068658646805)
                ·
                  refine ⟨11287246851665159468374069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240794599502190068658646805 11287246851665159468374069)
                  ·
                    refine ⟨1058179392343608700160069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11287246851665159468374069 1058179392343608700160069)
                    ·
                      rfl

theorem cell23_6182391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_6182391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182391 prefixEnd_6182391 := by exact prefixLift 6182391
  have htrace : WordTrace (prefixWord ++ tailWord_6182391) baseStart_6182391 baseEnd_6182391 := by
    simpa [prefixWord, tailWord_6182391, baseEnd_6182391] using wordTrace_append hprefix tailTrace_6182391
  have hstable : (prefixWord ++ tailWord_6182391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182391).length < 2 ^ (prefixWord ++ tailWord_6182391).sum := by decide
  have hdescent : baseEnd_6182391 < baseStart_6182391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182412 : List Nat := [2, 2, 1, 2, 5, 2, 1, 3, 5]
def baseStart_6182412 : Nat := 118140960795 + 6182412 * 2 ^ 59
def prefixEnd_6182412 : Nat := 4983230072969 + 3 ^ 40 * 6182412 * 2
def baseEnd_6182412 : Nat := 352727662236063390924179

theorem tailTrace_6182412 : CollatzResearch.WordTrace tailWord_6182412 prefixEnd_6182412 352727662236063390924179 := by
  unfold tailWord_6182412
  simp only [CollatzResearch.WordTrace]
  refine ⟨112745545239092335376226745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150327393652123113834968993 112745545239092335376226745)
  ·
    refine ⟨84559158929319251532170059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112745545239092335376226745 84559158929319251532170059)
    ·
      refine ⟨126838738393978877298255089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84559158929319251532170059 126838738393978877298255089)
      ·
        refine ⟨95129053795484157973691317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126838738393978877298255089 95129053795484157973691317)
        ·
          refine ⟨8918348793326639810033561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95129053795484157973691317 8918348793326639810033561)
          ·
            refine ⟨6688761594994979857525171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8918348793326639810033561 6688761594994979857525171)
            ·
              refine ⟨10033142392492469786287757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688761594994979857525171 10033142392492469786287757)
              ·
                refine ⟨3762428397184676169857909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10033142392492469786287757 3762428397184676169857909)
                ·
                  refine ⟨352727662236063390924179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3762428397184676169857909 352727662236063390924179)
                  ·
                    rfl

theorem cell23_6182412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_6182412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182412 prefixEnd_6182412 := by exact prefixLift 6182412
  have htrace : WordTrace (prefixWord ++ tailWord_6182412) baseStart_6182412 baseEnd_6182412 := by
    simpa [prefixWord, tailWord_6182412, baseEnd_6182412] using wordTrace_append hprefix tailTrace_6182412
  have hstable : (prefixWord ++ tailWord_6182412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182412).length < 2 ^ (prefixWord ++ tailWord_6182412).sum := by decide
  have hdescent : baseEnd_6182412 < baseStart_6182412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182448 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3]
def baseStart_6182448 : Nat := 118140960795 + 6182448 * 2 ^ 59
def prefixEnd_6182448 : Nat := 4983230072969 + 3 ^ 40 * 6182448 * 2
def baseEnd_6182448 : Nat := 3174567445428132377467445

theorem tailTrace_6182448 : CollatzResearch.WordTrace tailWord_6182448 prefixEnd_6182448 3174567445428132377467445 := by
  unfold tailWord_6182448
  simp only [CollatzResearch.WordTrace]
  refine ⟨112746201753027124450381999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150328269004036165933842665 112746201753027124450381999)
  ·
    refine ⟨169119302629540686675572999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112746201753027124450381999 169119302629540686675572999)
    ·
      refine ⟨253678953944311030013359499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169119302629540686675572999 253678953944311030013359499)
      ·
        refine ⟨380518430916466545020039249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253678953944311030013359499 380518430916466545020039249)
        ·
          refine ⟨285388823187349908765029437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380518430916466545020039249 285388823187349908765029437)
          ·
            refine ⟨107020808695256215786886039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285388823187349908765029437 107020808695256215786886039)
            ·
              refine ⟨160531213042884323680329059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107020808695256215786886039 160531213042884323680329059)
              ·
                refine ⟨240796819564326485520493589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160531213042884323680329059 240796819564326485520493589)
                ·
                  refine ⟨11287350917077804008773137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240796819564326485520493589 11287350917077804008773137)
                  ·
                    refine ⟨8465513187808353006579853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11287350917077804008773137 8465513187808353006579853)
                    ·
                      refine ⟨3174567445428132377467445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465513187808353006579853 3174567445428132377467445)
                      ·
                        rfl

theorem cell23_6182448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_6182448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182448 prefixEnd_6182448 := by exact prefixLift 6182448
  have htrace : WordTrace (prefixWord ++ tailWord_6182448) baseStart_6182448 baseEnd_6182448 := by
    simpa [prefixWord, tailWord_6182448, baseEnd_6182448] using wordTrace_append hprefix tailTrace_6182448
  have hstable : (prefixWord ++ tailWord_6182448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182448).length < 2 ^ (prefixWord ++ tailWord_6182448).sum := by decide
  have hdescent : baseEnd_6182448 < baseStart_6182448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182505 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 4, 3, 2]
def baseStart_6182505 : Nat := 118140960795 + 6182505 * 2 ^ 59
def prefixEnd_6182505 : Nat := 4983230072969 + 3 ^ 40 * 6182505 * 2
def baseEnd_6182505 : Nat := 3174596713825438654454683

theorem tailTrace_6182505 : CollatzResearch.WordTrace tailWord_6182505 prefixEnd_6182505 3174596713825438654454683 := by
  unfold tailWord_6182505
  simp only [CollatzResearch.WordTrace]
  refine ⟨225494482466847747635588969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150329654977898498423725979 225494482466847747635588969)
  ·
    refine ⟨169120861850135810726691727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225494482466847747635588969 169120861850135810726691727)
    ·
      refine ⟨253681292775203716090037591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169120861850135810726691727 253681292775203716090037591)
      ·
        refine ⟨380521939162805574135056387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253681292775203716090037591 380521939162805574135056387)
        ·
          refine ⟨570782908744208361202584581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380521939162805574135056387 570782908744208361202584581)
          ·
            refine ⟨107021795389539067725484609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 570782908744208361202584581 107021795389539067725484609)
            ·
              refine ⟨80266346542154300794113457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107021795389539067725484609 80266346542154300794113457)
              ·
                refine ⟨60199759906615725595585093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80266346542154300794113457 60199759906615725595585093)
                ·
                  refine ⟨11287454982490448549172205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60199759906615725595585093 11287454982490448549172205)
                  ·
                    refine ⟨4232795618433918205939577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11287454982490448549172205 4232795618433918205939577)
                    ·
                      refine ⟨3174596713825438654454683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232795618433918205939577 3174596713825438654454683)
                      ·
                        rfl

theorem cell23_6182505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 3, 2].length) (baseStart_6182505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182505 prefixEnd_6182505 := by exact prefixLift 6182505
  have htrace : WordTrace (prefixWord ++ tailWord_6182505) baseStart_6182505 baseEnd_6182505 := by
    simpa [prefixWord, tailWord_6182505, baseEnd_6182505] using wordTrace_append hprefix tailTrace_6182505
  have hstable : (prefixWord ++ tailWord_6182505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182505).length < 2 ^ (prefixWord ++ tailWord_6182505).sum := by decide
  have hdescent : baseEnd_6182505 < baseStart_6182505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182512 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 3, 1, 3]
def baseStart_6182512 : Nat := 118140960795 + 6182512 * 2 ^ 59
def prefixEnd_6182512 : Nat := 4983230072969 + 3 ^ 40 * 6182512 * 2
def baseEnd_6182512 : Nat := 3174600308190020127067151

theorem tailTrace_6182512 : CollatzResearch.WordTrace tailWord_6182512 prefixEnd_6182512 3174600308190020127067151 := by
  unfold tailWord_6182512
  simp only [CollatzResearch.WordTrace]
  refine ⟨112747368888911193915546895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150329825185214925220729193 112747368888911193915546895)
  ·
    refine ⟨169121053333366790873320343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112747368888911193915546895 169121053333366790873320343)
    ·
      refine ⟨253681580000050186309980515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169121053333366790873320343 253681580000050186309980515)
      ·
        refine ⟨380522370000075279464970773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253681580000050186309980515 380522370000075279464970773)
        ·
          refine ⟨17836986093753528724920505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 380522370000075279464970773 17836986093753528724920505)
          ·
            refine ⟨13377739570315146543690379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17836986093753528724920505 13377739570315146543690379)
            ·
              refine ⟨20066609355472719815535569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13377739570315146543690379 20066609355472719815535569)
              ·
                refine ⟨15049957016604539861651677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20066609355472719815535569 15049957016604539861651677)
                ·
                  refine ⟨5643733881226702448119379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15049957016604539861651677 5643733881226702448119379)
                  ·
                    refine ⟨8465600821840053672179069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643733881226702448119379 8465600821840053672179069)
                    ·
                      refine ⟨3174600308190020127067151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465600821840053672179069 3174600308190020127067151)
                      ·
                        rfl

theorem cell23_6182512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 1, 3].length) (baseStart_6182512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182512 prefixEnd_6182512 := by exact prefixLift 6182512
  have htrace : WordTrace (prefixWord ++ tailWord_6182512) baseStart_6182512 baseEnd_6182512 := by
    simpa [prefixWord, tailWord_6182512, baseEnd_6182512] using wordTrace_append hprefix tailTrace_6182512
  have hstable : (prefixWord ++ tailWord_6182512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182512).length < 2 ^ (prefixWord ++ tailWord_6182512).sum := by decide
  have hdescent : baseEnd_6182512 < baseStart_6182512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182528 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 1, 6]
def baseStart_6182528 : Nat := 118140960795 + 6182528 * 2 ^ 59
def prefixEnd_6182528 : Nat := 4983230072969 + 3 ^ 40 * 6182528 * 2
def baseEnd_6182528 : Nat := 1058202841293497354822359

theorem tailTrace_6182528 : CollatzResearch.WordTrace tailWord_6182528 prefixEnd_6182528 1058202841293497354822359 := by
  unfold tailWord_6182528
  simp only [CollatzResearch.WordTrace]
  refine ⟨112747660672882211281838119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150330214230509615042450825 112747660672882211281838119)
  ·
    refine ⟨169121491009323316922757179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112747660672882211281838119 169121491009323316922757179)
    ·
      refine ⟨253682236513984975384135769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169121491009323316922757179 253682236513984975384135769)
      ·
        refine ⟨190261677385488731538101827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253682236513984975384135769 190261677385488731538101827)
        ·
          refine ⟨285392516078233097307152741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190261677385488731538101827 285392516078233097307152741)
          ·
            refine ⟨53511096764668705745091139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285392516078233097307152741 53511096764668705745091139)
            ·
              refine ⟨80266645147003058617636709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53511096764668705745091139 80266645147003058617636709)
              ·
                refine ⟨15049995965063073490806883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80266645147003058617636709 15049995965063073490806883)
                ·
                  refine ⟨22574993947594610236210325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15049995965063073490806883 22574993947594610236210325)
                  ·
                    refine ⟨1058202841293497354822359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22574993947594610236210325 1058202841293497354822359)
                    ·
                      rfl

theorem cell23_6182528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 1, 6].length) (baseStart_6182528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182528 prefixEnd_6182528 := by exact prefixLift 6182528
  have htrace : WordTrace (prefixWord ++ tailWord_6182528) baseStart_6182528 baseEnd_6182528 := by
    simpa [prefixWord, tailWord_6182528, baseEnd_6182528] using wordTrace_append hprefix tailTrace_6182528
  have hstable : (prefixWord ++ tailWord_6182528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182528).length < 2 ^ (prefixWord ++ tailWord_6182528).sum := by decide
  have hdescent : baseEnd_6182528 < baseStart_6182528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182529 : List Nat := [1, 2, 4, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_6182529 : Nat := 118140960795 + 6182529 * 2 ^ 59
def prefixEnd_6182529 : Nat := 4983230072969 + 3 ^ 40 * 6182529 * 2
def baseEnd_6182529 : Nat := 3174609037361146560554573

theorem tailTrace_6182529 : CollatzResearch.WordTrace tailWord_6182529 prefixEnd_6182529 3174609037361146560554573 := by
  unfold tailWord_6182529
  simp only [CollatzResearch.WordTrace]
  refine ⟨225495357818760799734462641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150330238545840533156308427 225495357818760799734462641)
  ·
    refine ⟨169121518364070599800846981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225495357818760799734462641 169121518364070599800846981)
    ·
      refine ⟨31710284693263237462658809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169121518364070599800846981 31710284693263237462658809)
      ·
        refine ⟨23782713519947428096994107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31710284693263237462658809 23782713519947428096994107)
        ·
          refine ⟨35674070279921142145491161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23782713519947428096994107 35674070279921142145491161)
          ·
            refine ⟨26755552709940856609118371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35674070279921142145491161 26755552709940856609118371)
            ·
              refine ⟨40133329064911284913677557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26755552709940856609118371 40133329064911284913677557)
              ·
                refine ⟨3762499599835432960657271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40133329064911284913677557 3762499599835432960657271)
                ·
                  refine ⟨5643749399753149440985907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762499599835432960657271 5643749399753149440985907)
                  ·
                    refine ⟨8465624099629724161478861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5643749399753149440985907 8465624099629724161478861)
                    ·
                      refine ⟨3174609037361146560554573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465624099629724161478861 3174609037361146560554573)
                      ·
                        rfl

theorem cell23_6182529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_6182529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182529 prefixEnd_6182529 := by exact prefixLift 6182529
  have htrace : WordTrace (prefixWord ++ tailWord_6182529) baseStart_6182529 baseEnd_6182529 := by
    simpa [prefixWord, tailWord_6182529, baseEnd_6182529] using wordTrace_append hprefix tailTrace_6182529
  have hstable : (prefixWord ++ tailWord_6182529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182529).length < 2 ^ (prefixWord ++ tailWord_6182529).sum := by decide
  have hdescent : baseEnd_6182529 < baseStart_6182529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182532 : List Nat := [2, 3, 2, 1, 4, 1, 1, 3, 1, 5]
def baseStart_6182532 : Nat := 118140960795 + 6182532 * 2 ^ 59
def prefixEnd_6182532 : Nat := 4983230072969 + 3 ^ 40 * 6182532 * 2
def baseEnd_6182532 : Nat := 1058203525934370016272353

theorem tailTrace_6182532 : CollatzResearch.WordTrace tailWord_6182532 prefixEnd_6182532 1058203525934370016272353 := by
  unfold tailWord_6182532
  simp only [CollatzResearch.WordTrace]
  refine ⟨112747733618874965623410925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150330311491833287497881233 112747733618874965623410925)
  ·
    refine ⟨42280400107078112108779097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112747733618874965623410925 42280400107078112108779097)
    ·
      refine ⟨31710300080308584081584323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42280400107078112108779097 31710300080308584081584323)
      ·
        refine ⟨47565450120462876122376485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31710300080308584081584323 47565450120462876122376485)
        ·
          refine ⟨8918521897586789272945591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47565450120462876122376485 8918521897586789272945591)
          ·
            refine ⟨13377782846380183909418387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8918521897586789272945591 13377782846380183909418387)
            ·
              refine ⟨20066674269570275864127581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13377782846380183909418387 20066674269570275864127581)
              ·
                refine ⟨7525002851088853449047843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20066674269570275864127581 7525002851088853449047843)
                ·
                  refine ⟨11287504276633280173571765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7525002851088853449047843 11287504276633280173571765)
                  ·
                    refine ⟨1058203525934370016272353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11287504276633280173571765 1058203525934370016272353)
                    ·
                      rfl

theorem cell23_6182532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_6182532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182532 prefixEnd_6182532 := by exact prefixLift 6182532
  have htrace : WordTrace (prefixWord ++ tailWord_6182532) baseStart_6182532 baseEnd_6182532 := by
    simpa [prefixWord, tailWord_6182532, baseEnd_6182532] using wordTrace_append hprefix tailTrace_6182532
  have hstable : (prefixWord ++ tailWord_6182532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182532).length < 2 ^ (prefixWord ++ tailWord_6182532).sum := by decide
  have hdescent : baseEnd_6182532 < baseStart_6182532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182545 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 2, 4]
def baseStart_6182545 : Nat := 118140960795 + 6182545 * 2 ^ 59
def prefixEnd_6182545 : Nat := 4983230072969 + 3 ^ 40 * 6182545 * 2
def baseEnd_6182545 : Nat := 1058205751017206165984833

theorem tailTrace_6182545 : CollatzResearch.WordTrace tailWord_6182545 prefixEnd_6182545 1058205751017206165984833 := by
  unfold tailWord_6182545
  simp only [CollatzResearch.WordTrace]
  refine ⟨225495941386702834467045089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150330627591135222978030059 225495941386702834467045089)
  ·
    refine ⟨169121956040027125850283817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225495941386702834467045089 169121956040027125850283817)
    ·
      refine ⟨126841467030020344387712863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169121956040027125850283817 126841467030020344387712863)
      ·
        refine ⟨190262200545030516581569295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126841467030020344387712863 190262200545030516581569295)
        ·
          refine ⟨285393300817545774872353943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190262200545030516581569295 285393300817545774872353943)
          ·
            refine ⟨428089951226318662308530915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285393300817545774872353943 428089951226318662308530915)
            ·
              refine ⟨642134926839477993462796373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428089951226318662308530915 642134926839477993462796373)
              ·
                refine ⟨7525018673900132735892145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 642134926839477993462796373 7525018673900132735892145)
                ·
                  refine ⟨5643764005425099551919109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525018673900132735892145 5643764005425099551919109)
                  ·
                    refine ⟨1058205751017206165984833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5643764005425099551919109 1058205751017206165984833)
                    ·
                      rfl

theorem cell23_6182545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_6182545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182545 prefixEnd_6182545 := by exact prefixLift 6182545
  have htrace : WordTrace (prefixWord ++ tailWord_6182545) baseStart_6182545 baseEnd_6182545 := by
    simpa [prefixWord, tailWord_6182545, baseEnd_6182545] using wordTrace_append hprefix tailTrace_6182545
  have hstable : (prefixWord ++ tailWord_6182545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182545).length < 2 ^ (prefixWord ++ tailWord_6182545).sum := by decide
  have hdescent : baseEnd_6182545 < baseStart_6182545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182565 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 4]
def baseStart_6182565 : Nat := 118140960795 + 6182565 * 2 ^ 59
def prefixEnd_6182565 : Nat := 4983230072969 + 3 ^ 40 * 6182565 * 2
def baseEnd_6182565 : Nat := 3174627522664708419704407

theorem tailTrace_6182565 : CollatzResearch.WordTrace tailWord_6182565 prefixEnd_6182565 3174627522664708419704407 := by
  unfold tailWord_6182565
  simp only [CollatzResearch.WordTrace]
  refine ⟨225496670846630377882773149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150331113897753585255182099 225496670846630377882773149)
  ·
    refine ⟨84561251567486391706039931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225496670846630377882773149 84561251567486391706039931)
    ·
      refine ⟨126841877351229587559059897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84561251567486391706039931 126841877351229587559059897)
      ·
        refine ⟨95131408013422190669294923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126841877351229587559059897 95131408013422190669294923)
        ·
          refine ⟨142697112020133286003942385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95131408013422190669294923 142697112020133286003942385)
          ·
            refine ⟨107022834015099964502956789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142697112020133286003942385 107022834015099964502956789)
            ·
              refine ⟨10033390688915621672152199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107022834015099964502956789 10033390688915621672152199)
              ·
                refine ⟨15050086033373432508228299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10033390688915621672152199 15050086033373432508228299)
                ·
                  refine ⟨22575129050060148762342449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15050086033373432508228299 22575129050060148762342449)
                  ·
                    refine ⟨16931346787545111571756837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22575129050060148762342449 16931346787545111571756837)
                    ·
                      refine ⟨3174627522664708419704407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16931346787545111571756837 3174627522664708419704407)
                      ·
                        rfl

theorem cell23_6182565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_6182565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182565 prefixEnd_6182565 := by exact prefixLift 6182565
  have htrace : WordTrace (prefixWord ++ tailWord_6182565) baseStart_6182565 baseEnd_6182565 := by
    simpa [prefixWord, tailWord_6182565, baseEnd_6182565] using wordTrace_append hprefix tailTrace_6182565
  have hstable : (prefixWord ++ tailWord_6182565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182565).length < 2 ^ (prefixWord ++ tailWord_6182565).sum := by decide
  have hdescent : baseEnd_6182565 < baseStart_6182565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182585 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 3]
def baseStart_6182585 : Nat := 118140960795 + 6182585 * 2 ^ 59
def prefixEnd_6182585 : Nat := 4983230072969 + 3 ^ 40 * 6182585 * 2
def baseEnd_6182585 : Nat := 3174637792277798341454315

theorem tailTrace_6182585 : CollatzResearch.WordTrace tailWord_6182585 prefixEnd_6182585 3174637792277798341454315 := by
  unfold tailWord_6182585
  simp only [CollatzResearch.WordTrace]
  refine ⟨225497400306557921298501209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150331600204371947532334139 225497400306557921298501209)
  ·
    refine ⟨169123050229918440973875907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225497400306557921298501209 169123050229918440973875907)
    ·
      refine ⟨253684575344877661460813861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169123050229918440973875907 253684575344877661460813861)
      ·
        refine ⟨47565857877164561523902599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253684575344877661460813861 47565857877164561523902599)
        ·
          refine ⟨71348786815746842285853899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47565857877164561523902599 71348786815746842285853899)
          ·
            refine ⟨107023180223620263428780849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71348786815746842285853899 107023180223620263428780849)
            ·
              refine ⟨80267385167715197571585637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107023180223620263428780849 80267385167715197571585637)
              ·
                refine ⟨15050134718946599544672307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80267385167715197571585637 15050134718946599544672307)
                ·
                  refine ⟨22575202078419899317008461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15050134718946599544672307 22575202078419899317008461)
                  ·
                    refine ⟨8465700779407462243878173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22575202078419899317008461 8465700779407462243878173)
                    ·
                      refine ⟨3174637792277798341454315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465700779407462243878173 3174637792277798341454315)
                      ·
                        rfl

theorem cell23_6182585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_6182585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182585 prefixEnd_6182585 := by exact prefixLift 6182585
  have htrace : WordTrace (prefixWord ++ tailWord_6182585) baseStart_6182585 baseEnd_6182585 := by
    simpa [prefixWord, tailWord_6182585, baseEnd_6182585] using wordTrace_append hprefix tailTrace_6182585
  have hstable : (prefixWord ++ tailWord_6182585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182585).length < 2 ^ (prefixWord ++ tailWord_6182585).sum := by decide
  have hdescent : baseEnd_6182585 < baseStart_6182585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182586 : List Nat := [3, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2]
def baseStart_6182586 : Nat := 118140960795 + 6182586 * 2 ^ 59
def prefixEnd_6182586 : Nat := 4983230072969 + 3 ^ 40 * 6182586 * 2
def baseEnd_6182586 : Nat := 3174638305758452837541811

theorem tailTrace_6182586 : CollatzResearch.WordTrace tailWord_6182586 prefixEnd_6182586 3174638305758452837541811 := by
  unfold tailWord_6182586
  simp only [CollatzResearch.WordTrace]
  refine ⟨56374359194888574617321903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150331624519702865646191741 56374359194888574617321903)
  ·
    refine ⟨84561538792332861925982855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56374359194888574617321903 84561538792332861925982855)
    ·
      refine ⟨126842308188499292888974283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84561538792332861925982855 126842308188499292888974283)
      ·
        refine ⟨190263462282748939333461425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126842308188499292888974283 190263462282748939333461425)
        ·
          refine ⟨142697596712061704500096069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190263462282748939333461425 142697596712061704500096069)
          ·
            refine ⟨26755799383511569593768013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142697596712061704500096069 26755799383511569593768013)
            ·
              refine ⟨10033424768816838597663005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26755799383511569593768013 10033424768816838597663005)
              ·
                refine ⟨3762534288306314474123627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10033424768816838597663005 3762534288306314474123627)
                ·
                  refine ⟨5643801432459471711185441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762534288306314474123627 5643801432459471711185441)
                  ·
                    refine ⟨4232851074344603783389081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5643801432459471711185441 4232851074344603783389081)
                    ·
                      refine ⟨3174638305758452837541811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232851074344603783389081 3174638305758452837541811)
                      ·
                        rfl

theorem cell23_6182586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_6182586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182586 prefixEnd_6182586 := by exact prefixLift 6182586
  have htrace : WordTrace (prefixWord ++ tailWord_6182586) baseStart_6182586 baseEnd_6182586 := by
    simpa [prefixWord, tailWord_6182586, baseEnd_6182586] using wordTrace_append hprefix tailTrace_6182586
  have hstable : (prefixWord ++ tailWord_6182586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182586).length < 2 ^ (prefixWord ++ tailWord_6182586).sum := by decide
  have hdescent : baseEnd_6182586 < baseStart_6182586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182648 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 11]
def baseStart_6182648 : Nat := 118140960795 + 6182648 * 2 ^ 59
def prefixEnd_6182648 : Nat := 4983230072969 + 3 ^ 40 * 6182648 * 2
def baseEnd_6182648 : Nat := 352741126839892399440725

theorem tailTrace_6182648 : CollatzResearch.WordTrace tailWord_6182648 prefixEnd_6182648 352741126839892399440725 := by
  unfold tailWord_6182648
  simp only [CollatzResearch.WordTrace]
  refine ⟨112749849052664841529022299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150333132070219788705363065 112749849052664841529022299)
  ·
    refine ⟨169124773578997262293533449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112749849052664841529022299 169124773578997262293533449)
    ·
      refine ⟨126843580184247946720150087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169124773578997262293533449 126843580184247946720150087)
      ·
        refine ⟨190265370276371920080225131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126843580184247946720150087 190265370276371920080225131)
        ·
          refine ⟨285398055414557880120337697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190265370276371920080225131 285398055414557880120337697)
          ·
            refine ⟨214048541560918410090253273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285398055414557880120337697 214048541560918410090253273)
            ·
              refine ⟨160536406170688807567689955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214048541560918410090253273 160536406170688807567689955)
              ·
                refine ⟨240804609256033211351534933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160536406170688807567689955 240804609256033211351534933)
                ·
                  refine ⟨352741126839892399440725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 240804609256033211351534933 352741126839892399440725)
                  ·
                    rfl

theorem cell23_6182648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 11].length) (baseStart_6182648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182648 prefixEnd_6182648 := by exact prefixLift 6182648
  have htrace : WordTrace (prefixWord ++ tailWord_6182648) baseStart_6182648 baseEnd_6182648 := by
    simpa [prefixWord, tailWord_6182648, baseEnd_6182648] using wordTrace_append hprefix tailTrace_6182648
  have hstable : (prefixWord ++ tailWord_6182648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182648).length < 2 ^ (prefixWord ++ tailWord_6182648).sum := by decide
  have hdescent : baseEnd_6182648 < baseStart_6182648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182659 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 2, 2, 2]
def baseStart_6182659 : Nat := 118140960795 + 6182659 * 2 ^ 59
def prefixEnd_6182659 : Nat := 4983230072969 + 3 ^ 40 * 6182659 * 2
def baseEnd_6182659 : Nat := 3174675789846231051928975

theorem tailTrace_6182659 : CollatzResearch.WordTrace tailWord_6182659 prefixEnd_6182659 3174675789846231051928975 := by
  unfold tailWord_6182659
  simp only [CollatzResearch.WordTrace]
  refine ⟨225500099308289831936695031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150333399538859887957796687 225500099308289831936695031)
  ·
    refine ⟨338250148962434747905042547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225500099308289831936695031 338250148962434747905042547)
    ·
      refine ⟨507375223443652121857563821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338250148962434747905042547 507375223443652121857563821)
      ·
        refine ⟨190265708791369545696586433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507375223443652121857563821 190265708791369545696586433)
        ·
          refine ⟨142699281593527159272439825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190265708791369545696586433 142699281593527159272439825)
          ·
            refine ⟨107024461195145369454329869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142699281593527159272439825 107024461195145369454329869)
            ·
              refine ⟨40134172948179513545373701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107024461195145369454329869 40134172948179513545373701)
              ·
                refine ⟨7525157427783658789757569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40134172948179513545373701 7525157427783658789757569)
                ·
                  refine ⟨5643868070837744092318177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525157427783658789757569 5643868070837744092318177)
                  ·
                    refine ⟨4232901053128308069238633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5643868070837744092318177 4232901053128308069238633)
                    ·
                      refine ⟨3174675789846231051928975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232901053128308069238633 3174675789846231051928975)
                      ·
                        rfl

theorem cell23_6182659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_6182659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182659 prefixEnd_6182659 := by exact prefixLift 6182659
  have htrace : WordTrace (prefixWord ++ tailWord_6182659) baseStart_6182659 baseEnd_6182659 := by
    simpa [prefixWord, tailWord_6182659, baseEnd_6182659] using wordTrace_append hprefix tailTrace_6182659
  have hstable : (prefixWord ++ tailWord_6182659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182659).length < 2 ^ (prefixWord ++ tailWord_6182659).sum := by decide
  have hdescent : baseEnd_6182659 < baseStart_6182659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182710 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6182710 : Nat := 118140960795 + 6182710 * 2 ^ 59
def prefixEnd_6182710 : Nat := 4983230072969 + 3 ^ 40 * 6182710 * 2
def baseEnd_6182710 : Nat := 3174701977359610352391241

theorem tailTrace_6182710 : CollatzResearch.WordTrace tailWord_6182710 prefixEnd_6182710 3174701977359610352391241 := by
  unfold tailWord_6182710
  simp only [CollatzResearch.WordTrace]
  refine ⟨14093872464444066727925099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150334639620736711764534389 14093872464444066727925099)
  ·
    refine ⟨21140808696666100091887649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14093872464444066727925099 21140808696666100091887649)
    ·
      refine ⟨15855606522499575068915737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21140808696666100091887649 15855606522499575068915737)
      ·
        refine ⟨11891704891874681301686803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15855606522499575068915737 11891704891874681301686803)
        ·
          refine ⟨17837557337812021952530205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11891704891874681301686803 17837557337812021952530205)
          ·
            refine ⟨6689084001679508232198827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17837557337812021952530205 6689084001679508232198827)
            ·
              refine ⟨10033626002519262348298241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689084001679508232198827 10033626002519262348298241)
              ·
                refine ⟨7525219501889446761223681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10033626002519262348298241 7525219501889446761223681)
                ·
                  refine ⟨5643914626417085070917761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525219501889446761223681 5643914626417085070917761)
                  ·
                    refine ⟨4232935969812813803188321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5643914626417085070917761 4232935969812813803188321)
                    ·
                      refine ⟨3174701977359610352391241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4232935969812813803188321 3174701977359610352391241)
                      ·
                        rfl

theorem cell23_6182710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6182710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182710 prefixEnd_6182710 := by exact prefixLift 6182710
  have htrace : WordTrace (prefixWord ++ tailWord_6182710) baseStart_6182710 baseEnd_6182710 := by
    simpa [prefixWord, tailWord_6182710, baseEnd_6182710] using wordTrace_append hprefix tailTrace_6182710
  have hstable : (prefixWord ++ tailWord_6182710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182710).length < 2 ^ (prefixWord ++ tailWord_6182710).sum := by decide
  have hdescent : baseEnd_6182710 < baseStart_6182710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182726 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6182726 : Nat := 118140960795 + 6182726 * 2 ^ 59
def prefixEnd_6182726 : Nat := 4983230072969 + 3 ^ 40 * 6182726 * 2
def baseEnd_6182726 : Nat := 3174710193050082289791167

theorem tailTrace_6182726 : CollatzResearch.WordTrace tailWord_6182726 prefixEnd_6182726 3174710193050082289791167 := by
  unfold tailWord_6182726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046954468720221949355751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150335028666031401586256021 7046954468720221949355751)
  ·
    refine ⟨10570431703080332924033627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7046954468720221949355751 10570431703080332924033627)
    ·
      refine ⟨15855647554620499386050441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10570431703080332924033627 15855647554620499386050441)
      ·
        refine ⟨11891735665965374539537831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15855647554620499386050441 11891735665965374539537831)
        ·
          refine ⟨17837603498948061809306747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11891735665965374539537831 17837603498948061809306747)
          ·
            refine ⟨26756405248422092713960121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17837603498948061809306747 26756405248422092713960121)
            ·
              refine ⟨20067303936316569535470091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26756405248422092713960121 20067303936316569535470091)
              ·
                refine ⟨30100955904474854303205137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20067303936316569535470091 30100955904474854303205137)
                ·
                  refine ⟨22575716928356140727403853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30100955904474854303205137 22575716928356140727403853)
                  ·
                    refine ⟨8465893848133552772776445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22575716928356140727403853 8465893848133552772776445)
                    ·
                      refine ⟨3174710193050082289791167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465893848133552772776445 3174710193050082289791167)
                      ·
                        rfl

theorem cell23_6182726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6182726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182726 prefixEnd_6182726 := by exact prefixLift 6182726
  have htrace : WordTrace (prefixWord ++ tailWord_6182726) baseStart_6182726 baseEnd_6182726 := by
    simpa [prefixWord, tailWord_6182726, baseEnd_6182726] using wordTrace_append hprefix tailTrace_6182726
  have hstable : (prefixWord ++ tailWord_6182726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182726).length < 2 ^ (prefixWord ++ tailWord_6182726).sum := by decide
  have hdescent : baseEnd_6182726 < baseStart_6182726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182745 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_6182745 : Nat := 118140960795 + 6182745 * 2 ^ 59
def prefixEnd_6182745 : Nat := 4983230072969 + 3 ^ 40 * 6182745 * 2
def baseEnd_6182745 : Nat := 3174719949182517715453579

theorem tailTrace_6182745 : CollatzResearch.WordTrace tailWord_6182745 prefixEnd_6182745 3174719949182517715453579 := by
  unfold tailWord_6182745
  simp only [CollatzResearch.WordTrace]
  refine ⟨225503235985978268624325689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150335490657318845749550459 225503235985978268624325689)
  ·
    refine ⟨169127426989483701468244267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225503235985978268624325689 169127426989483701468244267)
    ·
      refine ⟨253691140484225552202366401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169127426989483701468244267 253691140484225552202366401)
      ·
        refine ⟨190268355363169164151774801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253691140484225552202366401 190268355363169164151774801)
        ·
          refine ⟨142701266522376873113831101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190268355363169164151774801 142701266522376873113831101)
          ·
            refine ⟨53512974945891327417686663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142701266522376873113831101 53512974945891327417686663)
            ·
              refine ⟨80269462418836991126529995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53512974945891327417686663 80269462418836991126529995)
              ·
                refine ⟨120404193628255486689794993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80269462418836991126529995 120404193628255486689794993)
                ·
                  refine ⟨90303145221191615017346245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120404193628255486689794993 90303145221191615017346245)
                  ·
                    refine ⟨16931839728973427815752421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90303145221191615017346245 16931839728973427815752421)
                    ·
                      refine ⟨3174719949182517715453579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16931839728973427815752421 3174719949182517715453579)
                      ·
                        rfl

theorem cell23_6182745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_6182745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182745 prefixEnd_6182745 := by exact prefixLift 6182745
  have htrace : WordTrace (prefixWord ++ tailWord_6182745) baseStart_6182745 baseEnd_6182745 := by
    simpa [prefixWord, tailWord_6182745, baseEnd_6182745] using wordTrace_append hprefix tailTrace_6182745
  have hstable : (prefixWord ++ tailWord_6182745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182745).length < 2 ^ (prefixWord ++ tailWord_6182745).sum := by decide
  have hdescent : baseEnd_6182745 < baseStart_6182745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182752 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3]
def baseStart_6182752 : Nat := 118140960795 + 6182752 * 2 ^ 59
def prefixEnd_6182752 : Nat := 4983230072969 + 3 ^ 40 * 6182752 * 2
def baseEnd_6182752 : Nat := 3174723543547099188066047

theorem tailTrace_6182752 : CollatzResearch.WordTrace tailWord_6182752 prefixEnd_6182752 3174723543547099188066047 := by
  unfold tailWord_6182752
  simp only [CollatzResearch.WordTrace]
  refine ⟨112751745648476454409915255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150335660864635272546553673 112751745648476454409915255)
  ·
    refine ⟨169127618472714681614872883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112751745648476454409915255 169127618472714681614872883)
    ·
      refine ⟨253691427709072022422309325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169127618472714681614872883 253691427709072022422309325)
      ·
        refine ⟨95134285390902008408365997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253691427709072022422309325 95134285390902008408365997)
        ·
          refine ⟨35675357021588253153137249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95134285390902008408365997 35675357021588253153137249)
          ·
            refine ⟨26756517766191189864852937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35675357021588253153137249 26756517766191189864852937)
            ·
              refine ⟨20067388324643392398639703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26756517766191189864852937 20067388324643392398639703)
              ·
                refine ⟨30101082486965088597959555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20067388324643392398639703 30101082486965088597959555)
                ·
                  refine ⟨45151623730447632896939333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30101082486965088597959555 45151623730447632896939333)
                  ·
                    refine ⟨8465929449458931168176125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45151623730447632896939333 8465929449458931168176125)
                    ·
                      refine ⟨3174723543547099188066047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8465929449458931168176125 3174723543547099188066047)
                      ·
                        rfl

theorem cell23_6182752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_6182752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182752 prefixEnd_6182752 := by exact prefixLift 6182752
  have htrace : WordTrace (prefixWord ++ tailWord_6182752) baseStart_6182752 baseEnd_6182752 := by
    simpa [prefixWord, tailWord_6182752, baseEnd_6182752] using wordTrace_append hprefix tailTrace_6182752
  have hstable : (prefixWord ++ tailWord_6182752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182752).length < 2 ^ (prefixWord ++ tailWord_6182752).sum := by decide
  have hdescent : baseEnd_6182752 < baseStart_6182752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182809 : List Nat := [1, 2, 1, 2, 1, 3, 3, 3, 2, 3, 2]
def baseStart_6182809 : Nat := 118140960795 + 6182809 * 2 ^ 59
def prefixEnd_6182809 : Nat := 4983230072969 + 3 ^ 40 * 6182809 * 2
def baseEnd_6182809 : Nat := 3174752811944405465053285

theorem tailTrace_6182809 : CollatzResearch.WordTrace tailWord_6182809 prefixEnd_6182809 3174752811944405465053285 := by
  unfold tailWord_6182809
  simp only [CollatzResearch.WordTrace]
  refine ⟨225505570257746407554655481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150337046838497605036436987 225505570257746407554655481)
  ·
    refine ⟨169129177693309805665991611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225505570257746407554655481 169129177693309805665991611)
    ·
      refine ⟨253693766539964708498987417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169129177693309805665991611 253693766539964708498987417)
      ·
        refine ⟨190270324904973531374240563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253693766539964708498987417 190270324904973531374240563)
        ·
          refine ⟨285405487357460297061360845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190270324904973531374240563 285405487357460297061360845)
          ·
            refine ⟨107027057759047611398010317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285405487357460297061360845 107027057759047611398010317)
            ·
              refine ⟨40135146659642854274253869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107027057759047611398010317 40135146659642854274253869)
              ·
                refine ⟨15050679997366070352845201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40135146659642854274253869 15050679997366070352845201)
                ·
                  refine ⟨11288009998024552764633901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15050679997366070352845201 11288009998024552764633901)
                  ·
                    refine ⟨4233003749259207286737713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11288009998024552764633901 4233003749259207286737713)
                    ·
                      refine ⟨3174752811944405465053285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233003749259207286737713 3174752811944405465053285)
                      ·
                        rfl

theorem cell23_6182809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_6182809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182809 prefixEnd_6182809 := by exact prefixLift 6182809
  have htrace : WordTrace (prefixWord ++ tailWord_6182809) baseStart_6182809 baseEnd_6182809 := by
    simpa [prefixWord, tailWord_6182809, baseEnd_6182809] using wordTrace_append hprefix tailTrace_6182809
  have hstable : (prefixWord ++ tailWord_6182809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182809).length < 2 ^ (prefixWord ++ tailWord_6182809).sum := by decide
  have hdescent : baseEnd_6182809 < baseStart_6182809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182816 : List Nat := [2, 1, 1, 4, 1, 1, 1, 7, 1, 1, 3]
def baseStart_6182816 : Nat := 118140960795 + 6182816 * 2 ^ 59
def prefixEnd_6182816 : Nat := 4983230072969 + 3 ^ 40 * 6182816 * 2
def baseEnd_6182816 : Nat := 3174756406308986937665753

theorem tailTrace_6182816 : CollatzResearch.WordTrace tailWord_6182816 prefixEnd_6182816 3174756406308986937665753 := by
  unfold tailWord_6182816
  simp only [CollatzResearch.WordTrace]
  refine ⟨112752912784360523875080151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150337217045814031833440201 112752912784360523875080151)
  ·
    refine ⟨169129369176540785812620227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112752912784360523875080151 169129369176540785812620227)
    ·
      refine ⟨253694053764811178718930341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169129369176540785812620227 253694053764811178718930341)
      ·
        refine ⟨47567635080902096009799439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253694053764811178718930341 47567635080902096009799439)
        ·
          refine ⟨71351452621353144014699159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47567635080902096009799439 71351452621353144014699159)
          ·
            refine ⟨107027178932029716022048739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71351452621353144014699159 107027178932029716022048739)
            ·
              refine ⟨160540768398044574033073109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107027178932029716022048739 160540768398044574033073109)
              ·
                refine ⟨3762674259329169703900151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160540768398044574033073109 3762674259329169703900151)
                ·
                  refine ⟨5644011388993754555850227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762674259329169703900151 5644011388993754555850227)
                  ·
                    refine ⟨8466017083490631833775341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5644011388993754555850227 8466017083490631833775341)
                    ·
                      refine ⟨3174756406308986937665753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8466017083490631833775341 3174756406308986937665753)
                      ·
                        rfl

theorem cell23_6182816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_6182816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182816 prefixEnd_6182816 := by exact prefixLift 6182816
  have htrace : WordTrace (prefixWord ++ tailWord_6182816) baseStart_6182816 baseEnd_6182816 := by
    simpa [prefixWord, tailWord_6182816, baseEnd_6182816] using wordTrace_append hprefix tailTrace_6182816
  have hstable : (prefixWord ++ tailWord_6182816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182816).length < 2 ^ (prefixWord ++ tailWord_6182816).sum := by decide
  have hdescent : baseEnd_6182816 < baseStart_6182816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182833 : List Nat := [1, 2, 2, 4, 2, 2, 1, 4, 1, 1, 3]
def baseStart_6182833 : Nat := 118140960795 + 6182833 * 2 ^ 59
def prefixEnd_6182833 : Nat := 4983230072969 + 3 ^ 40 * 6182833 * 2
def baseEnd_6182833 : Nat := 3174765135480113371153175

theorem tailTrace_6182833 : CollatzResearch.WordTrace tailWord_6182833 prefixEnd_6182833 3174765135480113371153175 := by
  unfold tailWord_6182833
  simp only [CollatzResearch.WordTrace]
  refine ⟨225506445609659459653529153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150337630406439639769019435 225506445609659459653529153)
  ·
    refine ⟨169129834207244594740146865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225506445609659459653529153 169129834207244594740146865)
    ·
      refine ⟨126847375655433446055110149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169129834207244594740146865 126847375655433446055110149)
      ·
        refine ⟨23783882935393771135333153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126847375655433446055110149 23783882935393771135333153)
        ·
          refine ⟨17837912201545328351499865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23783882935393771135333153 17837912201545328351499865)
          ·
            refine ⟨13378434151158996263624899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17837912201545328351499865 13378434151158996263624899)
            ·
              refine ⟨20067651226738494395437349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13378434151158996263624899 20067651226738494395437349)
              ·
                refine ⟨3762684605013467699144503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20067651226738494395437349 3762684605013467699144503)
                ·
                  refine ⟨5644026907520201548716755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762684605013467699144503 5644026907520201548716755)
                  ·
                    refine ⟨8466040361280302323075133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5644026907520201548716755 8466040361280302323075133)
                    ·
                      refine ⟨3174765135480113371153175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8466040361280302323075133 3174765135480113371153175)
                      ·
                        rfl

theorem cell23_6182833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_6182833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182833 prefixEnd_6182833 := by exact prefixLift 6182833
  have htrace : WordTrace (prefixWord ++ tailWord_6182833) baseStart_6182833 baseEnd_6182833 := by
    simpa [prefixWord, tailWord_6182833, baseEnd_6182833] using wordTrace_append hprefix tailTrace_6182833
  have hstable : (prefixWord ++ tailWord_6182833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182833).length < 2 ^ (prefixWord ++ tailWord_6182833).sum := by decide
  have hdescent : baseEnd_6182833 < baseStart_6182833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182856 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_6182856 : Nat := 118140960795 + 6182856 * 2 ^ 59
def prefixEnd_6182856 : Nat := 4983230072969 + 3 ^ 40 * 6182856 * 2
def baseEnd_6182856 : Nat := 3174776945535166781165569

theorem tailTrace_6182856 : CollatzResearch.WordTrace tailWord_6182856 prefixEnd_6182856 3174776945535166781165569 := by
  unfold tailWord_6182856
  simp only [CollatzResearch.WordTrace]
  refine ⟨112753642244288067290808211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150338189659050756387744281 112753642244288067290808211)
  ·
    refine ⟨169130463366432100936212317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112753642244288067290808211 169130463366432100936212317)
    ·
      refine ⟨63423923762412037851079619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169130463366432100936212317 63423923762412037851079619)
      ·
        refine ⟨95135885643618056776619429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63423923762412037851079619 95135885643618056776619429)
        ·
          refine ⟨17837978558178385645616143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95135885643618056776619429 17837978558178385645616143)
          ·
            refine ⟨26756967837267578468424215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17837978558178385645616143 26756967837267578468424215)
            ·
              refine ⟨40135451755901367702636323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26756967837267578468424215 40135451755901367702636323)
              ·
                refine ⟨60203177633852051553954485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40135451755901367702636323 60203177633852051553954485)
                ·
                  refine ⟨5644047903173629833183233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60203177633852051553954485 5644047903173629833183233)
                  ·
                    refine ⟨4233035927380222374887425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5644047903173629833183233 4233035927380222374887425)
                    ·
                      refine ⟨3174776945535166781165569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233035927380222374887425 3174776945535166781165569)
                      ·
                        rfl

theorem cell23_6182856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_6182856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182856 prefixEnd_6182856 := by exact prefixLift 6182856
  have htrace : WordTrace (prefixWord ++ tailWord_6182856) baseStart_6182856 baseEnd_6182856 := by
    simpa [prefixWord, tailWord_6182856, baseEnd_6182856] using wordTrace_append hprefix tailTrace_6182856
  have hstable : (prefixWord ++ tailWord_6182856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182856).length < 2 ^ (prefixWord ++ tailWord_6182856).sum := by decide
  have hdescent : baseEnd_6182856 < baseStart_6182856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182859 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 3]
def baseStart_6182859 : Nat := 118140960795 + 6182859 * 2 ^ 59
def prefixEnd_6182859 : Nat := 4983230072969 + 3 ^ 40 * 6182859 * 2
def baseEnd_6182859 : Nat := 3174778485977130269428055

theorem tailTrace_6182859 : CollatzResearch.WordTrace tailWord_6182859 prefixEnd_6182859 3174778485977130269428055 := by
  unfold tailWord_6182859
  simp only [CollatzResearch.WordTrace]
  refine ⟨225507393907565266093975631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150338262605043510729317087 225507393907565266093975631)
  ·
    refine ⟨338261090861347899140963447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225507393907565266093975631 338261090861347899140963447)
    ·
      refine ⟨507391636292021848711445171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338261090861347899140963447 507391636292021848711445171)
      ·
        refine ⟨761087454438032773067167757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507391636292021848711445171 761087454438032773067167757)
        ·
          refine ⟨285407795414262289900187909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 761087454438032773067167757 285407795414262289900187909)
          ·
            refine ⟨53513961640174179356285233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285407795414262289900187909 53513961640174179356285233)
            ·
              refine ⟨40135471230130634517213925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53513961640174179356285233 40135471230130634517213925)
              ·
                refine ⟨7525400855649493971977611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40135471230130634517213925 7525400855649493971977611)
                ·
                  refine ⟨11288101283474240957966417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7525400855649493971977611 11288101283474240957966417)
                  ·
                    refine ⟨8466075962605680718474813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11288101283474240957966417 8466075962605680718474813)
                    ·
                      refine ⟨3174778485977130269428055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8466075962605680718474813 3174778485977130269428055)
                      ·
                        rfl

theorem cell23_6182859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 2, 3].length) (baseStart_6182859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182859 prefixEnd_6182859 := by exact prefixLift 6182859
  have htrace : WordTrace (prefixWord ++ tailWord_6182859) baseStart_6182859 baseEnd_6182859 := by
    simpa [prefixWord, tailWord_6182859, baseEnd_6182859] using wordTrace_append hprefix tailTrace_6182859
  have hstable : (prefixWord ++ tailWord_6182859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182859).length < 2 ^ (prefixWord ++ tailWord_6182859).sum := by decide
  have hdescent : baseEnd_6182859 < baseStart_6182859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182869 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6182869 : Nat := 118140960795 + 6182869 * 2 ^ 59
def prefixEnd_6182869 : Nat := 4983230072969 + 3 ^ 40 * 6182869 * 2
def baseEnd_6182869 : Nat := 3174783620783675230303009

theorem tailTrace_6182869 : CollatzResearch.WordTrace tailWord_6182869 prefixEnd_6182869 3174783620783675230303009 := by
  unfold tailWord_6182869
  simp only [CollatzResearch.WordTrace]
  refine ⟨225507758637529037801839661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150338505758352691867893107 225507758637529037801839661)
  ·
    refine ⟨84565409489073389175689873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225507758637529037801839661 84565409489073389175689873)
    ·
      refine ⟨63424057116805041881767405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84565409489073389175689873 63424057116805041881767405)
      ·
        refine ⟨23784021418801890705662777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63424057116805041881767405 23784021418801890705662777)
        ·
          refine ⟨17838016064101418029247083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23784021418801890705662777 17838016064101418029247083)
          ·
            refine ⟨26757024096152127043870625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17838016064101418029247083 26757024096152127043870625)
            ·
              refine ⟨20067768072114095282902969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26757024096152127043870625 20067768072114095282902969)
              ·
                refine ⟨15050826054085571462177227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20067768072114095282902969 15050826054085571462177227)
                ·
                  refine ⟨22576239081128357193265841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15050826054085571462177227 22576239081128357193265841)
                  ·
                    refine ⟨16932179310846267894949381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22576239081128357193265841 16932179310846267894949381)
                    ·
                      refine ⟨3174783620783675230303009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16932179310846267894949381 3174783620783675230303009)
                      ·
                        rfl

theorem cell23_6182869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6182869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182869 prefixEnd_6182869 := by exact prefixLift 6182869
  have htrace : WordTrace (prefixWord ++ tailWord_6182869) baseStart_6182869 baseEnd_6182869 := by
    simpa [prefixWord, tailWord_6182869, baseEnd_6182869] using wordTrace_append hprefix tailTrace_6182869
  have hstable : (prefixWord ++ tailWord_6182869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182869).length < 2 ^ (prefixWord ++ tailWord_6182869).sum := by decide
  have hdescent : baseEnd_6182869 < baseStart_6182869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182870 : List Nat := [5, 2, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_6182870 : Nat := 118140960795 + 6182870 * 2 ^ 59
def prefixEnd_6182870 : Nat := 4983230072969 + 3 ^ 40 * 6182870 * 2
def baseEnd_6182870 : Nat := 1058261378088109908796835

theorem tailTrace_6182870 : CollatzResearch.WordTrace tailWord_6182870 prefixEnd_6182870 1058261378088109908796835 := by
  unfold tailWord_6182870
  simp only [CollatzResearch.WordTrace]
  refine ⟨14094237194407838435789129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150338530073683609981750709 14094237194407838435789129)
  ·
    refine ⟨10570677895805878826841847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14094237194407838435789129 10570677895805878826841847)
    ·
      refine ⟨15856016843708818240262771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10570677895805878826841847 15856016843708818240262771)
      ·
        refine ⟨23784025265563227360394157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15856016843708818240262771 23784025265563227360394157)
        ·
          refine ⟨8919009474586210260147809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23784025265563227360394157 8919009474586210260147809)
          ·
            refine ⟨6689257105939657695110857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919009474586210260147809 6689257105939657695110857)
            ·
              refine ⟨5016942829454743271333143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689257105939657695110857 5016942829454743271333143)
              ·
                refine ⟨7525414244182114906999715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5016942829454743271333143 7525414244182114906999715)
                ·
                  refine ⟨11288121366273172360499573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7525414244182114906999715 11288121366273172360499573)
                  ·
                    refine ⟨1058261378088109908796835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11288121366273172360499573 1058261378088109908796835)
                    ·
                      rfl

theorem cell23_6182870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_6182870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182870 prefixEnd_6182870 := by exact prefixLift 6182870
  have htrace : WordTrace (prefixWord ++ tailWord_6182870) baseStart_6182870 baseEnd_6182870 := by
    simpa [prefixWord, tailWord_6182870, baseEnd_6182870] using wordTrace_append hprefix tailTrace_6182870
  have hstable : (prefixWord ++ tailWord_6182870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182870).length < 2 ^ (prefixWord ++ tailWord_6182870).sum := by decide
  have hdescent : baseEnd_6182870 < baseStart_6182870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182873 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 1, 1, 4]
def baseStart_6182873 : Nat := 118140960795 + 6182873 * 2 ^ 59
def prefixEnd_6182873 : Nat := 4983230072969 + 3 ^ 40 * 6182873 * 2
def baseEnd_6182873 : Nat := 3174785674706293214652991

theorem tailTrace_6182873 : CollatzResearch.WordTrace tailWord_6182873 prefixEnd_6182873 3174785674706293214652991 := by
  unfold tailWord_6182873
  simp only [CollatzResearch.WordTrace]
  refine ⟨225507904529514546484985273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150338603019676364323323515 225507904529514546484985273)
  ·
    refine ⟨169130928397135909863738955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225507904529514546484985273 169130928397135909863738955)
    ·
      refine ⟨253696392595703864795608433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169130928397135909863738955 253696392595703864795608433)
      ·
        refine ⟨190272294446777898596706325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253696392595703864795608433 190272294446777898596706325)
        ·
          refine ⟨8919013802192713996720609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190272294446777898596706325 8919013802192713996720609)
          ·
            refine ⟨6689260351644535497540457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919013802192713996720609 6689260351644535497540457)
            ·
              refine ⟨5016945263733401623155343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689260351644535497540457 5016945263733401623155343)
              ·
                refine ⟨7525417895600102434733015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5016945263733401623155343 7525417895600102434733015)
                ·
                  refine ⟨11288126843400153652099523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7525417895600102434733015 11288126843400153652099523)
                  ·
                    refine ⟨16932190265100230478149285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11288126843400153652099523 16932190265100230478149285)
                    ·
                      refine ⟨3174785674706293214652991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16932190265100230478149285 3174785674706293214652991)
                      ·
                        rfl

theorem cell23_6182873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_6182873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182873 prefixEnd_6182873 := by exact prefixLift 6182873
  have htrace : WordTrace (prefixWord ++ tailWord_6182873) baseStart_6182873 baseEnd_6182873 := by
    simpa [prefixWord, tailWord_6182873, baseEnd_6182873] using wordTrace_append hprefix tailTrace_6182873
  have hstable : (prefixWord ++ tailWord_6182873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182873).length < 2 ^ (prefixWord ++ tailWord_6182873).sum := by decide
  have hdescent : baseEnd_6182873 < baseStart_6182873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182899 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 5, 3, 2]
def baseStart_6182899 : Nat := 118140960795 + 6182899 * 2 ^ 59
def prefixEnd_6182899 : Nat := 4983230072969 + 3 ^ 40 * 6182899 * 2
def baseEnd_6182899 : Nat := 3174799025203310112927871

theorem tailTrace_6182899 : CollatzResearch.WordTrace tailWord_6182899 prefixEnd_6182899 3174799025203310112927871 := by
  unfold tailWord_6182899
  simp only [CollatzResearch.WordTrace]
  refine ⟨225508852827420352925431751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150339235218280235283621167 225508852827420352925431751)
  ·
    refine ⟨338263279241130529388147627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225508852827420352925431751 338263279241130529388147627)
    ·
      refine ⟨507394918861695794082221441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338263279241130529388147627 507394918861695794082221441)
      ·
        refine ⟨380546189146271845561666081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507394918861695794082221441 380546189146271845561666081)
        ·
          refine ⟨285409641859703884171249561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380546189146271845561666081 285409641859703884171249561)
          ·
            refine ⟨214057231394777913128437171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285409641859703884171249561 214057231394777913128437171)
            ·
              refine ⟨321085847092166869692655757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214057231394777913128437171 321085847092166869692655757)
              ·
                refine ⟨120407192659562576134745909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321085847092166869692655757 120407192659562576134745909)
                ·
                  refine ⟨11288174311833991512632429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120407192659562576134745909 11288174311833991512632429)
                  ·
                    refine ⟨4233065366937746817237161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11288174311833991512632429 4233065366937746817237161)
                    ·
                      refine ⟨3174799025203310112927871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233065366937746817237161 3174799025203310112927871)
                      ·
                        rfl

theorem cell23_6182899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 3, 2].length) (baseStart_6182899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182899 prefixEnd_6182899 := by exact prefixLift 6182899
  have htrace : WordTrace (prefixWord ++ tailWord_6182899) baseStart_6182899 baseEnd_6182899 := by
    simpa [prefixWord, tailWord_6182899, baseEnd_6182899] using wordTrace_append hprefix tailTrace_6182899
  have hstable : (prefixWord ++ tailWord_6182899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182899).length < 2 ^ (prefixWord ++ tailWord_6182899).sum := by decide
  have hdescent : baseEnd_6182899 < baseStart_6182899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182918 : List Nat := [6, 2, 1, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6182918 : Nat := 118140960795 + 6182918 * 2 ^ 59
def prefixEnd_6182918 : Nat := 4983230072969 + 3 ^ 40 * 6182918 * 2
def baseEnd_6182918 : Nat := 3174808781335745538590285

theorem tailTrace_6182918 : CollatzResearch.WordTrace tailWord_6182918 prefixEnd_6182918 3174808781335745538590285 := by
  unfold tailWord_6182918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047173306698484974074169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150339697209567679446915605 7047173306698484974074169)
  ·
    refine ⟨5285379980023863730555627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7047173306698484974074169 5285379980023863730555627)
    ·
      refine ⟨7928069970035795595833441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5285379980023863730555627 7928069970035795595833441)
      ·
        refine ⟨5946052477526846696875081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7928069970035795595833441 5946052477526846696875081)
        ·
          refine ⟨4459539358145135022656311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5946052477526846696875081 4459539358145135022656311)
          ·
            refine ⟨6689309037217702533984467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459539358145135022656311 6689309037217702533984467)
            ·
              refine ⟨10033963555826553800976701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689309037217702533984467 10033963555826553800976701)
              ·
                refine ⟨3762736333434957675366263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10033963555826553800976701 3762736333434957675366263)
                ·
                  refine ⟨5644104500152436513049395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762736333434957675366263 5644104500152436513049395)
                  ·
                    refine ⟨8466156750228654769574093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5644104500152436513049395 8466156750228654769574093)
                    ·
                      refine ⟨3174808781335745538590285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8466156750228654769574093 3174808781335745538590285)
                      ·
                        rfl

theorem cell23_6182918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6182918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182918 prefixEnd_6182918 := by exact prefixLift 6182918
  have htrace : WordTrace (prefixWord ++ tailWord_6182918) baseStart_6182918 baseEnd_6182918 := by
    simpa [prefixWord, tailWord_6182918, baseEnd_6182918] using wordTrace_append hprefix tailTrace_6182918
  have hstable : (prefixWord ++ tailWord_6182918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182918).length < 2 ^ (prefixWord ++ tailWord_6182918).sum := by decide
  have hdescent : baseEnd_6182918 < baseStart_6182918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6182999 : List Nat := [1, 1, 3, 2, 2, 1, 4, 2, 2, 5]
def baseStart_6182999 : Nat := 118140960795 + 6182999 * 2 ^ 59
def prefixEnd_6182999 : Nat := 4983230072969 + 3 ^ 40 * 6182999 * 2
def baseEnd_6182999 : Nat := 1058283457756253240559137

theorem tailTrace_6182999 : CollatzResearch.WordTrace tailWord_6182999 prefixEnd_6182999 1058283457756253240559137 := by
  unfold tailWord_6182999
  simp only [CollatzResearch.WordTrace]
  refine ⟨225512500127058070004072051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150341666751372046669381367 225512500127058070004072051)
  ·
    refine ⟨338268750190587105006108077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225512500127058070004072051 338268750190587105006108077)
    ·
      refine ⟨126850781321470164377290529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338268750190587105006108077 126850781321470164377290529)
      ·
        refine ⟨95138085991102623282967897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126850781321470164377290529 95138085991102623282967897)
        ·
          refine ⟨71353564493326967462225923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95138085991102623282967897 71353564493326967462225923)
          ·
            refine ⟨107030346739990451193338885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71353564493326967462225923 107030346739990451193338885)
            ·
              refine ⟨20068190013748209598751041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107030346739990451193338885 20068190013748209598751041)
              ·
                refine ⟨15051142510311157199063281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20068190013748209598751041 15051142510311157199063281)
                ·
                  refine ⟨11288356882733367899297461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15051142510311157199063281 11288356882733367899297461)
                  ·
                    refine ⟨1058283457756253240559137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11288356882733367899297461 1058283457756253240559137)
                    ·
                      rfl

theorem cell23_6182999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_6182999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6182999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6182999 prefixEnd_6182999 := by exact prefixLift 6182999
  have htrace : WordTrace (prefixWord ++ tailWord_6182999) baseStart_6182999 baseEnd_6182999 := by
    simpa [prefixWord, tailWord_6182999, baseEnd_6182999] using wordTrace_append hprefix tailTrace_6182999
  have hstable : (prefixWord ++ tailWord_6182999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6182999).length < 2 ^ (prefixWord ++ tailWord_6182999).sum := by decide
  have hdescent : baseEnd_6182999 < baseStart_6182999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6182999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183036 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 2, 1, 4]
def baseStart_6183036 : Nat := 118140960795 + 6183036 * 2 ^ 59
def prefixEnd_6183036 : Nat := 4983230072969 + 3 ^ 40 * 6183036 * 2
def baseEnd_6183036 : Nat := 3174869372052976076914741

theorem tailTrace_6183036 : CollatzResearch.WordTrace tailWord_6183036 prefixEnd_6183036 3174869372052976076914741 := by
  unfold tailWord_6183036
  simp only [CollatzResearch.WordTrace]
  refine ⟨112756924813962012661584481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150342566418616016882112641 112756924813962012661584481)
  ·
    refine ⟨84567693610471509496188361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112756924813962012661584481 84567693610471509496188361)
    ·
      refine ⟨63425770207853632122141271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84567693610471509496188361 63425770207853632122141271)
      ·
        refine ⟨95138655311780448183211907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63425770207853632122141271 95138655311780448183211907)
        ·
          refine ⟨142707982967670672274817861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95138655311780448183211907 142707982967670672274817861)
          ·
            refine ⟨26757746806438251051528349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142707982967670672274817861 26757746806438251051528349)
            ·
              refine ⟨10034155052414344144323131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26757746806438251051528349 10034155052414344144323131)
              ·
                refine ⟨15051232578621516216484697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034155052414344144323131 15051232578621516216484697)
                ·
                  refine ⟨11288424433966137162363523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15051232578621516216484697 11288424433966137162363523)
                  ·
                    refine ⟨16932636650949205743545285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11288424433966137162363523 16932636650949205743545285)
                    ·
                      refine ⟨3174869372052976076914741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16932636650949205743545285 3174869372052976076914741)
                      ·
                        rfl

theorem cell23_6183036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_6183036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183036 prefixEnd_6183036 := by exact prefixLift 6183036
  have htrace : WordTrace (prefixWord ++ tailWord_6183036) baseStart_6183036 baseEnd_6183036 := by
    simpa [prefixWord, tailWord_6183036, baseEnd_6183036] using wordTrace_append hprefix tailTrace_6183036
  have hstable : (prefixWord ++ tailWord_6183036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183036).length < 2 ^ (prefixWord ++ tailWord_6183036).sum := by decide
  have hdescent : baseEnd_6183036 < baseStart_6183036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183063 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 3, 4]
def baseStart_6183063 : Nat := 118140960795 + 6183063 * 2 ^ 59
def prefixEnd_6183063 : Nat := 4983230072969 + 3 ^ 40 * 6183063 * 2
def baseEnd_6183063 : Nat := 1058294412010215823759039

theorem tailTrace_6183063 : CollatzResearch.WordTrace tailWord_6183063 prefixEnd_6183063 1058294412010215823759039 := by
  unfold tailWord_6183063
  simp only [CollatzResearch.WordTrace]
  refine ⟨225514834398826208934401843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150343222932550805956267895 225514834398826208934401843)
  ·
    refine ⟨338272251598239313401602765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225514834398826208934401843 338272251598239313401602765)
    ·
      refine ⟨126852094349339742525601037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338272251598239313401602765 126852094349339742525601037)
      ·
        refine ⟨47569535381002403447100389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126852094349339742525601037 47569535381002403447100389)
        ·
          refine ⟨8919287883937950646331323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47569535381002403447100389 8919287883937950646331323)
          ·
            refine ⟨13378931825906925969496985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8919287883937950646331323 13378931825906925969496985)
            ·
              refine ⟨10034198869430194477122739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13378931825906925969496985 10034198869430194477122739)
              ·
                refine ⟨15051298304145291715684109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034198869430194477122739 15051298304145291715684109)
                ·
                  refine ⟨5644236864054484393381541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15051298304145291715684109 5644236864054484393381541)
                  ·
                    refine ⟨1058294412010215823759039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5644236864054484393381541 1058294412010215823759039)
                    ·
                      rfl

theorem cell23_6183063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_6183063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183063 prefixEnd_6183063 := by exact prefixLift 6183063
  have htrace : WordTrace (prefixWord ++ tailWord_6183063) baseStart_6183063 baseEnd_6183063 := by
    simpa [prefixWord, tailWord_6183063, baseEnd_6183063] using wordTrace_append hprefix tailTrace_6183063
  have hstable : (prefixWord ++ tailWord_6183063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183063).length < 2 ^ (prefixWord ++ tailWord_6183063).sum := by decide
  have hdescent : baseEnd_6183063 < baseStart_6183063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183096 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 1, 5, 2]
def baseStart_6183096 : Nat := 118140960795 + 6183096 * 2 ^ 59
def prefixEnd_6183096 : Nat := 4983230072969 + 3 ^ 40 * 6183096 * 2
def baseEnd_6183096 : Nat := 3174900180892245842164465

theorem tailTrace_6183096 : CollatzResearch.WordTrace tailWord_6183096 prefixEnd_6183096 3174900180892245842164465 := by
  unfold tailWord_6183096
  simp only [CollatzResearch.WordTrace]
  refine ⟨112758019003853327785176571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150344025338471103713568761 112758019003853327785176571)
  ·
    refine ⟨169137028505779991677764857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112758019003853327785176571 169137028505779991677764857)
    ·
      refine ⟨126852771379334993758323643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169137028505779991677764857 126852771379334993758323643)
      ·
        refine ⟨190279157069002490637485465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126852771379334993758323643 190279157069002490637485465)
        ·
          refine ⟨142709367801751867978114099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190279157069002490637485465 142709367801751867978114099)
          ·
            refine ⟨214064051702627801967171149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142709367801751867978114099 214064051702627801967171149)
            ·
              refine ⟨80274019388485425737689181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214064051702627801967171149 80274019388485425737689181)
              ·
                refine ⟨30102757270682034651633443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80274019388485425737689181 30102757270682034651633443)
                ·
                  refine ⟨45154135906023051977450165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30102757270682034651633443 45154135906023051977450165)
                  ·
                    refine ⟨4233200241189661122885953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45154135906023051977450165 4233200241189661122885953)
                    ·
                      refine ⟨3174900180892245842164465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233200241189661122885953 3174900180892245842164465)
                      ·
                        rfl

theorem cell23_6183096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 1, 5, 2].length) (baseStart_6183096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183096 prefixEnd_6183096 := by exact prefixLift 6183096
  have htrace : WordTrace (prefixWord ++ tailWord_6183096) baseStart_6183096 baseEnd_6183096 := by
    simpa [prefixWord, tailWord_6183096, baseEnd_6183096] using wordTrace_append hprefix tailTrace_6183096
  have hstable : (prefixWord ++ tailWord_6183096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183096).length < 2 ^ (prefixWord ++ tailWord_6183096).sum := by decide
  have hdescent : baseEnd_6183096 < baseStart_6183096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183143 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6183143 : Nat := 118140960795 + 6183143 * 2 ^ 59
def prefixEnd_6183143 : Nat := 4983230072969 + 3 ^ 40 * 6183143 * 2
def baseEnd_6183143 : Nat := 3174924314483007158276749

theorem tailTrace_6183143 : CollatzResearch.WordTrace tailWord_6183143 prefixEnd_6183143 3174924314483007158276749 := by
  unfold tailWord_6183143
  simp only [CollatzResearch.WordTrace]
  refine ⟨225517752238536382597314083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150345168159024255064876055 225517752238536382597314083)
  ·
    refine ⟨338276628357804573895971125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225517752238536382597314083 338276628357804573895971125)
    ·
      refine ⟨31713433908544178802747293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 338276628357804573895971125 31713433908544178802747293)
      ·
        refine ⟨11892537715704067051030235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31713433908544178802747293 11892537715704067051030235)
        ·
          refine ⟨17838806573556100576545353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11892537715704067051030235 17838806573556100576545353)
          ·
            refine ⟨13379104930167075432409015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17838806573556100576545353 13379104930167075432409015)
            ·
              refine ⟨20068657395250613148613523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13379104930167075432409015 20068657395250613148613523)
              ·
                refine ⟨30102986092875919722920285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20068657395250613148613523 30102986092875919722920285)
                ·
                  refine ⟨11288619784828469896095107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30102986092875919722920285 11288619784828469896095107)
                  ·
                    refine ⟨16932929677242704844142661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11288619784828469896095107 16932929677242704844142661)
                    ·
                      refine ⟨3174924314483007158276749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16932929677242704844142661 3174924314483007158276749)
                      ·
                        rfl

theorem cell23_6183143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6183143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183143 prefixEnd_6183143 := by exact prefixLift 6183143
  have htrace : WordTrace (prefixWord ++ tailWord_6183143) baseStart_6183143 baseEnd_6183143 := by
    simpa [prefixWord, tailWord_6183143, baseEnd_6183143] using wordTrace_append hprefix tailTrace_6183143
  have hstable : (prefixWord ++ tailWord_6183143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183143).length < 2 ^ (prefixWord ++ tailWord_6183143).sum := by decide
  have hdescent : baseEnd_6183143 < baseStart_6183143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183170 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_6183170 : Nat := 118140960795 + 6183170 * 2 ^ 59
def prefixEnd_6183170 : Nat := 4983230072969 + 3 ^ 40 * 6183170 * 2
def baseEnd_6183170 : Nat := 1058312726153559517546375

theorem tailTrace_6183170 : CollatzResearch.WordTrace tailWord_6183170 prefixEnd_6183170 1058312726153559517546375 := by
  unfold tailWord_6183170
  simp only [CollatzResearch.WordTrace]
  refine ⟨56379684252359641552136741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150345824672959044139031309 56379684252359641552136741)
  ·
    refine ⟨10571190797317432791025639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56379684252359641552136741 10571190797317432791025639)
    ·
      refine ⟨15856786195976149186538459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10571190797317432791025639 15856786195976149186538459)
      ·
        refine ⟨23785179293964223779807689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15856786195976149186538459 23785179293964223779807689)
        ·
          refine ⟨17838884470473167834855767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23785179293964223779807689 17838884470473167834855767)
          ·
            refine ⟨26758326705709751752283651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17838884470473167834855767 26758326705709751752283651)
            ·
              refine ⟨40137490058564627628425477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26758326705709751752283651 40137490058564627628425477)
              ·
                refine ⟨7525779385980867680329777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40137490058564627628425477 7525779385980867680329777)
                ·
                  refine ⟨5644334539485650760247333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7525779385980867680329777 5644334539485650760247333)
                  ·
                    refine ⟨1058312726153559517546375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5644334539485650760247333 1058312726153559517546375)
                    ·
                      rfl

theorem cell23_6183170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_6183170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183170 prefixEnd_6183170 := by exact prefixLift 6183170
  have htrace : WordTrace (prefixWord ++ tailWord_6183170) baseStart_6183170 baseEnd_6183170 := by
    simpa [prefixWord, tailWord_6183170, baseEnd_6183170] using wordTrace_append hprefix tailTrace_6183170
  have hstable : (prefixWord ++ tailWord_6183170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183170).length < 2 ^ (prefixWord ++ tailWord_6183170).sum := by decide
  have hdescent : baseEnd_6183170 < baseStart_6183170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183177 : List Nat := [1, 2, 1, 1, 3, 5, 1, 4, 1, 2, 2]
def baseStart_6183177 : Nat := 118140960795 + 6183177 * 2 ^ 59
def prefixEnd_6183177 : Nat := 4983230072969 + 3 ^ 40 * 6183177 * 2
def baseEnd_6183177 : Nat := 3174941772825260025251593

theorem tailTrace_6183177 : CollatzResearch.WordTrace tailWord_6183177 prefixEnd_6183177 3174941772825260025251593 := by
  unfold tailWord_6183177
  simp only [CollatzResearch.WordTrace]
  refine ⟨225518992320413206404051785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150345994880275470936034523 225518992320413206404051785)
  ·
    refine ⟨169139244240309904803038839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225518992320413206404051785 169139244240309904803038839)
    ·
      refine ⟨253708866360464857204558259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169139244240309904803038839 253708866360464857204558259)
      ·
        refine ⟨380563299540697285806837389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253708866360464857204558259 380563299540697285806837389)
        ·
          refine ⟨142711237327761482177564021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380563299540697285806837389 142711237327761482177564021)
          ·
            refine ⟨13379178499477638954146627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142711237327761482177564021 13379178499477638954146627)
            ·
              refine ⟨20068767749216458431219941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13379178499477638954146627 20068767749216458431219941)
              ·
                refine ⟨3762893952978085955853739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20068767749216458431219941 3762893952978085955853739)
                ·
                  refine ⟨5644340929467128933780609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762893952978085955853739 5644340929467128933780609)
                  ·
                    refine ⟨4233255697100346700335457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5644340929467128933780609 4233255697100346700335457)
                    ·
                      refine ⟨3174941772825260025251593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233255697100346700335457 3174941772825260025251593)
                      ·
                        rfl

theorem cell23_6183177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 1, 2, 2].length) (baseStart_6183177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183177 prefixEnd_6183177 := by exact prefixLift 6183177
  have htrace : WordTrace (prefixWord ++ tailWord_6183177) baseStart_6183177 baseEnd_6183177 := by
    simpa [prefixWord, tailWord_6183177, baseEnd_6183177] using wordTrace_append hprefix tailTrace_6183177
  have hstable : (prefixWord ++ tailWord_6183177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183177).length < 2 ^ (prefixWord ++ tailWord_6183177).sum := by decide
  have hdescent : baseEnd_6183177 < baseStart_6183177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183179 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 1, 9]
def baseStart_6183179 : Nat := 118140960795 + 6183179 * 2 ^ 59
def prefixEnd_6183179 : Nat := 4983230072969 + 3 ^ 40 * 6183179 * 2
def baseEnd_6183179 : Nat := 1058314266595523005808861

theorem tailTrace_6183179 : CollatzResearch.WordTrace tailWord_6183179 prefixEnd_6183179 1058314266595523005808861 := by
  unfold tailWord_6183179
  simp only [CollatzResearch.WordTrace]
  refine ⟨225519065266405960745624591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150346043510937307163749727 225519065266405960745624591)
  ·
    refine ⟨338278597899608941118436887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225519065266405960745624591 338278597899608941118436887)
    ·
      refine ⟨507417896849413411677655331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338278597899608941118436887 507417896849413411677655331)
      ·
        refine ⟨761126845274120117516482997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507417896849413411677655331 761126845274120117516482997)
        ·
          refine ⟨71355641744448761017170281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 761126845274120117516482997 71355641744448761017170281)
          ·
            refine ⟨53516731308336570762877711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71355641744448761017170281 53516731308336570762877711)
            ·
              refine ⟨80275096962504856144316567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53516731308336570762877711 80275096962504856144316567)
              ·
                refine ⟨120412645443757284216474851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80275096962504856144316567 120412645443757284216474851)
                ·
                  refine ⟨180618968165635926324712277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120412645443757284216474851 180618968165635926324712277)
                  ·
                    refine ⟨1058314266595523005808861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180618968165635926324712277 1058314266595523005808861)
                    ·
                      rfl

theorem cell23_6183179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 9].length) (baseStart_6183179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183179 prefixEnd_6183179 := by exact prefixLift 6183179
  have htrace : WordTrace (prefixWord ++ tailWord_6183179) baseStart_6183179 baseEnd_6183179 := by
    simpa [prefixWord, tailWord_6183179, baseEnd_6183179] using wordTrace_append hprefix tailTrace_6183179
  have hstable : (prefixWord ++ tailWord_6183179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183179).length < 2 ^ (prefixWord ++ tailWord_6183179).sum := by decide
  have hdescent : baseEnd_6183179 < baseStart_6183179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183203 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 3, 3, 2]
def baseStart_6183203 : Nat := 118140960795 + 6183203 * 2 ^ 59
def prefixEnd_6183203 : Nat := 4983230072969 + 3 ^ 40 * 6183203 * 2
def baseEnd_6183203 : Nat := 3174955123322276923526473

theorem tailTrace_6183203 : CollatzResearch.WordTrace tailWord_6183203 prefixEnd_6183203 3174955123322276923526473 := by
  unfold tailWord_6183203
  simp only [CollatzResearch.WordTrace]
  refine ⟨225519940618319012844498263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150346627078879341896332175 225519940618319012844498263)
  ·
    refine ⟨338279910927478519266747395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225519940618319012844498263 338279910927478519266747395)
    ·
      refine ⟨507419866391217778900121093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338279910927478519266747395 507419866391217778900121093)
      ·
        refine ⟨95141224948353333543772705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 507419866391217778900121093 95141224948353333543772705)
        ·
          refine ⟨71355918711265000157829529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95141224948353333543772705 71355918711265000157829529)
          ·
            refine ⟨53516939033448750118372147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71355918711265000157829529 53516939033448750118372147)
            ·
              refine ⟨80275408550173125177558221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53516939033448750118372147 80275408550173125177558221)
              ·
                refine ⟨30103278206314921941584333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80275408550173125177558221 30103278206314921941584333)
                ·
                  refine ⟨11288729327368095728094125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30103278206314921941584333 11288729327368095728094125)
                  ·
                    refine ⟨4233273497763035898035297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11288729327368095728094125 4233273497763035898035297)
                    ·
                      refine ⟨3174955123322276923526473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233273497763035898035297 3174955123322276923526473)
                      ·
                        rfl

theorem cell23_6183203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_6183203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183203 prefixEnd_6183203 := by exact prefixLift 6183203
  have htrace : WordTrace (prefixWord ++ tailWord_6183203) baseStart_6183203 baseEnd_6183203 := by
    simpa [prefixWord, tailWord_6183203, baseEnd_6183203] using wordTrace_append hprefix tailTrace_6183203
  have hstable : (prefixWord ++ tailWord_6183203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183203).length < 2 ^ (prefixWord ++ tailWord_6183203).sum := by decide
  have hdescent : baseEnd_6183203 < baseStart_6183203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183226 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_6183226 : Nat := 118140960795 + 6183226 * 2 ^ 59
def prefixEnd_6183226 : Nat := 4983230072969 + 3 ^ 40 * 6183226 * 2
def baseEnd_6183226 : Nat := 1058322311125776777846289

theorem tailTrace_6183226 : CollatzResearch.WordTrace tailWord_6183226 prefixEnd_6183226 1058322311125776777846289 := by
  unfold tailWord_6183226
  simp only [CollatzResearch.WordTrace]
  refine ⟨56380194874308921943146383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150347186331490458515057021 56380194874308921943146383)
  ·
    refine ⟨84570292311463382914719575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56380194874308921943146383 84570292311463382914719575)
    ·
      refine ⟨126855438467195074372079363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84570292311463382914719575 126855438467195074372079363)
      ·
        refine ⟨190283157700792611558119045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126855438467195074372079363 190283157700792611558119045)
        ·
          refine ⟨35678092068898614667147321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190283157700792611558119045 35678092068898614667147321)
          ·
            refine ⟨26758569051673961000360491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35678092068898614667147321 26758569051673961000360491)
            ·
              refine ⟨40137853577510941500540737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26758569051673961000360491 40137853577510941500540737)
              ·
                refine ⟨30103390183133206125405553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40137853577510941500540737 30103390183133206125405553)
                ·
                  refine ⟨22577542637349904594054165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30103390183133206125405553 22577542637349904594054165)
                  ·
                    refine ⟨1058322311125776777846289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22577542637349904594054165 1058322311125776777846289)
                    ·
                      rfl

theorem cell23_6183226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_6183226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183226 prefixEnd_6183226 := by exact prefixLift 6183226
  have htrace : WordTrace (prefixWord ++ tailWord_6183226) baseStart_6183226 baseEnd_6183226 := by
    simpa [prefixWord, tailWord_6183226, baseEnd_6183226] using wordTrace_append hprefix tailTrace_6183226
  have hstable : (prefixWord ++ tailWord_6183226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183226).length < 2 ^ (prefixWord ++ tailWord_6183226).sum := by decide
  have hdescent : baseEnd_6183226 < baseStart_6183226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183246 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_6183246 : Nat := 118140960795 + 6183246 * 2 ^ 59
def prefixEnd_6183246 : Nat := 4983230072969 + 3 ^ 40 * 6183246 * 2
def baseEnd_6183246 : Nat := 3174977202990420255288775

theorem tailTrace_6183246 : CollatzResearch.WordTrace tailWord_6183246 prefixEnd_6183246 3174977202990420255288775 := by
  unfold tailWord_6183246
  simp only [CollatzResearch.WordTrace]
  refine ⟨28190188619645403898539199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150347672638108820792209061 28190188619645403898539199)
  ·
    refine ⟨42285282929468105847808799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28190188619645403898539199 42285282929468105847808799)
    ·
      refine ⟨63427924394202158771713199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42285282929468105847808799 63427924394202158771713199)
      ·
        refine ⟨95141886591303238157569799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63427924394202158771713199 95141886591303238157569799)
        ·
          refine ⟨142712829886954857236354699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95141886591303238157569799 142712829886954857236354699)
          ·
            refine ⟨214069244830432285854532049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142712829886954857236354699 214069244830432285854532049)
            ·
              refine ⟨160551933622824214390899037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214069244830432285854532049 160551933622824214390899037)
              ·
                refine ⟨60206975108559080396587139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160551933622824214390899037 60206975108559080396587139)
                ·
                  refine ⟨90310462662838620594880709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60206975108559080396587139 90310462662838620594880709)
                  ·
                    refine ⟨16933211749282241361540133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90310462662838620594880709 16933211749282241361540133)
                    ·
                      refine ⟨3174977202990420255288775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16933211749282241361540133 3174977202990420255288775)
                      ·
                        rfl

theorem cell23_6183246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_6183246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183246 prefixEnd_6183246 := by exact prefixLift 6183246
  have htrace : WordTrace (prefixWord ++ tailWord_6183246) baseStart_6183246 baseEnd_6183246 := by
    simpa [prefixWord, tailWord_6183246, baseEnd_6183246] using wordTrace_append hprefix tailTrace_6183246
  have hstable : (prefixWord ++ tailWord_6183246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183246).length < 2 ^ (prefixWord ++ tailWord_6183246).sum := by decide
  have hdescent : baseEnd_6183246 < baseStart_6183246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183250 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_6183250 : Nat := 118140960795 + 6183250 * 2 ^ 59
def prefixEnd_6183250 : Nat := 4983230072969 + 3 ^ 40 * 6183250 * 2
def baseEnd_6183250 : Nat := 3174979256913038239638757

theorem tailTrace_6183250 : CollatzResearch.WordTrace tailWord_6183250 prefixEnd_6183250 3174979256913038239638757 := by
  unfold tailWord_6183250
  simp only [CollatzResearch.WordTrace]
  refine ⟨56380413712287184967864801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150347769899432493247639469 56380413712287184967864801)
  ·
    refine ⟨42285310284215388725898601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56380413712287184967864801 42285310284215388725898601)
    ·
      refine ⟨31713982713161541544423951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42285310284215388725898601 31713982713161541544423951)
      ·
        refine ⟨47570974069742312316635927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31713982713161541544423951 47570974069742312316635927)
        ·
          refine ⟨71356461104613468474953891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47570974069742312316635927 71356461104613468474953891)
          ·
            refine ⟨107034691656920202712430837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71356461104613468474953891 107034691656920202712430837)
            ·
              refine ⟨10034502342836269004290391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107034691656920202712430837 10034502342836269004290391)
              ·
                refine ⟨15051753514254403506435587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034502342836269004290391 15051753514254403506435587)
                ·
                  refine ⟨22577630271381605259653381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15051753514254403506435587 22577630271381605259653381)
                  ·
                    refine ⟨4233305675884050986185009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22577630271381605259653381 4233305675884050986185009)
                    ·
                      refine ⟨3174979256913038239638757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233305675884050986185009 3174979256913038239638757)
                      ·
                        rfl

theorem cell23_6183250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_6183250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183250 prefixEnd_6183250 := by exact prefixLift 6183250
  have htrace : WordTrace (prefixWord ++ tailWord_6183250) baseStart_6183250 baseEnd_6183250 := by
    simpa [prefixWord, tailWord_6183250, baseEnd_6183250] using wordTrace_append hprefix tailTrace_6183250
  have hstable : (prefixWord ++ tailWord_6183250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183250).length < 2 ^ (prefixWord ++ tailWord_6183250).sum := by decide
  have hdescent : baseEnd_6183250 < baseStart_6183250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183262 : List Nat := [4, 4, 2, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6183262 : Nat := 118140960795 + 6183262 * 2 ^ 59
def prefixEnd_6183262 : Nat := 4983230072969 + 3 ^ 40 * 6183262 * 2
def baseEnd_6183262 : Nat := 3174985418680892192688703

theorem tailTrace_6183262 : CollatzResearch.WordTrace tailWord_6183262 prefixEnd_6183262 3174985418680892192688703 := by
  unfold tailWord_6183262
  simp only [CollatzResearch.WordTrace]
  refine ⟨28190261565638158240112005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150348061683403510613930693 28190261565638158240112005)
  ·
    refine ⟨5285674043557154670021001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28190261565638158240112005 5285674043557154670021001)
    ·
      refine ⟨3964255532667866002515751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5285674043557154670021001 3964255532667866002515751)
      ·
        refine ⟨5946383299001799003773627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964255532667866002515751 5946383299001799003773627)
        ·
          refine ⟨8919574948502698505660441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946383299001799003773627 8919574948502698505660441)
          ·
            refine ⟨6689681211377023879245331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919574948502698505660441 6689681211377023879245331)
            ·
              refine ⟨10034521817065535818867997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689681211377023879245331 10034521817065535818867997)
              ·
                refine ⟨3762945681399575932075499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10034521817065535818867997 3762945681399575932075499)
                ·
                  refine ⟨5644418522099363898113249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762945681399575932075499 5644418522099363898113249)
                  ·
                    refine ⟨4233313891574522923584937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5644418522099363898113249 4233313891574522923584937)
                    ·
                      refine ⟨3174985418680892192688703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233313891574522923584937 3174985418680892192688703)
                      ·
                        rfl

theorem cell23_6183262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6183262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183262 prefixEnd_6183262 := by exact prefixLift 6183262
  have htrace : WordTrace (prefixWord ++ tailWord_6183262) baseStart_6183262 baseEnd_6183262 := by
    simpa [prefixWord, tailWord_6183262, baseEnd_6183262] using wordTrace_append hprefix tailTrace_6183262
  have hstable : (prefixWord ++ tailWord_6183262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183262).length < 2 ^ (prefixWord ++ tailWord_6183262).sum := by decide
  have hdescent : baseEnd_6183262 < baseStart_6183262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183320 : List Nat := [2, 1, 2, 5, 1, 2, 2, 1, 2, 5]
def baseStart_6183320 : Nat := 118140960795 + 6183320 * 2 ^ 59
def prefixEnd_6183320 : Nat := 4983230072969 + 3 ^ 40 * 6183320 * 2
def baseEnd_6183320 : Nat := 1058338400186284321921145

theorem tailTrace_6183320 : CollatzResearch.WordTrace tailWord_6183320 prefixEnd_6183320 1058338400186284321921145 := by
  unfold tailWord_6183320
  simp only [CollatzResearch.WordTrace]
  refine ⟨112762103979447570913253707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150349471972596761217671609 112762103979447570913253707)
  ·
    refine ⟨169143155969171356369880561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112762103979447570913253707 169143155969171356369880561)
    ·
      refine ⟨126857366976878517277410421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169143155969171356369880561 126857366976878517277410421)
      ·
        refine ⟨11892878154082360994757227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126857366976878517277410421 11892878154082360994757227)
        ·
          refine ⟨17839317231123541492135841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11892878154082360994757227 17839317231123541492135841)
          ·
            refine ⟨13379487923342656119101881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17839317231123541492135841 13379487923342656119101881)
            ·
              refine ⟨10034615942506992089326411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13379487923342656119101881 10034615942506992089326411)
              ·
                refine ⟨15051923913760488133989617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034615942506992089326411 15051923913760488133989617)
                ·
                  refine ⟨11288942935320366100492213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15051923913760488133989617 11288942935320366100492213)
                  ·
                    refine ⟨1058338400186284321921145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11288942935320366100492213 1058338400186284321921145)
                    ·
                      rfl

theorem cell23_6183320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_6183320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183320 prefixEnd_6183320 := by exact prefixLift 6183320
  have htrace : WordTrace (prefixWord ++ tailWord_6183320) baseStart_6183320 baseEnd_6183320 := by
    simpa [prefixWord, tailWord_6183320, baseEnd_6183320] using wordTrace_append hprefix tailTrace_6183320
  have hstable : (prefixWord ++ tailWord_6183320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183320).length < 2 ^ (prefixWord ++ tailWord_6183320).sum := by decide
  have hdescent : baseEnd_6183320 < baseStart_6183320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183341 : List Nat := [1, 5, 2, 2, 3, 1, 2, 2, 5]
def baseStart_6183341 : Nat := 118140960795 + 6183341 * 2 ^ 59
def prefixEnd_6183341 : Nat := 4983230072969 + 3 ^ 40 * 6183341 * 2
def baseEnd_6183341 : Nat := 352780664850288598177871

theorem tailTrace_6183341 : CollatzResearch.WordTrace tailWord_6183341 prefixEnd_6183341 352780664850288598177871 := by
  unfold tailWord_6183341
  simp only [CollatzResearch.WordTrace]
  refine ⟨225524973891819062413021877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150349982594546041608681251 225524973891819062413021877)
  ·
    refine ⟨21142966302358037101220801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 225524973891819062413021877 21142966302358037101220801)
    ·
      refine ⟨15857224726768527825915601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21142966302358037101220801 15857224726768527825915601)
      ·
        refine ⟨11892918545076395869436701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15857224726768527825915601 11892918545076395869436701)
        ·
          refine ⟨4459844454403648451038763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11892918545076395869436701 4459844454403648451038763)
          ·
            refine ⟨6689766681605472676558145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459844454403648451038763 6689766681605472676558145)
            ·
              refine ⟨5017325011204104507418609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689766681605472676558145 5017325011204104507418609)
              ·
                refine ⟨3762993758403078380563957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5017325011204104507418609 3762993758403078380563957)
                ·
                  refine ⟨352780664850288598177871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3762993758403078380563957 352780664850288598177871)
                  ·
                    rfl

theorem cell23_6183341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_6183341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183341 prefixEnd_6183341 := by exact prefixLift 6183341
  have htrace : WordTrace (prefixWord ++ tailWord_6183341) baseStart_6183341 baseEnd_6183341 := by
    simpa [prefixWord, tailWord_6183341, baseEnd_6183341] using wordTrace_append hprefix tailTrace_6183341
  have hstable : (prefixWord ++ tailWord_6183341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183341).length < 2 ^ (prefixWord ++ tailWord_6183341).sum := by decide
  have hdescent : baseEnd_6183341 < baseStart_6183341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183397 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 6]
def baseStart_6183397 : Nat := 118140960795 + 6183397 * 2 ^ 59
def prefixEnd_6183397 : Nat := 4983230072969 + 3 ^ 40 * 6183397 * 2
def baseEnd_6183397 : Nat := 352783859841027684944509

theorem tailTrace_6183397 : CollatzResearch.WordTrace tailWord_6183397 prefixEnd_6183397 352783859841027684944509 := by
  unfold tailWord_6183397
  simp only [CollatzResearch.WordTrace]
  refine ⟨225527016379616183977060445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150351344253077455984706963 225527016379616183977060445)
  ·
    refine ⟨84572631142356068991397667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225527016379616183977060445 84572631142356068991397667)
    ·
      refine ⟨126858946713534103487096501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84572631142356068991397667 126858946713534103487096501)
      ·
        refine ⟨11893026254393822201915297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126858946713534103487096501 11893026254393822201915297)
        ·
          refine ⟨8919769690795366651436473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11893026254393822201915297 8919769690795366651436473)
          ·
            refine ⟨6689827268096524988577355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919769690795366651436473 6689827268096524988577355)
            ·
              refine ⟨10034740902144787482866033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689827268096524988577355 10034740902144787482866033)
              ·
                refine ⟨7526055676608590612149525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10034740902144787482866033 7526055676608590612149525)
                ·
                  refine ⟨352783859841027684944509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7526055676608590612149525 352783859841027684944509)
                  ·
                    rfl

theorem cell23_6183397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_6183397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183397 prefixEnd_6183397 := by exact prefixLift 6183397
  have htrace : WordTrace (prefixWord ++ tailWord_6183397) baseStart_6183397 baseEnd_6183397 := by
    simpa [prefixWord, tailWord_6183397, baseEnd_6183397] using wordTrace_append hprefix tailTrace_6183397
  have hstable : (prefixWord ++ tailWord_6183397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183397).length < 2 ^ (prefixWord ++ tailWord_6183397).sum := by decide
  have hdescent : baseEnd_6183397 < baseStart_6183397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183443 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4]
def baseStart_6183443 : Nat := 118140960795 + 6183443 * 2 ^ 59
def prefixEnd_6183443 : Nat := 4983230072969 + 3 ^ 40 * 6183443 * 2
def baseEnd_6183443 : Nat := 3175078358679355984525369

theorem tailTrace_6183443 : CollatzResearch.WordTrace tailWord_6183443 prefixEnd_6183443 3175078358679355984525369 := by
  unfold tailWord_6183443
  simp only [CollatzResearch.WordTrace]
  refine ⟨225528694137449533833234983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150352462758299689222156655 225528694137449533833234983)
  ·
    refine ⟨338293041206174300749852475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225528694137449533833234983 338293041206174300749852475)
    ·
      refine ⟨507439561809261451124778713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338293041206174300749852475 507439561809261451124778713)
      ·
        refine ⟨380579671356946088343584035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507439561809261451124778713 380579671356946088343584035)
        ·
          refine ⟨570869507035419132515376053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380579671356946088343584035 570869507035419132515376053)
          ·
            refine ⟨53519016284570543673316505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 570869507035419132515376053 53519016284570543673316505)
            ·
              refine ⟨40139262213427907754987379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53519016284570543673316505 40139262213427907754987379)
              ·
                refine ⟨60208893320141861632481069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40139262213427907754987379 60208893320141861632481069)
                ·
                  refine ⟨22578334995053198112180401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60208893320141861632481069 22578334995053198112180401)
                  ·
                    refine ⟨16933751246289898584135301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22578334995053198112180401 16933751246289898584135301)
                    ·
                      refine ⟨3175078358679355984525369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16933751246289898584135301 3175078358679355984525369)
                      ·
                        rfl

theorem cell23_6183443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_6183443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183443 prefixEnd_6183443 := by exact prefixLift 6183443
  have htrace : WordTrace (prefixWord ++ tailWord_6183443) baseStart_6183443 baseEnd_6183443 := by
    simpa [prefixWord, tailWord_6183443, baseEnd_6183443] using wordTrace_append hprefix tailTrace_6183443
  have hstable : (prefixWord ++ tailWord_6183443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183443).length < 2 ^ (prefixWord ++ tailWord_6183443).sum := by decide
  have hdescent : baseEnd_6183443 < baseStart_6183443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183453 : List Nat := [1, 4, 2, 2, 1, 2, 11]
def baseStart_6183453 : Nat := 118140960795 + 6183453 * 2 ^ 59
def prefixEnd_6183453 : Nat := 4983230072969 + 3 ^ 40 * 6183453 * 2
def baseEnd_6183453 : Nat := 39198561647974085745683

theorem tailTrace_6183453 : CollatzResearch.WordTrace tailWord_6183453 prefixEnd_6183453 39198561647974085745683 := by
  unfold tailWord_6183453
  simp only [CollatzResearch.WordTrace]
  refine ⟨225529058867413305541099013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150352705911608870360732675 225529058867413305541099013)
  ·
    refine ⟨42286698537639994788956065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225529058867413305541099013 42286698537639994788956065)
    ·
      refine ⟨31715023903229996091717049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42286698537639994788956065 31715023903229996091717049)
      ·
        refine ⟨23786267927422497068787787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31715023903229996091717049 23786267927422497068787787)
        ·
          refine ⟨35679401891133745603181681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23786267927422497068787787 35679401891133745603181681)
          ·
            refine ⟨26759551418350309202386261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35679401891133745603181681 26759551418350309202386261)
            ·
              refine ⟨39198561647974085745683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26759551418350309202386261 39198561647974085745683)
              ·
                rfl

theorem cell23_6183453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 11].length) (baseStart_6183453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183453 prefixEnd_6183453 := by exact prefixLift 6183453
  have htrace : WordTrace (prefixWord ++ tailWord_6183453) baseStart_6183453 baseEnd_6183453 := by
    simpa [prefixWord, tailWord_6183453, baseEnd_6183453] using wordTrace_append hprefix tailTrace_6183453
  have hstable : (prefixWord ++ tailWord_6183453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183453).length < 2 ^ (prefixWord ++ tailWord_6183453).sum := by decide
  have hdescent : baseEnd_6183453 < baseStart_6183453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183480 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 1, 3, 3]
def baseStart_6183480 : Nat := 118140960795 + 6183480 * 2 ^ 59
def prefixEnd_6183480 : Nat := 4983230072969 + 3 ^ 40 * 6183480 * 2
def baseEnd_6183480 : Nat := 3175097357463572339762699

theorem tailTrace_6183480 : CollatzResearch.WordTrace tailWord_6183480 prefixEnd_6183480 3175097357463572339762699 := by
  unfold tailWord_6183480
  simp only [CollatzResearch.WordTrace]
  refine ⟨112765021819157744576165947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150353362425543659434887929 112765021819157744576165947)
  ·
    refine ⟨169147532728736616864248921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112765021819157744576165947 169147532728736616864248921)
    ·
      refine ⟨126860649546552462648186691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169147532728736616864248921 126860649546552462648186691)
      ·
        refine ⟨190290974319828693972280037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126860649546552462648186691 190290974319828693972280037)
        ·
          refine ⟨35679557684967880119802507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190290974319828693972280037 35679557684967880119802507)
          ·
            refine ⟨53519336527451820179703761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35679557684967880119802507 53519336527451820179703761)
            ·
              refine ⟨40139502395588865134777821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53519336527451820179703761 40139502395588865134777821)
              ·
                refine ⟨15052313398345824425541683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40139502395588865134777821 15052313398345824425541683)
                ·
                  refine ⟨22578470097518736638312525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15052313398345824425541683 22578470097518736638312525)
                  ·
                    refine ⟨8466926286569526239367197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22578470097518736638312525 8466926286569526239367197)
                    ·
                      refine ⟨3175097357463572339762699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8466926286569526239367197 3175097357463572339762699)
                      ·
                        rfl

theorem cell23_6183480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_6183480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183480 prefixEnd_6183480 := by exact prefixLift 6183480
  have htrace : WordTrace (prefixWord ++ tailWord_6183480) baseStart_6183480 baseEnd_6183480 := by
    simpa [prefixWord, tailWord_6183480, baseEnd_6183480] using wordTrace_append hprefix tailTrace_6183480
  have hstable : (prefixWord ++ tailWord_6183480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183480).length < 2 ^ (prefixWord ++ tailWord_6183480).sum := by decide
  have hdescent : baseEnd_6183480 < baseStart_6183480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183484 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 1, 2, 3]
def baseStart_6183484 : Nat := 118140960795 + 6183484 * 2 ^ 59
def prefixEnd_6183484 : Nat := 4983230072969 + 3 ^ 40 * 6183484 * 2
def baseEnd_6183484 : Nat := 3175099411386190324112681

theorem tailTrace_6183484 : CollatzResearch.WordTrace tailWord_6183484 prefixEnd_6183484 3175099411386190324112681 := by
  unfold tailWord_6183484
  simp only [CollatzResearch.WordTrace]
  refine ⟨112765094765150498917738753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150353459686867331890318337 112765094765150498917738753)
  ·
    refine ⟨84573821073862874188304065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112765094765150498917738753 84573821073862874188304065)
    ·
      refine ⟨63430365805397155641228049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84573821073862874188304065 63430365805397155641228049)
      ·
        refine ⟨47572774354047866730921037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63430365805397155641228049 47572774354047866730921037)
        ·
          refine ⟨17839790382767950024095389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47572774354047866730921037 17839790382767950024095389)
          ·
            refine ⟨6689921393537981259035771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17839790382767950024095389 6689921393537981259035771)
            ·
              refine ⟨10034882090306971888553657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689921393537981259035771 10034882090306971888553657)
              ·
                refine ⟨7526161567730228916415243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10034882090306971888553657 7526161567730228916415243)
                ·
                  refine ⟨11289242351595343374622865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526161567730228916415243 11289242351595343374622865)
                  ·
                    refine ⟨8466931763696507530967149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11289242351595343374622865 8466931763696507530967149)
                    ·
                      refine ⟨3175099411386190324112681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8466931763696507530967149 3175099411386190324112681)
                      ·
                        rfl

theorem cell23_6183484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_6183484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183484 prefixEnd_6183484 := by exact prefixLift 6183484
  have htrace : WordTrace (prefixWord ++ tailWord_6183484) baseStart_6183484 baseEnd_6183484 := by
    simpa [prefixWord, tailWord_6183484, baseEnd_6183484] using wordTrace_append hprefix tailTrace_6183484
  have hstable : (prefixWord ++ tailWord_6183484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183484).length < 2 ^ (prefixWord ++ tailWord_6183484).sum := by decide
  have hdescent : baseEnd_6183484 < baseStart_6183484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183494 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6183494 : Nat := 118140960795 + 6183494 * 2 ^ 59
def prefixEnd_6183494 : Nat := 4983230072969 + 3 ^ 40 * 6183494 * 2
def baseEnd_6183494 : Nat := 3175104546192735284987635

theorem tailTrace_6183494 : CollatzResearch.WordTrace tailWord_6183494 prefixEnd_6183494 3175104546192735284987635 := by
  unfold tailWord_6183494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047829820633274048229423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150353702840176513028894357 7047829820633274048229423)
  ·
    refine ⟨10571744730949911072344135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7047829820633274048229423 10571744730949911072344135)
    ·
      refine ⟨15857617096424866608516203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10571744730949911072344135 15857617096424866608516203)
      ·
        refine ⟨23786425644637299912774305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15857617096424866608516203 23786425644637299912774305)
        ·
          refine ⟨17839819233477974934580729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23786425644637299912774305 17839819233477974934580729)
          ·
            refine ⟨13379864425108481200935547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17839819233477974934580729 13379864425108481200935547)
            ·
              refine ⟨20069796637662721801403321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13379864425108481200935547 20069796637662721801403321)
              ·
                refine ⟨15052347478247041351052491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20069796637662721801403321 15052347478247041351052491)
                ·
                  refine ⟨22578521217370562026578737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15052347478247041351052491 22578521217370562026578737)
                  ·
                    refine ⟨16933890913027921519934053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22578521217370562026578737 16933890913027921519934053)
                    ·
                      refine ⟨3175104546192735284987635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16933890913027921519934053 3175104546192735284987635)
                      ·
                        rfl

theorem cell23_6183494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6183494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183494 prefixEnd_6183494 := by exact prefixLift 6183494
  have htrace : WordTrace (prefixWord ++ tailWord_6183494) baseStart_6183494 baseEnd_6183494 := by
    simpa [prefixWord, tailWord_6183494, baseEnd_6183494] using wordTrace_append hprefix tailTrace_6183494
  have hstable : (prefixWord ++ tailWord_6183494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183494).length < 2 ^ (prefixWord ++ tailWord_6183494).sum := by decide
  have hdescent : baseEnd_6183494 < baseStart_6183494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183501 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 1, 2, 3]
def baseStart_6183501 : Nat := 118140960795 + 6183501 * 2 ^ 59
def prefixEnd_6183501 : Nat := 4983230072969 + 3 ^ 40 * 6183501 * 2
def baseEnd_6183501 : Nat := 3175108140557316757600103

theorem tailTrace_6183501 : CollatzResearch.WordTrace tailWord_6183501 prefixEnd_6183501 3175108140557316757600103 := by
  unfold tailWord_6183501
  simp only [CollatzResearch.WordTrace]
  refine ⟨225530809571239409738846357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150353873047492939825897571 225530809571239409738846357)
  ·
    refine ⟨10571756698651847331508423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 225530809571239409738846357 10571756698651847331508423)
    ·
      refine ⟨15857635047977770997262635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10571756698651847331508423 15857635047977770997262635)
      ·
        refine ⟨23786452571966656495893953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15857635047977770997262635 23786452571966656495893953)
        ·
          refine ⟨17839839428974992371920465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23786452571966656495893953 17839839428974992371920465)
          ·
            refine ⟨13379879571731244278940349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17839839428974992371920465 13379879571731244278940349)
            ·
              refine ⟨5017454839399216604602631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13379879571731244278940349 5017454839399216604602631)
              ·
                refine ⟨7526182259098824906903947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017454839399216604602631 7526182259098824906903947)
                ·
                  refine ⟨11289273388648237360355921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526182259098824906903947 11289273388648237360355921)
                  ·
                    refine ⟨8466955041486178020266941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11289273388648237360355921 8466955041486178020266941)
                    ·
                      refine ⟨3175108140557316757600103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8466955041486178020266941 3175108140557316757600103)
                      ·
                        rfl

theorem cell23_6183501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_6183501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183501 prefixEnd_6183501 := by exact prefixLift 6183501
  have htrace : WordTrace (prefixWord ++ tailWord_6183501) baseStart_6183501 baseEnd_6183501 := by
    simpa [prefixWord, tailWord_6183501, baseEnd_6183501] using wordTrace_append hprefix tailTrace_6183501
  have hstable : (prefixWord ++ tailWord_6183501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183501).length < 2 ^ (prefixWord ++ tailWord_6183501).sum := by decide
  have hdescent : baseEnd_6183501 < baseStart_6183501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183530 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_6183530 : Nat := 118140960795 + 6183530 * 2 ^ 59
def prefixEnd_6183530 : Nat := 4983230072969 + 3 ^ 40 * 6183530 * 2
def baseEnd_6183530 : Nat := 1058374343832099048045823

theorem tailTrace_6183530 : CollatzResearch.WordTrace tailWord_6183530 prefixEnd_6183530 1058374343832099048045823 := by
  unfold tailWord_6183530
  simp only [CollatzResearch.WordTrace]
  refine ⟨56382966822033586922913011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150354578192089565127768029 56382966822033586922913011)
  ·
    refine ⟨84574450233050380384369517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56382966822033586922913011 84574450233050380384369517)
    ·
      refine ⟨31715418837393892644138569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84574450233050380384369517 31715418837393892644138569)
      ·
        refine ⟨23786564128045419483103927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31715418837393892644138569 23786564128045419483103927)
        ·
          refine ⟨35679846192068129224655891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23786564128045419483103927 35679846192068129224655891)
          ·
            refine ⟨53519769288102193836983837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35679846192068129224655891 53519769288102193836983837)
            ·
              refine ⟨20069913483038322688868939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53519769288102193836983837 20069913483038322688868939)
              ·
                refine ⟨30104870224557484033303409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20069913483038322688868939 30104870224557484033303409)
                ·
                  refine ⟨22578652668418113024977557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30104870224557484033303409 22578652668418113024977557)
                  ·
                    refine ⟨1058374343832099048045823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22578652668418113024977557 1058374343832099048045823)
                    ·
                      rfl

theorem cell23_6183530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_6183530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183530 prefixEnd_6183530 := by exact prefixLift 6183530
  have htrace : WordTrace (prefixWord ++ tailWord_6183530) baseStart_6183530 baseEnd_6183530 := by
    simpa [prefixWord, tailWord_6183530, baseEnd_6183530] using wordTrace_append hprefix tailTrace_6183530
  have hstable : (prefixWord ++ tailWord_6183530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183530).length < 2 ^ (prefixWord ++ tailWord_6183530).sum := by decide
  have hdescent : baseEnd_6183530 < baseStart_6183530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183537 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 8, 2, 2]
def baseStart_6183537 : Nat := 118140960795 + 6183537 * 2 ^ 59
def prefixEnd_6183537 : Nat := 4983230072969 + 3 ^ 40 * 6183537 * 2
def baseEnd_6183537 : Nat := 3175126625860878616749937

theorem tailTrace_6183537 : CollatzResearch.WordTrace tailWord_6183537 prefixEnd_6183537 3175126625860878616749937 := by
  unfold tailWord_6183537
  simp only [CollatzResearch.WordTrace]
  refine ⟨225532122599108987887156865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150354748399405991924771243 225532122599108987887156865)
  ·
    refine ⟨169149091949331740915367649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225532122599108987887156865 169149091949331740915367649)
    ·
      refine ⟨126861818961998805686525737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169149091949331740915367649 126861818961998805686525737)
      ·
        refine ⟨95146364221499104264894303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126861818961998805686525737 95146364221499104264894303)
        ·
          refine ⟨142719546332248656397341455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95146364221499104264894303 142719546332248656397341455)
          ·
            refine ⟨214079319498372984596012183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142719546332248656397341455 214079319498372984596012183)
            ·
              refine ⟨321118979247559476894018275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214079319498372984596012183 321118979247559476894018275)
              ·
                refine ⟨481678468871339215341027413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321118979247559476894018275 481678468871339215341027413)
                ·
                  refine ⟨5644669557086006429777665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 481678468871339215341027413 5644669557086006429777665)
                  ·
                    refine ⟨4233502167814504822333249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5644669557086006429777665 4233502167814504822333249)
                    ·
                      refine ⟨3175126625860878616749937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233502167814504822333249 3175126625860878616749937)
                      ·
                        rfl

theorem cell23_6183537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_6183537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183537 prefixEnd_6183537 := by exact prefixLift 6183537
  have htrace : WordTrace (prefixWord ++ tailWord_6183537) baseStart_6183537 baseEnd_6183537 := by
    simpa [prefixWord, tailWord_6183537, baseEnd_6183537] using wordTrace_append hprefix tailTrace_6183537
  have hstable : (prefixWord ++ tailWord_6183537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183537).length < 2 ^ (prefixWord ++ tailWord_6183537).sum := by decide
  have hdescent : baseEnd_6183537 < baseStart_6183537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183543 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 9]
def baseStart_6183543 : Nat := 118140960795 + 6183543 * 2 ^ 59
def prefixEnd_6183543 : Nat := 4983230072969 + 3 ^ 40 * 6183543 * 2
def baseEnd_6183543 : Nat := 352792189638311732586101

theorem tailTrace_6183543 : CollatzResearch.WordTrace tailWord_6183543 prefixEnd_6183543 352792189638311732586101 := by
  unfold tailWord_6183543
  simp only [CollatzResearch.WordTrace]
  refine ⟨225532341437087250911875283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150354894291391500607916855 225532341437087250911875283)
  ·
    refine ⟨338298512155630876367812925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225532341437087250911875283 338298512155630876367812925)
    ·
      refine ⟨126861942058361578637929847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338298512155630876367812925 126861942058361578637929847)
      ·
        refine ⟨190292913087542367956894771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126861942058361578637929847 190292913087542367956894771)
        ·
          refine ⟨285439369631313551935342157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190292913087542367956894771 285439369631313551935342157)
          ·
            refine ⟨107039763611742581975753309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285439369631313551935342157 107039763611742581975753309)
            ·
              refine ⟨40139911354403468240907491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107039763611742581975753309 40139911354403468240907491)
              ·
                refine ⟨60209867031605202361361237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40139911354403468240907491 60209867031605202361361237)
                ·
                  refine ⟨352792189638311732586101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60209867031605202361361237 352792189638311732586101)
                  ·
                    rfl

theorem cell23_6183543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 9].length) (baseStart_6183543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183543 prefixEnd_6183543 := by exact prefixLift 6183543
  have htrace : WordTrace (prefixWord ++ tailWord_6183543) baseStart_6183543 baseEnd_6183543 := by
    simpa [prefixWord, tailWord_6183543, baseEnd_6183543] using wordTrace_append hprefix tailTrace_6183543
  have hstable : (prefixWord ++ tailWord_6183543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183543).length < 2 ^ (prefixWord ++ tailWord_6183543).sum := by decide
  have hdescent : baseEnd_6183543 < baseStart_6183543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183610 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4]
def baseStart_6183610 : Nat := 118140960795 + 6183610 * 2 ^ 59
def prefixEnd_6183610 : Nat := 4983230072969 + 3 ^ 40 * 6183610 * 2
def baseEnd_6183610 : Nat := 3175164109948656831137101

theorem tailTrace_6183610 : CollatzResearch.WordTrace tailWord_6183610 prefixEnd_6183610 3175164109948656831137101 := by
  unfold tailWord_6183610
  simp only [CollatzResearch.WordTrace]
  refine ⟨56383696281961130338641071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150356523418563014236376189 56383696281961130338641071)
  ·
    refine ⟨84575544422941695507961607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56383696281961130338641071 84575544422941695507961607)
    ·
      refine ⟨126863316634412543261942411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84575544422941695507961607 126863316634412543261942411)
      ·
        refine ⟨190294974951618814892913617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126863316634412543261942411 190294974951618814892913617)
        ·
          refine ⟨142721231213714111169685213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190294974951618814892913617 142721231213714111169685213)
          ·
            refine ⟨53520461705142791688631955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142721231213714111169685213 53520461705142791688631955)
            ·
              refine ⟨80280692557714187532947933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53520461705142791688631955 80280692557714187532947933)
              ·
                refine ⟨30105259709142820324855475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80280692557714187532947933 30105259709142820324855475)
                ·
                  refine ⟨45157889563714230487283213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30105259709142820324855475 45157889563714230487283213)
                  ·
                    refine ⟨16934208586392836432731205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45157889563714230487283213 16934208586392836432731205)
                    ·
                      refine ⟨3175164109948656831137101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16934208586392836432731205 3175164109948656831137101)
                      ·
                        rfl

theorem cell23_6183610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_6183610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183610 prefixEnd_6183610 := by exact prefixLift 6183610
  have htrace : WordTrace (prefixWord ++ tailWord_6183610) baseStart_6183610 baseEnd_6183610 := by
    simpa [prefixWord, tailWord_6183610, baseEnd_6183610] using wordTrace_append hprefix tailTrace_6183610
  have hstable : (prefixWord ++ tailWord_6183610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183610).length < 2 ^ (prefixWord ++ tailWord_6183610).sum := by decide
  have hdescent : baseEnd_6183610 < baseStart_6183610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183680 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 7, 5]
def baseStart_6183680 : Nat := 118140960795 + 6183680 * 2 ^ 59
def prefixEnd_6183680 : Nat := 4983230072969 + 3 ^ 40 * 6183680 * 2
def baseEnd_6183680 : Nat := 1058400017864823852420593

theorem tailTrace_6183680 : CollatzResearch.WordTrace tailWord_6183680 prefixEnd_6183680 1058400017864823852420593 := by
  unfold tailWord_6183680
  simp only [CollatzResearch.WordTrace]
  refine ⟨112768669118795461654806247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150358225491727282206408329 112768669118795461654806247)
  ·
    refine ⟨169153003678193192482209371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112768669118795461654806247 169153003678193192482209371)
    ·
      refine ⟨253729505517289788723314057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169153003678193192482209371 253729505517289788723314057)
      ·
        refine ⟨190297129137967341542485543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253729505517289788723314057 190297129137967341542485543)
        ·
          refine ⟨285445693706951012313728315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190297129137967341542485543 285445693706951012313728315)
          ·
            refine ⟨428168540560426518470592473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285445693706951012313728315 428168540560426518470592473)
            ·
              refine ⟨321126405420319888852944355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428168540560426518470592473 321126405420319888852944355)
              ·
                refine ⟨481689608130479833279416533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321126405420319888852944355 481689608130479833279416533)
                ·
                  refine ⟨11289600190558121092486325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 481689608130479833279416533 11289600190558121092486325)
                  ·
                    refine ⟨1058400017864823852420593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11289600190558121092486325 1058400017864823852420593)
                    ·
                      rfl

theorem cell23_6183680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_6183680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183680 prefixEnd_6183680 := by exact prefixLift 6183680
  have htrace : WordTrace (prefixWord ++ tailWord_6183680) baseStart_6183680 baseEnd_6183680 := by
    simpa [prefixWord, tailWord_6183680, baseEnd_6183680] using wordTrace_append hprefix tailTrace_6183680
  have hstable : (prefixWord ++ tailWord_6183680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183680).length < 2 ^ (prefixWord ++ tailWord_6183680).sum := by decide
  have hdescent : baseEnd_6183680 < baseStart_6183680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183688 : List Nat := [2, 1, 3, 2, 2, 4, 2, 2, 1, 4]
def baseStart_6183688 : Nat := 118140960795 + 6183688 * 2 ^ 59
def prefixEnd_6183688 : Nat := 4983230072969 + 3 ^ 40 * 6183688 * 2
def baseEnd_6183688 : Nat := 1058401387146569175320581

theorem tailTrace_6183688 : CollatzResearch.WordTrace tailWord_6183688 prefixEnd_6183688 1058401387146569175320581 := by
  unfold tailWord_6183688
  simp only [CollatzResearch.WordTrace]
  refine ⟨112768815010780970337951859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150358420014374627117269145 112768815010780970337951859)
  ·
    refine ⟨169153222516171455506927789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112768815010780970337951859 169153222516171455506927789)
    ·
      refine ⟨63432458443564295815097921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169153222516171455506927789 63432458443564295815097921)
      ·
        refine ⟨47574343832673221861323441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63432458443564295815097921 47574343832673221861323441)
        ·
          refine ⟨35680757874504916395992581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47574343832673221861323441 35680757874504916395992581)
          ·
            refine ⟨6690142101469671824248609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35680757874504916395992581 6690142101469671824248609)
            ·
              refine ⟨5017606576102253868186457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6690142101469671824248609 5017606576102253868186457)
              ·
                refine ⟨3763204932076690401139843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5017606576102253868186457 3763204932076690401139843)
                ·
                  refine ⟨5644807398115035601709765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763204932076690401139843 5644807398115035601709765)
                  ·
                    refine ⟨1058401387146569175320581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5644807398115035601709765 1058401387146569175320581)
                    ·
                      rfl

theorem cell23_6183688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_6183688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183688 prefixEnd_6183688 := by exact prefixLift 6183688
  have htrace : WordTrace (prefixWord ++ tailWord_6183688) baseStart_6183688 baseEnd_6183688 := by
    simpa [prefixWord, tailWord_6183688, baseEnd_6183688] using wordTrace_append hprefix tailTrace_6183688
  have hstable : (prefixWord ++ tailWord_6183688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183688).length < 2 ^ (prefixWord ++ tailWord_6183688).sum := by decide
  have hdescent : baseEnd_6183688 < baseStart_6183688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183694 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_6183694 : Nat := 118140960795 + 6183694 * 2 ^ 59
def prefixEnd_6183694 : Nat := 4983230072969 + 3 ^ 40 * 6183694 * 2
def baseEnd_6183694 : Nat := 3175207242323634502486715

theorem tailTrace_6183694 : CollatzResearch.WordTrace tailWord_6183694 prefixEnd_6183694 3175207242323634502486715 := by
  unfold tailWord_6183694
  simp only [CollatzResearch.WordTrace]
  refine ⟨28192231107442525462577767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150358565906360135800414757 28192231107442525462577767)
  ·
    refine ⟨42288346661163788193866651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28192231107442525462577767 42288346661163788193866651)
    ·
      refine ⟨63432519991745682290799977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42288346661163788193866651 63432519991745682290799977)
      ·
        refine ⟨47574389993809261718099983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63432519991745682290799977 47574389993809261718099983)
        ·
          refine ⟨71361584990713892577149975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47574389993809261718099983 71361584990713892577149975)
          ·
            refine ⟨107042377486070838865724963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71361584990713892577149975 107042377486070838865724963)
            ·
              refine ⟨160563566229106258298587445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107042377486070838865724963 160563566229106258298587445)
              ·
                refine ⟨15052834333978711715492573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160563566229106258298587445 15052834333978711715492573)
                ·
                  refine ⟨5644812875242016893309715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15052834333978711715492573 5644812875242016893309715)
                  ·
                    refine ⟨8467219312863025339964573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5644812875242016893309715 8467219312863025339964573)
                    ·
                      refine ⟨3175207242323634502486715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8467219312863025339964573 3175207242323634502486715)
                      ·
                        rfl

theorem cell23_6183694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_6183694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183694 prefixEnd_6183694 := by exact prefixLift 6183694
  have htrace : WordTrace (prefixWord ++ tailWord_6183694) baseStart_6183694 baseEnd_6183694 := by
    simpa [prefixWord, tailWord_6183694, baseEnd_6183694] using wordTrace_append hprefix tailTrace_6183694
  have hstable : (prefixWord ++ tailWord_6183694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183694).length < 2 ^ (prefixWord ++ tailWord_6183694).sum := by decide
  have hdescent : baseEnd_6183694 < baseStart_6183694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183717 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 4]
def baseStart_6183717 : Nat := 118140960795 + 6183717 * 2 ^ 59
def prefixEnd_6183717 : Nat := 4983230072969 + 3 ^ 40 * 6183717 * 2
def baseEnd_6183717 : Nat := 3175219052378687912499109

theorem tailTrace_6183717 : CollatzResearch.WordTrace tailWord_6183717 prefixEnd_6183717 3175219052378687912499109 := by
  unfold tailWord_6183717
  simp only [CollatzResearch.WordTrace]
  refine ⟨225538687738456878628709405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150359125158971252419139603 225538687738456878628709405)
  ·
    refine ⟨84577007901921329485766027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225538687738456878628709405 84577007901921329485766027)
    ·
      refine ⟨126865511852881994228649041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84577007901921329485766027 126865511852881994228649041)
      ·
        refine ⟨95149133889661495671486781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126865511852881994228649041 95149133889661495671486781)
        ·
          refine ⟨35680925208623060876807543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95149133889661495671486781 35680925208623060876807543)
          ·
            refine ⟨53521387812934591315211315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35680925208623060876807543 53521387812934591315211315)
            ·
              refine ⟨80282081719401886972816973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53521387812934591315211315 80282081719401886972816973)
              ·
                refine ⟨30105780644775707614806365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80282081719401886972816973 30105780644775707614806365)
                ·
                  refine ⟨11289667741790890355552387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30105780644775707614806365 11289667741790890355552387)
                  ·
                    refine ⟨16934501612686335533328581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11289667741790890355552387 16934501612686335533328581)
                    ·
                      refine ⟨3175219052378687912499109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16934501612686335533328581 3175219052378687912499109)
                      ·
                        rfl

theorem cell23_6183717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_6183717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183717 prefixEnd_6183717 := by exact prefixLift 6183717
  have htrace : WordTrace (prefixWord ++ tailWord_6183717) baseStart_6183717 baseEnd_6183717 := by
    simpa [prefixWord, tailWord_6183717, baseEnd_6183717] using wordTrace_append hprefix tailTrace_6183717
  have hstable : (prefixWord ++ tailWord_6183717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183717).length < 2 ^ (prefixWord ++ tailWord_6183717).sum := by decide
  have hdescent : baseEnd_6183717 < baseStart_6183717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183731 : List Nat := [1, 1, 1, 2, 6, 3, 2, 1, 1, 5]
def baseStart_6183731 : Nat := 118140960795 + 6183731 * 2 ^ 59
def prefixEnd_6183731 : Nat := 4983230072969 + 3 ^ 40 * 6183731 * 2
def baseEnd_6183731 : Nat := 1058408747035950285908015

theorem tailTrace_6183731 : CollatzResearch.WordTrace tailWord_6183731 prefixEnd_6183731 1058408747035950285908015 := by
  unfold tailWord_6183731
  simp only [CollatzResearch.WordTrace]
  refine ⟨225539198360406159019719047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150359465573604106013146031 225539198360406159019719047)
  ·
    refine ⟨338308797540609238529578571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225539198360406159019719047 338308797540609238529578571)
    ·
      refine ⟨507463196310913857794367857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338308797540609238529578571 507463196310913857794367857)
      ·
        refine ⟨380597397233185393345775893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507463196310913857794367857 380597397233185393345775893)
        ·
          refine ⟨17840502995305565313083245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 380597397233185393345775893 17840502995305565313083245)
          ·
            refine ⟨6690188623239586992406217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17840502995305565313083245 6690188623239586992406217)
            ·
              refine ⟨5017641467429690244304663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6690188623239586992406217 5017641467429690244304663)
              ·
                refine ⟨7526462201144535366456995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017641467429690244304663 7526462201144535366456995)
                ·
                  refine ⟨11289693301716803049685493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526462201144535366456995 11289693301716803049685493)
                  ·
                    refine ⟨1058408747035950285908015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11289693301716803049685493 1058408747035950285908015)
                    ·
                      rfl

theorem cell23_6183731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 1, 5].length) (baseStart_6183731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183731 prefixEnd_6183731 := by exact prefixLift 6183731
  have htrace : WordTrace (prefixWord ++ tailWord_6183731) baseStart_6183731 baseEnd_6183731 := by
    simpa [prefixWord, tailWord_6183731, baseEnd_6183731] using wordTrace_append hprefix tailTrace_6183731
  have hstable : (prefixWord ++ tailWord_6183731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183731).length < 2 ^ (prefixWord ++ tailWord_6183731).sum := by decide
  have hdescent : baseEnd_6183731 < baseStart_6183731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183761 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 1, 6]
def baseStart_6183761 : Nat := 118140960795 + 6183761 * 2 ^ 59
def prefixEnd_6183761 : Nat := 4983230072969 + 3 ^ 40 * 6183761 * 2
def baseEnd_6183761 : Nat := 1058413881842495246782969

theorem tailTrace_6183761 : CollatzResearch.WordTrace tailWord_6183761 prefixEnd_6183761 1058413881842495246782969 := by
  unfold tailWord_6183761
  simp only [CollatzResearch.WordTrace]
  refine ⟨225540292550297474143311137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150360195033531649428874091 225540292550297474143311137)
  ·
    refine ⟨169155219412723105607483353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225540292550297474143311137 169155219412723105607483353)
    ·
      refine ⟨126866414559542329205612515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169155219412723105607483353 126866414559542329205612515)
      ·
        refine ⟨190299621839313493808418773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126866414559542329205612515 190299621839313493808418773)
        ·
          refine ⟨4460147386858910011134815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 190299621839313493808418773 4460147386858910011134815)
          ·
            refine ⟨6690221080288365016702223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460147386858910011134815 6690221080288365016702223)
            ·
              refine ⟨10035331620432547525053335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690221080288365016702223 10035331620432547525053335)
              ·
                refine ⟨15052997430648821287580003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10035331620432547525053335 15052997430648821287580003)
                ·
                  refine ⟨22579496145973231931370005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15052997430648821287580003 22579496145973231931370005)
                  ·
                    refine ⟨1058413881842495246782969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22579496145973231931370005 1058413881842495246782969)
                    ·
                      rfl

theorem cell23_6183761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_6183761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183761 prefixEnd_6183761 := by exact prefixLift 6183761
  have htrace : WordTrace (prefixWord ++ tailWord_6183761) baseStart_6183761 baseEnd_6183761 := by
    simpa [prefixWord, tailWord_6183761, baseEnd_6183761] using wordTrace_append hprefix tailTrace_6183761
  have hstable : (prefixWord ++ tailWord_6183761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183761).length < 2 ^ (prefixWord ++ tailWord_6183761).sum := by decide
  have hdescent : baseEnd_6183761 < baseStart_6183761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183764 : List Nat := [2, 4, 1, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_6183764 : Nat := 118140960795 + 6183764 * 2 ^ 59
def prefixEnd_6183764 : Nat := 4983230072969 + 3 ^ 40 * 6183764 * 2
def baseEnd_6183764 : Nat := 3175243185969449228611393

theorem tailTrace_6183764 : CollatzResearch.WordTrace tailWord_6183764 prefixEnd_6183764 3175243185969449228611393 := by
  unfold tailWord_6183764
  simp only [CollatzResearch.WordTrace]
  refine ⟨112770200984643302827835173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150360267979524403770446897 112770200984643302827835173)
  ·
    refine ⟨21144412684620619280219095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112770200984643302827835173 21144412684620619280219095)
    ·
      refine ⟨31716619026930928920328643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21144412684620619280219095 31716619026930928920328643)
      ·
        refine ⟨47574928540396393380492965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31716619026930928920328643 47574928540396393380492965)
        ·
          refine ⟨8920299101324323758842431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47574928540396393380492965 8920299101324323758842431)
          ·
            refine ⟨13380448651986485638263647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8920299101324323758842431 13380448651986485638263647)
            ·
              refine ⟨20070672977979728457395471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13380448651986485638263647 20070672977979728457395471)
              ·
                refine ⟨30106009466969592686093207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20070672977979728457395471 30106009466969592686093207)
                ·
                  refine ⟨45159014200454389029139811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30106009466969592686093207 45159014200454389029139811)
                  ·
                    refine ⟨67738521300681583543709717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45159014200454389029139811 67738521300681583543709717)
                    ·
                      refine ⟨3175243185969449228611393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67738521300681583543709717 3175243185969449228611393)
                      ·
                        rfl

theorem cell23_6183764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_6183764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183764 prefixEnd_6183764 := by exact prefixLift 6183764
  have htrace : WordTrace (prefixWord ++ tailWord_6183764) baseStart_6183764 baseEnd_6183764 := by
    simpa [prefixWord, tailWord_6183764, baseEnd_6183764] using wordTrace_append hprefix tailTrace_6183764
  have hstable : (prefixWord ++ tailWord_6183764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183764).length < 2 ^ (prefixWord ++ tailWord_6183764).sum := by decide
  have hdescent : baseEnd_6183764 < baseStart_6183764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183818 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6183818 : Nat := 118140960795 + 6183818 * 2 ^ 59
def prefixEnd_6183818 : Nat := 4983230072969 + 3 ^ 40 * 6183818 * 2
def baseEnd_6183818 : Nat := 3175270913924792017336145

theorem tailTrace_6183818 : CollatzResearch.WordTrace tailWord_6183818 prefixEnd_6183818 3175270913924792017336145 := by
  unfold tailWord_6183818
  simp only [CollatzResearch.WordTrace]
  refine ⟨56385592877772743219534027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150361581007393981918757405 56385592877772743219534027)
  ·
    refine ⟨84578389316659114829301041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56385592877772743219534027 84578389316659114829301041)
    ·
      refine ⟨63433791987494336121975781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84578389316659114829301041 63433791987494336121975781)
      ·
        refine ⟨11893835997655188022870459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63433791987494336121975781 11893835997655188022870459)
        ·
          refine ⟨17840753996482782034305689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11893835997655188022870459 17840753996482782034305689)
          ·
            refine ⟨13380565497362086525729267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17840753996482782034305689 13380565497362086525729267)
            ·
              refine ⟨20070848246043129788593901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13380565497362086525729267 20070848246043129788593901)
              ·
                refine ⟨7526568092266173670722713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20070848246043129788593901 7526568092266173670722713)
                ·
                  refine ⟨5644926069199630253042035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7526568092266173670722713 5644926069199630253042035)
                  ·
                    refine ⟨8467389103799445379563053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5644926069199630253042035 8467389103799445379563053)
                    ·
                      refine ⟨3175270913924792017336145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8467389103799445379563053 3175270913924792017336145)
                      ·
                        rfl

theorem cell23_6183818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6183818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183818 prefixEnd_6183818 := by exact prefixLift 6183818
  have htrace : WordTrace (prefixWord ++ tailWord_6183818) baseStart_6183818 baseEnd_6183818 := by
    simpa [prefixWord, tailWord_6183818, baseEnd_6183818] using wordTrace_append hprefix tailTrace_6183818
  have hstable : (prefixWord ++ tailWord_6183818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183818).length < 2 ^ (prefixWord ++ tailWord_6183818).sum := by decide
  have hdescent : baseEnd_6183818 < baseStart_6183818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183827 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 3]
def baseStart_6183827 : Nat := 118140960795 + 6183827 * 2 ^ 59
def prefixEnd_6183827 : Nat := 4983230072969 + 3 ^ 40 * 6183827 * 2
def baseEnd_6183827 : Nat := 3175275535250682482123603

theorem tailTrace_6183827 : CollatzResearch.WordTrace tailWord_6183827 prefixEnd_6183827 3175275535250682482123603 := by
  unfold tailWord_6183827
  simp only [CollatzResearch.WordTrace]
  refine ⟨225542699768058367415213735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150361799845372244943475823 225542699768058367415213735)
  ·
    refine ⟨338314049652087551122820603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225542699768058367415213735 338314049652087551122820603)
    ·
      refine ⟨507471074478131326684230905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338314049652087551122820603 507471074478131326684230905)
      ·
        refine ⟨380603305858598495013173179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507471074478131326684230905 380603305858598495013173179)
        ·
          refine ⟨570904958787897742519759769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380603305858598495013173179 570904958787897742519759769)
          ·
            refine ⟨428178719090923306889819827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570904958787897742519759769 428178719090923306889819827)
            ·
              refine ⟨642268078636384960334729741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428178719090923306889819827 642268078636384960334729741)
              ·
                refine ⟨240850529488644360125523653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642268078636384960334729741 240850529488644360125523653)
                ·
                  refine ⟨45159474279120817523535685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240850529488644360125523653 45159474279120817523535685)
                  ·
                    refine ⟨8467401427335153285662941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45159474279120817523535685 8467401427335153285662941)
                    ·
                      refine ⟨3175275535250682482123603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8467401427335153285662941 3175275535250682482123603)
                      ·
                        rfl

theorem cell23_6183827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_6183827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183827 prefixEnd_6183827 := by exact prefixLift 6183827
  have htrace : WordTrace (prefixWord ++ tailWord_6183827) baseStart_6183827 baseEnd_6183827 := by
    simpa [prefixWord, tailWord_6183827, baseEnd_6183827] using wordTrace_append hprefix tailTrace_6183827
  have hstable : (prefixWord ++ tailWord_6183827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183827).length < 2 ^ (prefixWord ++ tailWord_6183827).sum := by decide
  have hdescent : baseEnd_6183827 < baseStart_6183827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183841 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6183841 : Nat := 118140960795 + 6183841 * 2 ^ 59
def prefixEnd_6183841 : Nat := 4983230072969 + 3 ^ 40 * 6183841 * 2
def baseEnd_6183841 : Nat := 3175282723979845427348539

theorem tailTrace_6183841 : CollatzResearch.WordTrace tailWord_6183841 prefixEnd_6183841 3175282723979845427348539 := by
  unfold tailWord_6183841
  simp only [CollatzResearch.WordTrace]
  refine ⟨225543210390007647806223377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150362140260005098537482251 225543210390007647806223377)
  ·
    refine ⟨169157407792505735854667533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225543210390007647806223377 169157407792505735854667533)
    ·
      refine ⟨63434027922189650945500325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169157407792505735854667533 63434027922189650945500325)
      ·
        refine ⟨11893880235410559552281311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63434027922189650945500325 11893880235410559552281311)
        ·
          refine ⟨17840820353115839328421967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11893880235410559552281311 17840820353115839328421967)
          ·
            refine ⟨26761230529673758992632951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17840820353115839328421967 26761230529673758992632951)
            ·
              refine ⟨40141845794510638488949427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26761230529673758992632951 40141845794510638488949427)
              ·
                refine ⟨60212768691765957733424141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40141845794510638488949427 60212768691765957733424141)
                ·
                  refine ⟨22579788259412234150034053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60212768691765957733424141 22579788259412234150034053)
                  ·
                    refine ⟨4233710298639793903131385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22579788259412234150034053 4233710298639793903131385)
                    ·
                      refine ⟨3175282723979845427348539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233710298639793903131385 3175282723979845427348539)
                      ·
                        rfl

theorem cell23_6183841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6183841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183841 prefixEnd_6183841 := by exact prefixLift 6183841
  have htrace : WordTrace (prefixWord ++ tailWord_6183841) baseStart_6183841 baseEnd_6183841 := by
    simpa [prefixWord, tailWord_6183841, baseEnd_6183841] using wordTrace_append hprefix tailTrace_6183841
  have hstable : (prefixWord ++ tailWord_6183841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183841).length < 2 ^ (prefixWord ++ tailWord_6183841).sum := by decide
  have hdescent : baseEnd_6183841 < baseStart_6183841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183909 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6183909 : Nat := 118140960795 + 6183909 * 2 ^ 59
def prefixEnd_6183909 : Nat := 4983230072969 + 3 ^ 40 * 6183909 * 2
def baseEnd_6183909 : Nat := 3175317640664351161298227

theorem tailTrace_6183909 : CollatzResearch.WordTrace tailWord_6183909 prefixEnd_6183909 3175317640664351161298227 := by
  unfold tailWord_6183909
  simp only [CollatzResearch.WordTrace]
  refine ⟨225545690553761295419698781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150363793702507530279799187 225545690553761295419698781)
  ·
    refine ⟨84579633957660485782387043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225545690553761295419698781 84579633957660485782387043)
    ·
      refine ⟨126869450936490728673580565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84579633957660485782387043 126869450936490728673580565)
      ·
        refine ⟨5947005512648002906574089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126869450936490728673580565 5947005512648002906574089)
        ·
          refine ⟨4460254134486002179930567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5947005512648002906574089 4460254134486002179930567)
          ·
            refine ⟨6690381201729003269895851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460254134486002179930567 6690381201729003269895851)
            ·
              refine ⟨10035571802593504904843777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690381201729003269895851 10035571802593504904843777)
              ·
                refine ⟨7526678851945128678632833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10035571802593504904843777 7526678851945128678632833)
                ·
                  refine ⟨5645009138958846508974625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7526678851945128678632833 5645009138958846508974625)
                  ·
                    refine ⟨4233756854219134881730969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5645009138958846508974625 4233756854219134881730969)
                    ·
                      refine ⟨3175317640664351161298227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233756854219134881730969 3175317640664351161298227)
                      ·
                        rfl

theorem cell23_6183909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6183909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183909 prefixEnd_6183909 := by exact prefixLift 6183909
  have htrace : WordTrace (prefixWord ++ tailWord_6183909) baseStart_6183909 baseEnd_6183909 := by
    simpa [prefixWord, tailWord_6183909, baseEnd_6183909] using wordTrace_append hprefix tailTrace_6183909
  have hstable : (prefixWord ++ tailWord_6183909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183909).length < 2 ^ (prefixWord ++ tailWord_6183909).sum := by decide
  have hdescent : baseEnd_6183909 < baseStart_6183909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183975 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 3, 4]
def baseStart_6183975 : Nat := 118140960795 + 6183975 * 2 ^ 59
def prefixEnd_6183975 : Nat := 4983230072969 + 3 ^ 40 * 6183975 * 2
def baseEnd_6183975 : Nat := 1058450510129182634357641

theorem tailTrace_6183975 : CollatzResearch.WordTrace tailWord_6183975 prefixEnd_6183975 1058450510129182634357641 := by
  unfold tailWord_6183975
  simp only [CollatzResearch.WordTrace]
  refine ⟨225548097771522188691601379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150365398514348125794400919 225548097771522188691601379)
  ·
    refine ⟨338322146657283283037402069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225548097771522188691601379 338322146657283283037402069)
    ·
      refine ⟨7929425312280076946189111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 338322146657283283037402069 7929425312280076946189111)
      ·
        refine ⟨11894137968420115419283667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7929425312280076946189111 11894137968420115419283667)
        ·
          refine ⟨17841206952630173128925501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11894137968420115419283667 17841206952630173128925501)
          ·
            refine ⟨6690452607236314923347063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17841206952630173128925501 6690452607236314923347063)
            ·
              refine ⟨10035678910854472385020595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690452607236314923347063 10035678910854472385020595)
              ·
                refine ⟨15053518366281708577530893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10035678910854472385020595 15053518366281708577530893)
                ·
                  refine ⟨5645069387355640716574085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15053518366281708577530893 5645069387355640716574085)
                  ·
                    refine ⟨1058450510129182634357641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5645069387355640716574085 1058450510129182634357641)
                    ·
                      rfl

theorem cell23_6183975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_6183975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183975 prefixEnd_6183975 := by exact prefixLift 6183975
  have htrace : WordTrace (prefixWord ++ tailWord_6183975) baseStart_6183975 baseEnd_6183975 := by
    simpa [prefixWord, tailWord_6183975, baseEnd_6183975] using wordTrace_append hprefix tailTrace_6183975
  have hstable : (prefixWord ++ tailWord_6183975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183975).length < 2 ^ (prefixWord ++ tailWord_6183975).sum := by decide
  have hdescent : baseEnd_6183975 < baseStart_6183975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183984 : List Nat := [2, 1, 1, 1, 2, 4, 2, 2, 3, 5]
def baseStart_6183984 : Nat := 118140960795 + 6183984 * 2 ^ 59
def prefixEnd_6183984 : Nat := 4983230072969 + 3 ^ 40 * 6183984 * 2
def baseEnd_6183984 : Nat := 1058452050571146122620127

theorem tailTrace_6183984 : CollatzResearch.WordTrace tailWord_6183984 prefixEnd_6183984 1058452050571146122620127 := by
  unfold tailWord_6183984
  simp only [CollatzResearch.WordTrace]
  refine ⟨112774213014244791614339503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150365617352326388819119337 112774213014244791614339503)
  ·
    refine ⟨169161319521367187421509255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112774213014244791614339503 169161319521367187421509255)
    ·
      refine ⟨253741979282050781132263883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169161319521367187421509255 253741979282050781132263883)
      ·
        refine ⟨380612968923076171698395825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253741979282050781132263883 380612968923076171698395825)
        ·
          refine ⟨285459726692307128773796869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380612968923076171698395825 285459726692307128773796869)
          ·
            refine ⟨53523698754807586645086913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285459726692307128773796869 53523698754807586645086913)
            ·
              refine ⟨40142774066105689983815185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53523698754807586645086913 40142774066105689983815185)
              ·
                refine ⟨30107080549579267487861389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40142774066105689983815185 30107080549579267487861389)
                ·
                  refine ⟨11290155206092225307948021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30107080549579267487861389 11290155206092225307948021)
                  ·
                    refine ⟨1058452050571146122620127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11290155206092225307948021 1058452050571146122620127)
                    ·
                      rfl

theorem cell23_6183984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_6183984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183984 prefixEnd_6183984 := by exact prefixLift 6183984
  have htrace : WordTrace (prefixWord ++ tailWord_6183984) baseStart_6183984 baseEnd_6183984 := by
    simpa [prefixWord, tailWord_6183984, baseEnd_6183984] using wordTrace_append hprefix tailTrace_6183984
  have hstable : (prefixWord ++ tailWord_6183984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183984).length < 2 ^ (prefixWord ++ tailWord_6183984).sum := by decide
  have hdescent : baseEnd_6183984 < baseStart_6183984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183988 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 6]
def baseStart_6183988 : Nat := 118140960795 + 6183988 * 2 ^ 59
def prefixEnd_6183988 : Nat := 4983230072969 + 3 ^ 40 * 6183988 * 2
def baseEnd_6183988 : Nat := 352817578404006261356707

theorem tailTrace_6183988 : CollatzResearch.WordTrace tailWord_6183988 prefixEnd_6183988 352817578404006261356707 := by
  unfold tailWord_6183988
  simp only [CollatzResearch.WordTrace]
  refine ⟨112774285960237545955912309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150365714613650061274549745 112774285960237545955912309)
  ·
    refine ⟨10572589308772269933366779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112774285960237545955912309 10572589308772269933366779)
    ·
      refine ⟨15858883963158404900050169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10572589308772269933366779 15858883963158404900050169)
      ·
        refine ⟨11894162972368803675037627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15858883963158404900050169 11894162972368803675037627)
        ·
          refine ⟨17841244458553205512556441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11894162972368803675037627 17841244458553205512556441)
          ·
            refine ⟨13380933343914904134417331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17841244458553205512556441 13380933343914904134417331)
            ·
              refine ⟨20071400015872356201625997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13380933343914904134417331 20071400015872356201625997)
              ·
                refine ⟨7526775005952133575609749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20071400015872356201625997 7526775005952133575609749)
                ·
                  refine ⟨352817578404006261356707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7526775005952133575609749 352817578404006261356707)
                  ·
                    rfl

theorem cell23_6183988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_6183988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183988 prefixEnd_6183988 := by exact prefixLift 6183988
  have htrace : WordTrace (prefixWord ++ tailWord_6183988) baseStart_6183988 baseEnd_6183988 := by
    simpa [prefixWord, tailWord_6183988, baseEnd_6183988] using wordTrace_append hprefix tailTrace_6183988
  have hstable : (prefixWord ++ tailWord_6183988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183988).length < 2 ^ (prefixWord ++ tailWord_6183988).sum := by decide
  have hdescent : baseEnd_6183988 < baseStart_6183988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6183991 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 6, 3, 2]
def baseStart_6183991 : Nat := 118140960795 + 6183991 * 2 ^ 59
def prefixEnd_6183991 : Nat := 4983230072969 + 3 ^ 40 * 6183991 * 2
def baseEnd_6183991 : Nat := 3175359746078019840472849

theorem tailTrace_6183991 : CollatzResearch.WordTrace tailWord_6183991 prefixEnd_6183991 3175359746078019840472849 := by
  unfold tailWord_6183991
  simp only [CollatzResearch.WordTrace]
  refine ⟨225548681339464223424183827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150365787559642815616122551 225548681339464223424183827)
  ·
    refine ⟨338323022009196335136275741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225548681339464223424183827 338323022009196335136275741)
    ·
      refine ⟨126871133253448625676103403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338323022009196335136275741 126871133253448625676103403)
      ·
        refine ⟨190306699880172938514155105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126871133253448625676103403 190306699880172938514155105)
        ·
          refine ⟨142730024910129703885616329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190306699880172938514155105 142730024910129703885616329)
          ·
            refine ⟨107047518682597277914212247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142730024910129703885616329 107047518682597277914212247)
            ·
              refine ⟨160571278023895916871318371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107047518682597277914212247 160571278023895916871318371)
              ·
                refine ⟨240856917035843875306977557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160571278023895916871318371 240856917035843875306977557)
                ·
                  refine ⟨11290167986055181655014573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240856917035843875306977557 11290167986055181655014573)
                  ·
                    refine ⟨4233812994770693120630465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11290167986055181655014573 4233812994770693120630465)
                    ·
                      refine ⟨3175359746078019840472849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233812994770693120630465 3175359746078019840472849)
                      ·
                        rfl

theorem cell23_6183991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_6183991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6183991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6183991 prefixEnd_6183991 := by exact prefixLift 6183991
  have htrace : WordTrace (prefixWord ++ tailWord_6183991) baseStart_6183991 baseEnd_6183991 := by
    simpa [prefixWord, tailWord_6183991, baseEnd_6183991] using wordTrace_append hprefix tailTrace_6183991
  have hstable : (prefixWord ++ tailWord_6183991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6183991).length < 2 ^ (prefixWord ++ tailWord_6183991).sum := by decide
  have hdescent : baseEnd_6183991 < baseStart_6183991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6183991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184008 : List Nat := [2, 1, 3, 1, 1, 1, 6, 1, 2, 3, 2]
def baseStart_6184008 : Nat := 118140960795 + 6184008 * 2 ^ 59
def prefixEnd_6184008 : Nat := 4983230072969 + 3 ^ 40 * 6184008 * 2
def baseEnd_6184008 : Nat := 3175368475249146273960271

theorem tailTrace_6184008 : CollatzResearch.WordTrace tailWord_6184008 prefixEnd_6184008 3175368475249146273960271 := by
  unfold tailWord_6184008
  simp only [CollatzResearch.WordTrace]
  refine ⟨112774650690201317663776339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150366200920268423551701785 112774650690201317663776339)
  ·
    refine ⟨169161976035301976495664509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112774650690201317663776339 169161976035301976495664509)
    ·
      refine ⟨63435741013238241185874191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169161976035301976495664509 63435741013238241185874191)
      ·
        refine ⟨95153611519857361778811287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63435741013238241185874191 95153611519857361778811287)
        ·
          refine ⟨142730417279786042668216931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95153611519857361778811287 142730417279786042668216931)
          ·
            refine ⟨214095625919679064002325397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142730417279786042668216931 214095625919679064002325397)
            ·
              refine ⟨10035732464984956125109003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214095625919679064002325397 10035732464984956125109003)
              ·
                refine ⟨15053598697477434187663505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10035732464984956125109003 15053598697477434187663505)
                ·
                  refine ⟨11290199023108075640747629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15053598697477434187663505 11290199023108075640747629)
                  ·
                    refine ⟨4233824633665528365280361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11290199023108075640747629 4233824633665528365280361)
                    ·
                      refine ⟨3175368475249146273960271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233824633665528365280361 3175368475249146273960271)
                      ·
                        rfl

theorem cell23_6184008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 1, 2, 3, 2].length) (baseStart_6184008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184008 prefixEnd_6184008 := by exact prefixLift 6184008
  have htrace : WordTrace (prefixWord ++ tailWord_6184008) baseStart_6184008 baseEnd_6184008 := by
    simpa [prefixWord, tailWord_6184008, baseEnd_6184008] using wordTrace_append hprefix tailTrace_6184008
  have hstable : (prefixWord ++ tailWord_6184008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184008).length < 2 ^ (prefixWord ++ tailWord_6184008).sum := by decide
  have hdescent : baseEnd_6184008 < baseStart_6184008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184041 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 3]
def baseStart_6184041 : Nat := 118140960795 + 6184041 * 2 ^ 59
def prefixEnd_6184041 : Nat := 4983230072969 + 3 ^ 40 * 6184041 * 2
def baseEnd_6184041 : Nat := 3175385420110744644847619

theorem tailTrace_6184041 : CollatzResearch.WordTrace tailWord_6184041 prefixEnd_6184041 3175385420110744644847619 := by
  unfold tailWord_6184041
  simp only [CollatzResearch.WordTrace]
  refine ⟨225550504989283081963503977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150367003326188721309002651 225550504989283081963503977)
  ·
    refine ⟨169162878741962311472627983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225550504989283081963503977 169162878741962311472627983)
    ·
      refine ⟨253744318112943467208941975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169162878741962311472627983 253744318112943467208941975)
      ·
        refine ⟨380616477169415200813412963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253744318112943467208941975 380616477169415200813412963)
        ·
          refine ⟨570924715754122801220119445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380616477169415200813412963 570924715754122801220119445)
          ·
            refine ⟨26762096050974506307193099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 570924715754122801220119445 26762096050974506307193099)
            ·
              refine ⟨40143144076461759460789649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26762096050974506307193099 40143144076461759460789649)
              ·
                refine ⟨30107358057346319595592237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40143144076461759460789649 30107358057346319595592237)
                ·
                  refine ⟨11290259271504869848347089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30107358057346319595592237 11290259271504869848347089)
                  ·
                    refine ⟨8467694453628652386260317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11290259271504869848347089 8467694453628652386260317)
                    ·
                      refine ⟨3175385420110744644847619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8467694453628652386260317 3175385420110744644847619)
                      ·
                        rfl

theorem cell23_6184041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 2, 3].length) (baseStart_6184041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184041 prefixEnd_6184041 := by exact prefixLift 6184041
  have htrace : WordTrace (prefixWord ++ tailWord_6184041) baseStart_6184041 baseEnd_6184041 := by
    simpa [prefixWord, tailWord_6184041, baseEnd_6184041] using wordTrace_append hprefix tailTrace_6184041
  have hstable : (prefixWord ++ tailWord_6184041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184041).length < 2 ^ (prefixWord ++ tailWord_6184041).sum := by decide
  have hdescent : baseEnd_6184041 < baseStart_6184041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184061 : List Nat := [1, 4, 1, 1, 3, 1, 5, 7]
def baseStart_6184061 : Nat := 118140960795 + 6184061 * 2 ^ 59
def prefixEnd_6184061 : Nat := 4983230072969 + 3 ^ 40 * 6184061 * 2
def baseEnd_6184061 : Nat := 117607247767549428392501

theorem tailTrace_6184061 : CollatzResearch.WordTrace tailWord_6184061 prefixEnd_6184061 117607247767549428392501 := by
  unfold tailWord_6184061
  simp only [CollatzResearch.WordTrace]
  refine ⟨225551234449210625379232037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150367489632807083586154691 225551234449210625379232037)
  ·
    refine ⟨42290856459226992258606007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225551234449210625379232037 42290856459226992258606007)
    ·
      refine ⟨63436284688840488387909011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42290856459226992258606007 63436284688840488387909011)
      ·
        refine ⟨95154427033260732581863517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63436284688840488387909011 95154427033260732581863517)
        ·
          refine ⟨35682910137472774718198819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95154427033260732581863517 35682910137472774718198819)
          ·
            refine ⟨53524365206209162077298229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35682910137472774718198819 53524365206209162077298229)
            ·
              refine ⟨5017909238082108944746709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53524365206209162077298229 5017909238082108944746709)
              ·
                refine ⟨117607247767549428392501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5017909238082108944746709 117607247767549428392501)
                ·
                  rfl

theorem cell23_6184061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 5, 7].length) (baseStart_6184061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184061 prefixEnd_6184061 := by exact prefixLift 6184061
  have htrace : WordTrace (prefixWord ++ tailWord_6184061) baseStart_6184061 baseEnd_6184061 := by
    simpa [prefixWord, tailWord_6184061, baseEnd_6184061] using wordTrace_append hprefix tailTrace_6184061
  have hstable : (prefixWord ++ tailWord_6184061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184061).length < 2 ^ (prefixWord ++ tailWord_6184061).sum := by decide
  have hdescent : baseEnd_6184061 < baseStart_6184061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184072 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 1, 1, 4]
def baseStart_6184072 : Nat := 118140960795 + 6184072 * 2 ^ 59
def prefixEnd_6184072 : Nat := 4983230072969 + 3 ^ 40 * 6184072 * 2
def baseEnd_6184072 : Nat := 3175401338011034023559977

theorem tailTrace_6184072 : CollatzResearch.WordTrace tailWord_6184072 prefixEnd_6184072 3175401338011034023559977 := by
  unfold tailWord_6184072
  simp only [CollatzResearch.WordTrace]
  refine ⟨112775817826085387128941235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150367757101447182838588313 112775817826085387128941235)
  ·
    refine ⟨169163726739128080693411853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112775817826085387128941235 169163726739128080693411853)
    ·
      refine ⟨63436397527173030260029445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169163726739128080693411853 63436397527173030260029445)
      ·
        refine ⟨11894324536344943173755521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63436397527173030260029445 11894324536344943173755521)
        ·
          refine ⟨8920743402258707380316641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11894324536344943173755521 8920743402258707380316641)
          ·
            refine ⟨6690557551694030535237481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8920743402258707380316641 6690557551694030535237481)
            ·
              refine ⟨5017918163770522901428111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6690557551694030535237481 5017918163770522901428111)
              ·
                refine ⟨7526877245655784352142167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017918163770522901428111 7526877245655784352142167)
                ·
                  refine ⟨11290315868483676528213251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7526877245655784352142167 11290315868483676528213251)
                  ·
                    refine ⟨16935473802725514792319877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11290315868483676528213251 16935473802725514792319877)
                    ·
                      refine ⟨3175401338011034023559977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16935473802725514792319877 3175401338011034023559977)
                      ·
                        rfl

theorem cell23_6184072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_6184072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184072 prefixEnd_6184072 := by exact prefixLift 6184072
  have htrace : WordTrace (prefixWord ++ tailWord_6184072) baseStart_6184072 baseEnd_6184072 := by
    simpa [prefixWord, tailWord_6184072, baseEnd_6184072] using wordTrace_append hprefix tailTrace_6184072
  have hstable : (prefixWord ++ tailWord_6184072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184072).length < 2 ^ (prefixWord ++ tailWord_6184072).sum := by decide
  have hdescent : baseEnd_6184072 < baseStart_6184072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184145 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 2, 2, 2]
def baseStart_6184145 : Nat := 118140960795 + 6184145 * 2 ^ 59
def prefixEnd_6184145 : Nat := 4983230072969 + 3 ^ 40 * 6184145 * 2
def baseEnd_6184145 : Nat := 3175438822098812237947141

theorem tailTrace_6184145 : CollatzResearch.WordTrace tailWord_6184145 prefixEnd_6184145 3175438822098812237947141 := by
  unfold tailWord_6184145
  simp only [CollatzResearch.WordTrace]
  refine ⟨225554298180906307725289889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150369532120604205150193259 225554298180906307725289889)
  ·
    refine ⟨169165723635679730793967417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225554298180906307725289889 169165723635679730793967417)
    ·
      refine ⟨126874292726759798095475563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169165723635679730793967417 126874292726759798095475563)
      ·
        refine ⟨190311439090139697143213345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126874292726759798095475563 190311439090139697143213345)
        ·
          refine ⟨142733579317604772857410009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190311439090139697143213345 142733579317604772857410009)
          ·
            refine ⟨107050184488203579643057507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142733579317604772857410009 107050184488203579643057507)
            ·
              refine ⟨160575276732305369464586261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107050184488203579643057507 160575276732305369464586261)
              ·
                refine ⟨7526966096826814193652481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 160575276732305369464586261 7526966096826814193652481)
                ·
                  refine ⟨5645224572620110645239361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7526966096826814193652481 5645224572620110645239361)
                  ·
                    refine ⟨4233918429465082983929521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5645224572620110645239361 4233918429465082983929521)
                    ·
                      refine ⟨3175438822098812237947141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4233918429465082983929521 3175438822098812237947141)
                      ·
                        rfl

theorem cell23_6184145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_6184145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184145 prefixEnd_6184145 := by exact prefixLift 6184145
  have htrace : WordTrace (prefixWord ++ tailWord_6184145) baseStart_6184145 baseEnd_6184145 := by
    simpa [prefixWord, tailWord_6184145, baseEnd_6184145] using wordTrace_append hprefix tailTrace_6184145
  have hstable : (prefixWord ++ tailWord_6184145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184145).length < 2 ^ (prefixWord ++ tailWord_6184145).sum := by decide
  have hdescent : baseEnd_6184145 < baseStart_6184145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184151 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 7]
def baseStart_6184151 : Nat := 118140960795 + 6184151 * 2 ^ 59
def prefixEnd_6184151 : Nat := 4983230072969 + 3 ^ 40 * 6184151 * 2
def baseEnd_6184151 : Nat := 352826878109193246052457

theorem tailTrace_6184151 : CollatzResearch.WordTrace tailWord_6184151 prefixEnd_6184151 352826878109193246052457 := by
  unfold tailWord_6184151
  simp only [CollatzResearch.WordTrace]
  refine ⟨225554517018884570750008307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150369678012589713833338871 225554517018884570750008307)
  ·
    refine ⟨338331775528326856125012461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225554517018884570750008307 338331775528326856125012461)
    ·
      refine ⟨126874415823122571046879673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338331775528326856125012461 126874415823122571046879673)
      ·
        refine ⟨95155811867341928285159755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126874415823122571046879673 95155811867341928285159755)
        ·
          refine ⟨142733717801012892427739633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95155811867341928285159755 142733717801012892427739633)
          ·
            refine ⟨107050288350759669320804725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142733717801012892427739633 107050288350759669320804725)
            ·
              refine ⟨10035964532883718998825443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107050288350759669320804725 10035964532883718998825443)
              ·
                refine ⟨15053946799325578498238165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10035964532883718998825443 15053946799325578498238165)
                ·
                  refine ⟨352826878109193246052457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15053946799325578498238165 352826878109193246052457)
                  ·
                    rfl

theorem cell23_6184151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 7].length) (baseStart_6184151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184151 prefixEnd_6184151 := by exact prefixLift 6184151
  have htrace : WordTrace (prefixWord ++ tailWord_6184151) baseStart_6184151 baseEnd_6184151 := by
    simpa [prefixWord, tailWord_6184151, baseEnd_6184151] using wordTrace_append hprefix tailTrace_6184151
  have hstable : (prefixWord ++ tailWord_6184151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184151).length < 2 ^ (prefixWord ++ tailWord_6184151).sum := by decide
  have hdescent : baseEnd_6184151 < baseStart_6184151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184191 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_6184191 : Nat := 118140960795 + 6184191 * 2 ^ 59
def prefixEnd_6184191 : Nat := 4983230072969 + 3 ^ 40 * 6184191 * 2
def baseEnd_6184191 : Nat := 3175462442208919057971929

theorem tailTrace_6184191 : CollatzResearch.WordTrace tailWord_6184191 prefixEnd_6184191 3175462442208919057971929 := by
  unfold tailWord_6184191
  simp only [CollatzResearch.WordTrace]
  refine ⟨225555975938739657581464427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150370650625826438387642951 225555975938739657581464427)
  ·
    refine ⟨338333963908109486372196641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225555975938739657581464427 338333963908109486372196641)
    ·
      refine ⟨253750472931082114779147481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338333963908109486372196641 253750472931082114779147481)
      ·
        refine ⟨190312854698311586084360611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253750472931082114779147481 190312854698311586084360611)
        ·
          refine ⟨285469282047467379126540917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190312854698311586084360611 285469282047467379126540917)
          ·
            refine ⟨26762745191950066793113211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285469282047467379126540917 26762745191950066793113211)
            ·
              refine ⟨40144117787925100189669817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26762745191950066793113211 40144117787925100189669817)
              ·
                refine ⟨30108088340943825142252363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40144117787925100189669817 30108088340943825142252363)
                ·
                  refine ⟨45162132511415737713378545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30108088340943825142252363 45162132511415737713378545)
                  ·
                    refine ⟨33871599383561803285033909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45162132511415737713378545 33871599383561803285033909)
                    ·
                      refine ⟨3175462442208919057971929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33871599383561803285033909 3175462442208919057971929)
                      ·
                        rfl

theorem cell23_6184191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_6184191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184191 prefixEnd_6184191 := by exact prefixLift 6184191
  have htrace : WordTrace (prefixWord ++ tailWord_6184191) baseStart_6184191 baseEnd_6184191 := by
    simpa [prefixWord, tailWord_6184191, baseEnd_6184191] using wordTrace_append hprefix tailTrace_6184191
  have hstable : (prefixWord ++ tailWord_6184191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184191).length < 2 ^ (prefixWord ++ tailWord_6184191).sum := by decide
  have hdescent : baseEnd_6184191 < baseStart_6184191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184281 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_6184281 : Nat := 118140960795 + 6184281 * 2 ^ 59
def prefixEnd_6184281 : Nat := 4983230072969 + 3 ^ 40 * 6184281 * 2
def baseEnd_6184281 : Nat := 3175508655467823705846515

theorem tailTrace_6184281 : CollatzResearch.WordTrace tailWord_6184281 prefixEnd_6184281 3175508655467823705846515 := by
  unfold tailWord_6184281
  simp only [CollatzResearch.WordTrace]
  refine ⟨225559258508413602952240697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150372839005609068634827131 225559258508413602952240697)
  ·
    refine ⟨169169443881310202214180523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225559258508413602952240697 169169443881310202214180523)
    ·
      refine ⟨253754165821965303321270785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169169443881310202214180523 253754165821965303321270785)
      ·
        refine ⟨190315624366473977490953089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253754165821965303321270785 190315624366473977490953089)
        ·
          refine ⟨142736718274855483118214817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190315624366473977490953089 142736718274855483118214817)
          ·
            refine ⟨107052538706141612338661113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142736718274855483118214817 107052538706141612338661113)
            ·
              refine ⟨80289404029606209253995835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107052538706141612338661113 80289404029606209253995835)
              ·
                refine ⟨120434106044409313880993753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80289404029606209253995835 120434106044409313880993753)
                ·
                  refine ⟨90325579533306985410745315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120434106044409313880993753 90325579533306985410745315)
                  ·
                    refine ⟨135488369299960478116117973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90325579533306985410745315 135488369299960478116117973)
                    ·
                      refine ⟨3175508655467823705846515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135488369299960478116117973 3175508655467823705846515)
                      ·
                        rfl

theorem cell23_6184281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_6184281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184281 prefixEnd_6184281 := by exact prefixLift 6184281
  have htrace : WordTrace (prefixWord ++ tailWord_6184281) baseStart_6184281 baseEnd_6184281 := by
    simpa [prefixWord, tailWord_6184281, baseEnd_6184281] using wordTrace_append hprefix tailTrace_6184281
  have hstable : (prefixWord ++ tailWord_6184281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184281).length < 2 ^ (prefixWord ++ tailWord_6184281).sum := by decide
  have hdescent : baseEnd_6184281 < baseStart_6184281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184296 : List Nat := [2, 1, 4, 2, 4, 1, 1, 3, 1, 4]
def baseStart_6184296 : Nat := 118140960795 + 6184296 * 2 ^ 59
def prefixEnd_6184296 : Nat := 4983230072969 + 3 ^ 40 * 6184296 * 2
def baseEnd_6184296 : Nat := 1058505452559213715719649

theorem tailTrace_6184296 : CollatzResearch.WordTrace tailWord_6184296 prefixEnd_6184296 1058505452559213715719649 := by
  unfold tailWord_6184296
  simp only [CollatzResearch.WordTrace]
  refine ⟨112779902801679630257018371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150373203735572840342691161 112779902801679630257018371)
  ·
    refine ⟨169169854202519445385527557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112779902801679630257018371 169169854202519445385527557)
    ·
      refine ⟨31719347662972396009786417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169169854202519445385527557 31719347662972396009786417)
      ·
        refine ⟨23789510747229297007339813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31719347662972396009786417 23789510747229297007339813)
        ·
          refine ⟨4460533265105493188876215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23789510747229297007339813 4460533265105493188876215)
          ·
            refine ⟨6690799897658239783314323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460533265105493188876215 6690799897658239783314323)
            ·
              refine ⟨10036199846487359674971485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690799897658239783314323 10036199846487359674971485)
              ·
                refine ⟨3763574942432759878114307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10036199846487359674971485 3763574942432759878114307)
                ·
                  refine ⟨5645362413649139817171461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763574942432759878114307 5645362413649139817171461)
                  ·
                    refine ⟨1058505452559213715719649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5645362413649139817171461 1058505452559213715719649)
                    ·
                      rfl

theorem cell23_6184296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_6184296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184296 prefixEnd_6184296 := by exact prefixLift 6184296
  have htrace : WordTrace (prefixWord ++ tailWord_6184296) baseStart_6184296 baseEnd_6184296 := by
    simpa [prefixWord, tailWord_6184296, baseEnd_6184296] using wordTrace_append hprefix tailTrace_6184296
  have hstable : (prefixWord ++ tailWord_6184296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184296).length < 2 ^ (prefixWord ++ tailWord_6184296).sum := by decide
  have hdescent : baseEnd_6184296 < baseStart_6184296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184345 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 3]
def baseStart_6184345 : Nat := 118140960795 + 6184345 * 2 ^ 59
def prefixEnd_6184345 : Nat := 4983230072969 + 3 ^ 40 * 6184345 * 2
def baseEnd_6184345 : Nat := 3175541518229711455446221

theorem tailTrace_6184345 : CollatzResearch.WordTrace tailWord_6184345 prefixEnd_6184345 3175541518229711455446221 := by
  unfold tailWord_6184345
  simp only [CollatzResearch.WordTrace]
  refine ⟨225561592780181741882570489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150374395186787827921713659 225561592780181741882570489)
  ·
    refine ⟨169171194585136306411927867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225561592780181741882570489 169171194585136306411927867)
    ·
      refine ⟨253756791877704459617891801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169171194585136306411927867 253756791877704459617891801)
      ·
        refine ⟨190317593908278344713418851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253756791877704459617891801 190317593908278344713418851)
        ·
          refine ⟨285476390862417517070128277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190317593908278344713418851 285476390862417517070128277)
          ·
            refine ⟨13381705821675821112662263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285476390862417517070128277 13381705821675821112662263)
            ·
              refine ⟨20072558732513731668993395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13381705821675821112662263 20072558732513731668993395)
              ·
                refine ⟨30108838098770597503490093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20072558732513731668993395 30108838098770597503490093)
                ·
                  refine ⟨11290814287038974063808785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30108838098770597503490093 11290814287038974063808785)
                  ·
                    refine ⟨8468110715279230547856589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11290814287038974063808785 8468110715279230547856589)
                    ·
                      refine ⟨3175541518229711455446221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8468110715279230547856589 3175541518229711455446221)
                      ·
                        rfl

theorem cell23_6184345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_6184345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184345 prefixEnd_6184345 := by exact prefixLift 6184345
  have htrace : WordTrace (prefixWord ++ tailWord_6184345) baseStart_6184345 baseEnd_6184345 := by
    simpa [prefixWord, tailWord_6184345, baseEnd_6184345] using wordTrace_append hprefix tailTrace_6184345
  have hstable : (prefixWord ++ tailWord_6184345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184345).length < 2 ^ (prefixWord ++ tailWord_6184345).sum := by decide
  have hdescent : baseEnd_6184345 < baseStart_6184345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184376 : List Nat := [2, 1, 2, 1, 2, 2, 6, 2, 1, 2, 2]
def baseStart_6184376 : Nat := 118140960795 + 6184376 * 2 ^ 59
def prefixEnd_6184376 : Nat := 4983230072969 + 3 ^ 40 * 6184376 * 2
def baseEnd_6184376 : Nat := 3175557436130000834158579

theorem tailTrace_6184376 : CollatzResearch.WordTrace tailWord_6184376 prefixEnd_6184376 3175557436130000834158579 := by
  unfold tailWord_6184376
  simp only [CollatzResearch.WordTrace]
  refine ⟨112781361721534717088474491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150375148962046289451299321 112781361721534717088474491)
  ·
    refine ⟨169172042582302075632711737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112781361721534717088474491 169172042582302075632711737)
    ·
      refine ⟨126879031936726556724533803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169172042582302075632711737 126879031936726556724533803)
      ·
        refine ⟨190318547905089835086800705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126879031936726556724533803 190318547905089835086800705)
        ·
          refine ⟨142738910928817376315100529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190318547905089835086800705 142738910928817376315100529)
          ·
            refine ⟨107054183196613032236325397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142738910928817376315100529 107054183196613032236325397)
            ·
              refine ⟨5018164837341235886077753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107054183196613032236325397 5018164837341235886077753)
              ·
                refine ⟨3763623628005926914558315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5018164837341235886077753 3763623628005926914558315)
                ·
                  refine ⟨5645435442008890371837473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763623628005926914558315 5645435442008890371837473)
                  ·
                    refine ⟨4234076581506667778878105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5645435442008890371837473 4234076581506667778878105)
                    ·
                      refine ⟨3175557436130000834158579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234076581506667778878105 3175557436130000834158579)
                      ·
                        rfl

theorem cell23_6184376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 1, 2, 2].length) (baseStart_6184376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184376 prefixEnd_6184376 := by exact prefixLift 6184376
  have htrace : WordTrace (prefixWord ++ tailWord_6184376) baseStart_6184376 baseEnd_6184376 := by
    simpa [prefixWord, tailWord_6184376, baseEnd_6184376] using wordTrace_append hprefix tailTrace_6184376
  have hstable : (prefixWord ++ tailWord_6184376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184376).length < 2 ^ (prefixWord ++ tailWord_6184376).sum := by decide
  have hdescent : baseEnd_6184376 < baseStart_6184376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184392 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 2, 1, 3]
def baseStart_6184392 : Nat := 118140960795 + 6184392 * 2 ^ 59
def prefixEnd_6184392 : Nat := 4983230072969 + 3 ^ 40 * 6184392 * 2
def baseEnd_6184392 : Nat := 3175565651820472771558505

theorem tailTrace_6184392 : CollatzResearch.WordTrace tailWord_6184392 prefixEnd_6184392 3175565651820472771558505 := by
  unfold tailWord_6184392
  simp only [CollatzResearch.WordTrace]
  refine ⟨112781653505505734454765715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150375538007340979273020953 112781653505505734454765715)
  ·
    refine ⟨169172480258258601682148573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112781653505505734454765715 169172480258258601682148573)
    ·
      refine ⟨63439680096846975630805715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169172480258258601682148573 63439680096846975630805715)
      ·
        refine ⟨95159520145270463446208573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63439680096846975630805715 95159520145270463446208573)
        ·
          refine ⟨35684820054476423792328215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95159520145270463446208573 35684820054476423792328215)
          ·
            refine ⟨53527230081714635688492323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35684820054476423792328215 53527230081714635688492323)
            ·
              refine ⟨80290845122571953532738485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53527230081714635688492323 80290845122571953532738485)
              ·
                refine ⟨7527266730241120643694233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80290845122571953532738485 7527266730241120643694233)
                ·
                  refine ⟨5645450047680840482770675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7527266730241120643694233 5645450047680840482770675)
                  ·
                    refine ⟨8468175071521260724156013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5645450047680840482770675 8468175071521260724156013)
                    ·
                      refine ⟨3175565651820472771558505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8468175071521260724156013 3175565651820472771558505)
                      ·
                        rfl

theorem cell23_6184392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 2, 1, 3].length) (baseStart_6184392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184392 prefixEnd_6184392 := by exact prefixLift 6184392
  have htrace : WordTrace (prefixWord ++ tailWord_6184392) baseStart_6184392 baseEnd_6184392 := by
    simpa [prefixWord, tailWord_6184392, baseEnd_6184392] using wordTrace_append hprefix tailTrace_6184392
  have hstable : (prefixWord ++ tailWord_6184392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184392).length < 2 ^ (prefixWord ++ tailWord_6184392).sum := by decide
  have hdescent : baseEnd_6184392 < baseStart_6184392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184419 : List Nat := [1, 1, 1, 6, 2, 2, 1, 3, 1, 3, 2]
def baseStart_6184419 : Nat := 118140960795 + 6184419 * 2 ^ 59
def prefixEnd_6184419 : Nat := 4983230072969 + 3 ^ 40 * 6184419 * 2
def baseEnd_6184419 : Nat := 3175579515798144165920881

theorem tailTrace_6184419 : CollatzResearch.WordTrace tailWord_6184419 prefixEnd_6184419 3175579515798144165920881 := by
  unfold tailWord_6184419
  simp only [CollatzResearch.WordTrace]
  refine ⟨225564291781913652520764311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150376194521275768347176207 225564291781913652520764311)
  ·
    refine ⟨338346437672870478781146467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225564291781913652520764311 338346437672870478781146467)
    ·
      refine ⟨507519656509305718171719701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338346437672870478781146467 507519656509305718171719701)
      ·
        refine ⟨23789983898873705539299361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 507519656509305718171719701 23789983898873705539299361)
        ·
          refine ⟨17842487924155279154474521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23789983898873705539299361 17842487924155279154474521)
          ·
            refine ⟨13381865943116459365855891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17842487924155279154474521 13381865943116459365855891)
            ·
              refine ⟨20072798914674689048783837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13381865943116459365855891 20072798914674689048783837)
              ·
                refine ⟨7527299593003008393293939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20072798914674689048783837 7527299593003008393293939)
                ·
                  refine ⟨11290949389504512589940909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7527299593003008393293939 11290949389504512589940909)
                  ·
                    refine ⟨4234106021064192221227841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11290949389504512589940909 4234106021064192221227841)
                    ·
                      refine ⟨3175579515798144165920881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234106021064192221227841 3175579515798144165920881)
                      ·
                        rfl

theorem cell23_6184419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_6184419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184419 prefixEnd_6184419 := by exact prefixLift 6184419
  have htrace : WordTrace (prefixWord ++ tailWord_6184419) baseStart_6184419 baseEnd_6184419 := by
    simpa [prefixWord, tailWord_6184419, baseEnd_6184419] using wordTrace_append hprefix tailTrace_6184419
  have hstable : (prefixWord ++ tailWord_6184419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184419).length < 2 ^ (prefixWord ++ tailWord_6184419).sum := by decide
  have hdescent : baseEnd_6184419 < baseStart_6184419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184426 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3]
def baseStart_6184426 : Nat := 118140960795 + 6184426 * 2 ^ 59
def prefixEnd_6184426 : Nat := 4983230072969 + 3 ^ 40 * 6184426 * 2
def baseEnd_6184426 : Nat := 3175583110162725638533349

theorem tailTrace_6184426 : CollatzResearch.WordTrace tailWord_6184426 prefixEnd_6184426 3175583110162725638533349 := by
  unfold tailWord_6184426
  simp only [CollatzResearch.WordTrace]
  refine ⟨56391136773222073179067283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150376364728592195144179421 56391136773222073179067283)
  ·
    refine ⟨84586705159833109768600925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56391136773222073179067283 84586705159833109768600925)
    ·
      refine ⟨31720014434937416163225347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84586705159833109768600925 31720014434937416163225347)
      ·
        refine ⟨47580021652406124244838021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31720014434937416163225347 47580021652406124244838021)
        ·
          refine ⟨8921254059826148295907129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47580021652406124244838021 8921254059826148295907129)
          ·
            refine ⟨6690940544869611221930347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921254059826148295907129 6690940544869611221930347)
            ·
              refine ⟨10036410817304416832895521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690940544869611221930347 10036410817304416832895521)
              ·
                refine ⟨7527308112978312624671641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036410817304416832895521 7527308112978312624671641)
                ·
                  refine ⟨5645481084733734468503731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7527308112978312624671641 5645481084733734468503731)
                  ·
                    refine ⟨8468221627100601702755597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5645481084733734468503731 8468221627100601702755597)
                    ·
                      refine ⟨3175583110162725638533349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8468221627100601702755597 3175583110162725638533349)
                      ·
                        rfl

theorem cell23_6184426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_6184426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184426 prefixEnd_6184426 := by exact prefixLift 6184426
  have htrace : WordTrace (prefixWord ++ tailWord_6184426) baseStart_6184426 baseEnd_6184426 := by
    simpa [prefixWord, tailWord_6184426, baseEnd_6184426] using wordTrace_append hprefix tailTrace_6184426
  have hstable : (prefixWord ++ tailWord_6184426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184426).length < 2 ^ (prefixWord ++ tailWord_6184426).sum := by decide
  have hdescent : baseEnd_6184426 < baseStart_6184426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184445 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_6184445 : Nat := 118140960795 + 6184445 * 2 ^ 59
def prefixEnd_6184445 : Nat := 4983230072969 + 3 ^ 40 * 6184445 * 2
def baseEnd_6184445 : Nat := 3175592866295161064195761

theorem tailTrace_6184445 : CollatzResearch.WordTrace tailWord_6184445 prefixEnd_6184445 3175592866295161064195761 := by
  unfold tailWord_6184445
  simp only [CollatzResearch.WordTrace]
  refine ⟨225565240079819458961210789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150376826719879639307473859 225565240079819458961210789)
  ·
    refine ⟨42293482514966148555227023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225565240079819458961210789 42293482514966148555227023)
    ·
      refine ⟨63440223772449222832840535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42293482514966148555227023 63440223772449222832840535)
      ·
        refine ⟨95160335658673834249260803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63440223772449222832840535 95160335658673834249260803)
        ·
          refine ⟨142740503488010751373891205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95160335658673834249260803 142740503488010751373891205)
          ·
            refine ⟨26763844404002015882604601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142740503488010751373891205 26763844404002015882604601)
            ·
              refine ⟨20072883303001511911953451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26763844404002015882604601 20072883303001511911953451)
              ·
                refine ⟨30109324954502267867930177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20072883303001511911953451 30109324954502267867930177)
                ·
                  refine ⟨22581993715876700900947633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30109324954502267867930177 22581993715876700900947633)
                  ·
                    refine ⟨16936495286907525675710725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22581993715876700900947633 16936495286907525675710725)
                    ·
                      refine ⟨3175592866295161064195761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16936495286907525675710725 3175592866295161064195761)
                      ·
                        rfl

theorem cell23_6184445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_6184445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184445 prefixEnd_6184445 := by exact prefixLift 6184445
  have htrace : WordTrace (prefixWord ++ tailWord_6184445) baseStart_6184445 baseEnd_6184445 := by
    simpa [prefixWord, tailWord_6184445, baseEnd_6184445] using wordTrace_append hprefix tailTrace_6184445
  have hstable : (prefixWord ++ tailWord_6184445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184445).length < 2 ^ (prefixWord ++ tailWord_6184445).sum := by decide
  have hdescent : baseEnd_6184445 < baseStart_6184445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184455 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 7]
def baseStart_6184455 : Nat := 118140960795 + 6184455 * 2 ^ 59
def prefixEnd_6184455 : Nat := 4983230072969 + 3 ^ 40 * 6184455 * 2
def baseEnd_6184455 : Nat := 352844222344634002785635

theorem tailTrace_6184455 : CollatzResearch.WordTrace tailWord_6184455 prefixEnd_6184455 352844222344634002785635 := by
  unfold tailWord_6184455
  simp only [CollatzResearch.WordTrace]
  refine ⟨225565604809783230669074819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150377069873188820446049879 225565604809783230669074819)
  ·
    refine ⟨338348407214674846003612229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225565604809783230669074819 338348407214674846003612229)
    ·
      refine ⟨63440326352751533625677293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338348407214674846003612229 63440326352751533625677293)
      ·
        refine ⟨23790122382281825109628985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63440326352751533625677293 23790122382281825109628985)
        ·
          refine ⟨17842591786711368832221739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23790122382281825109628985 17842591786711368832221739)
          ·
            refine ⟨26763887680067053248332609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17842591786711368832221739 26763887680067053248332609)
            ·
              refine ⟨20072915760050289936249457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26763887680067053248332609 20072915760050289936249457)
              ·
                refine ⟨15054686820037717452187093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20072915760050289936249457 15054686820037717452187093)
                ·
                  refine ⟨352844222344634002785635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15054686820037717452187093 352844222344634002785635)
                  ·
                    rfl

theorem cell23_6184455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 7].length) (baseStart_6184455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184455 prefixEnd_6184455 := by exact prefixLift 6184455
  have htrace : WordTrace (prefixWord ++ tailWord_6184455) baseStart_6184455 baseEnd_6184455 := by
    simpa [prefixWord, tailWord_6184455, baseEnd_6184455] using wordTrace_append hprefix tailTrace_6184455
  have hstable : (prefixWord ++ tailWord_6184455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184455).length < 2 ^ (prefixWord ++ tailWord_6184455).sum := by decide
  have hdescent : baseEnd_6184455 < baseStart_6184455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184522 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4]
def baseStart_6184522 : Nat := 118140960795 + 6184522 * 2 ^ 59
def prefixEnd_6184522 : Nat := 4983230072969 + 3 ^ 40 * 6184522 * 2
def baseEnd_6184522 : Nat := 3175632404305557262932907

theorem tailTrace_6184522 : CollatzResearch.WordTrace tailWord_6184522 prefixEnd_6184522 3175632404305557262932907 := by
  unfold tailWord_6184522
  simp only [CollatzResearch.WordTrace]
  refine ⟨56392012125135125277940955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150378699000360334074509213 56392012125135125277940955)
  ·
    refine ⟨84588018187702687916911433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56392012125135125277940955 84588018187702687916911433)
    ·
      refine ⟨63441013640777015937683575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84588018187702687916911433 63441013640777015937683575)
      ·
        refine ⟨95161520461165523906525363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63441013640777015937683575 95161520461165523906525363)
        ·
          refine ⟨142742280691748285859788045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95161520461165523906525363 142742280691748285859788045)
          ·
            refine ⟨53528355259405607197420517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142742280691748285859788045 53528355259405607197420517)
            ·
              refine ⟨10036566611138551349516347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53528355259405607197420517 10036566611138551349516347)
              ·
                refine ⟨15054849916707827024274521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10036566611138551349516347 15054849916707827024274521)
                ·
                  refine ⟨11291137437530870268205891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15054849916707827024274521 11291137437530870268205891)
                  ·
                    refine ⟨16936706156296305402308837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11291137437530870268205891 16936706156296305402308837)
                    ·
                      refine ⟨3175632404305557262932907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16936706156296305402308837 3175632404305557262932907)
                      ·
                        rfl

theorem cell23_6184522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4].length) (baseStart_6184522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184522 prefixEnd_6184522 := by exact prefixLift 6184522
  have htrace : WordTrace (prefixWord ++ tailWord_6184522) baseStart_6184522 baseEnd_6184522 := by
    simpa [prefixWord, tailWord_6184522, baseEnd_6184522] using wordTrace_append hprefix tailTrace_6184522
  have hstable : (prefixWord ++ tailWord_6184522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184522).length < 2 ^ (prefixWord ++ tailWord_6184522).sum := by decide
  have hdescent : baseEnd_6184522 < baseStart_6184522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184562 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 6]
def baseStart_6184562 : Nat := 118140960795 + 6184562 * 2 ^ 59
def prefixEnd_6184562 : Nat := 4983230072969 + 3 ^ 40 * 6184562 * 2
def baseEnd_6184562 : Nat := 352850327059081900714747

theorem tailTrace_6184562 : CollatzResearch.WordTrace tailWord_6184562 prefixEnd_6184562 352850327059081900714747 := by
  unfold tailWord_6184562
  simp only [CollatzResearch.WordTrace]
  refine ⟨56392376855098896985804985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150379671613597058628813293 56392376855098896985804985)
  ·
    refine ⟨42294282641324172739353739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56392376855098896985804985 42294282641324172739353739)
    ·
      refine ⟨63441423961986259109030609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42294282641324172739353739 63441423961986259109030609)
      ·
        refine ⟨47581067971489694331772957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63441423961986259109030609 47581067971489694331772957)
        ·
          refine ⟨17842900489308635374414859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47581067971489694331772957 17842900489308635374414859)
          ·
            refine ⟨26764350733962953061622289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17842900489308635374414859 26764350733962953061622289)
            ·
              refine ⟨20073263050472214796216717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26764350733962953061622289 20073263050472214796216717)
              ·
                refine ⟨7527473643927080548581269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20073263050472214796216717 7527473643927080548581269)
                ·
                  refine ⟨352850327059081900714747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7527473643927080548581269 352850327059081900714747)
                  ·
                    rfl

theorem cell23_6184562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_6184562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184562 prefixEnd_6184562 := by exact prefixLift 6184562
  have htrace : WordTrace (prefixWord ++ tailWord_6184562) baseStart_6184562 baseEnd_6184562 := by
    simpa [prefixWord, tailWord_6184562, baseEnd_6184562] using wordTrace_append hprefix tailTrace_6184562
  have hstable : (prefixWord ++ tailWord_6184562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184562).length < 2 ^ (prefixWord ++ tailWord_6184562).sum := by decide
  have hdescent : baseEnd_6184562 < baseStart_6184562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184596 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 6]
def baseStart_6184596 : Nat := 118140960795 + 6184596 * 2 ^ 59
def prefixEnd_6184596 : Nat := 4983230072969 + 3 ^ 40 * 6184596 * 2
def baseEnd_6184596 : Nat := 352852266874887774823063

theorem tailTrace_6184596 : CollatzResearch.WordTrace tailWord_6184596 prefixEnd_6184596 352852266874887774823063 := by
  unfold tailWord_6184596
  simp only [CollatzResearch.WordTrace]
  refine ⟨112785373751136205874978821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150380498334848274499971761 112785373751136205874978821)
  ·
    refine ⟨21147257578338038601558529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112785373751136205874978821 21147257578338038601558529)
    ·
      refine ⟨15860443183753528951168897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21147257578338038601558529 15860443183753528951168897)
      ·
        refine ⟨11895332387815146713376673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15860443183753528951168897 11895332387815146713376673)
        ·
          refine ⟨8921499290861360035032505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11895332387815146713376673 8921499290861360035032505)
          ·
            refine ⟨6691124468146020026274379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921499290861360035032505 6691124468146020026274379)
            ·
              refine ⟨10036686702219030039411569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691124468146020026274379 10036686702219030039411569)
              ·
                refine ⟨7527515026664272529558677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036686702219030039411569 7527515026664272529558677)
                ·
                  refine ⟨352852266874887774823063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7527515026664272529558677 352852266874887774823063)
                  ·
                    rfl

theorem cell23_6184596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_6184596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184596 prefixEnd_6184596 := by exact prefixLift 6184596
  have htrace : WordTrace (prefixWord ++ tailWord_6184596) baseStart_6184596 baseEnd_6184596 := by
    simpa [prefixWord, tailWord_6184596, baseEnd_6184596] using wordTrace_append hprefix tailTrace_6184596
  have hstable : (prefixWord ++ tailWord_6184596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184596).length < 2 ^ (prefixWord ++ tailWord_6184596).sum := by decide
  have hdescent : baseEnd_6184596 < baseStart_6184596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184606 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_6184606 : Nat := 118140960795 + 6184606 * 2 ^ 59
def prefixEnd_6184606 : Nat := 4983230072969 + 3 ^ 40 * 6184606 * 2
def baseEnd_6184606 : Nat := 3175675536680534934282521

theorem tailTrace_6184606 : CollatzResearch.WordTrace tailWord_6184606 prefixEnd_6184606 3175675536680534934282521 := by
  unfold tailWord_6184606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28196389029029522932227709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150380741488157455638547781 28196389029029522932227709)
  ·
    refine ⟨10573645885886071099585391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28196389029029522932227709 10573645885886071099585391)
    ·
      refine ⟨15860468828829106649378087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10573645885886071099585391 15860468828829106649378087)
      ·
        refine ⟨23790703243243659974067131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15860468828829106649378087 23790703243243659974067131)
        ·
          refine ⟨35686054864865489961100697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23790703243243659974067131 35686054864865489961100697)
          ·
            refine ⟨26764541148649117470825523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35686054864865489961100697 26764541148649117470825523)
            ·
              refine ⟨40146811722973676206238285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26764541148649117470825523 40146811722973676206238285)
              ·
                refine ⟨15055054396115128577339357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40146811722973676206238285 15055054396115128577339357)
                ·
                  refine ⟨5645645398543173216502259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15055054396115128577339357 5645645398543173216502259)
                  ·
                    refine ⟨8468468097814759824753389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5645645398543173216502259 8468468097814759824753389)
                    ·
                      refine ⟨3175675536680534934282521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8468468097814759824753389 3175675536680534934282521)
                      ·
                        rfl

theorem cell23_6184606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_6184606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184606 prefixEnd_6184606 := by exact prefixLift 6184606
  have htrace : WordTrace (prefixWord ++ tailWord_6184606) baseStart_6184606 baseEnd_6184606 := by
    simpa [prefixWord, tailWord_6184606, baseEnd_6184606] using wordTrace_append hprefix tailTrace_6184606
  have hstable : (prefixWord ++ tailWord_6184606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184606).length < 2 ^ (prefixWord ++ tailWord_6184606).sum := by decide
  have hdescent : baseEnd_6184606 < baseStart_6184606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184632 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 3, 2, 3]
def baseStart_6184632 : Nat := 118140960795 + 6184632 * 2 ^ 59
def prefixEnd_6184632 : Nat := 4983230072969 + 3 ^ 40 * 6184632 * 2
def baseEnd_6184632 : Nat := 3175688887177551832557401

theorem tailTrace_6184632 : CollatzResearch.WordTrace tailWord_6184632 prefixEnd_6184632 3175688887177551832557401 := by
  unfold tailWord_6184632
  simp only [CollatzResearch.WordTrace]
  refine ⟨112786030265070994949134075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150381373686761326598845433 112786030265070994949134075)
  ·
    refine ⟨169179045397606492423701113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112786030265070994949134075 169179045397606492423701113)
    ·
      refine ⟨126884284048204869317775835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169179045397606492423701113 126884284048204869317775835)
      ·
        refine ⟨190326426072307303976663753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126884284048204869317775835 190326426072307303976663753)
        ·
          refine ⟨142744819554230477982497815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190326426072307303976663753 142744819554230477982497815)
          ·
            refine ⟨214117229331345716973746723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142744819554230477982497815 214117229331345716973746723)
            ·
              refine ⟨321175843997018575460620085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214117229331345716973746723 321175843997018575460620085)
              ·
                refine ⟨30110235374720491449433133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 321175843997018575460620085 30110235374720491449433133)
                ·
                  refine ⟨11291338265520184293537425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30110235374720491449433133 11291338265520184293537425)
                  ·
                    refine ⟨8468503699140138220153069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11291338265520184293537425 8468503699140138220153069)
                    ·
                      refine ⟨3175688887177551832557401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8468503699140138220153069 3175688887177551832557401)
                      ·
                        rfl

theorem cell23_6184632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_6184632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184632 prefixEnd_6184632 := by exact prefixLift 6184632
  have htrace : WordTrace (prefixWord ++ tailWord_6184632) baseStart_6184632 baseEnd_6184632 := by
    simpa [prefixWord, tailWord_6184632, baseEnd_6184632] using wordTrace_append hprefix tailTrace_6184632
  have hstable : (prefixWord ++ tailWord_6184632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184632).length < 2 ^ (prefixWord ++ tailWord_6184632).sum := by decide
  have hdescent : baseEnd_6184632 < baseStart_6184632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184673 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 2, 4]
def baseStart_6184673 : Nat := 118140960795 + 6184673 * 2 ^ 59
def prefixEnd_6184673 : Nat := 4983230072969 + 3 ^ 40 * 6184673 * 2
def baseEnd_6184673 : Nat := 1058569979961462057381571

theorem tailTrace_6184673 : CollatzResearch.WordTrace tailWord_6184673 prefixEnd_6184673 1058569979961462057381571 := by
  unfold tailWord_6184673
  simp only [CollatzResearch.WordTrace]
  refine ⟨225573555922993453900510673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150382370615328969267007115 225573555922993453900510673)
  ·
    refine ⟨169180166942245090425383005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225573555922993453900510673 169180166942245090425383005)
    ·
      refine ⟨63442562603341908909518627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169180166942245090425383005 63442562603341908909518627)
      ·
        refine ⟨95163843905012863364277941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63442562603341908909518627 95163843905012863364277941)
        ·
          refine ⟨8921610366094955940401057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95163843905012863364277941 8921610366094955940401057)
          ·
            refine ⟨6691207774571216955300793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921610366094955940401057 6691207774571216955300793)
            ·
              refine ⟨5018405830928412716475595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6691207774571216955300793 5018405830928412716475595)
              ·
                refine ⟨7527608746392619074713393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018405830928412716475595 7527608746392619074713393)
                ·
                  refine ⟨5645706559794464306035045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7527608746392619074713393 5645706559794464306035045)
                  ·
                    refine ⟨1058569979961462057381571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5645706559794464306035045 1058569979961462057381571)
                    ·
                      rfl

theorem cell23_6184673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_6184673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184673 prefixEnd_6184673 := by exact prefixLift 6184673
  have htrace : WordTrace (prefixWord ++ tailWord_6184673) baseStart_6184673 baseEnd_6184673 := by
    simpa [prefixWord, tailWord_6184673, baseEnd_6184673] using wordTrace_append hprefix tailTrace_6184673
  have hstable : (prefixWord ++ tailWord_6184673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184673).length < 2 ^ (prefixWord ++ tailWord_6184673).sum := by decide
  have hdescent : baseEnd_6184673 < baseStart_6184673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184712 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 2, 6]
def baseStart_6184712 : Nat := 118140960795 + 6184712 * 2 ^ 59
def prefixEnd_6184712 : Nat := 4983230072969 + 3 ^ 40 * 6184712 * 2
def baseEnd_6184712 : Nat := 1058576655209970506519011

theorem tailTrace_6184712 : CollatzResearch.WordTrace tailWord_6184712 prefixEnd_6184712 1058576655209970506519011 := by
  unfold tailWord_6184712
  simp only [CollatzResearch.WordTrace]
  refine ⟨112787489184926081780590195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150383318913234775707453593 112787489184926081780590195)
  ·
    refine ⟨169181233777389122670885293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112787489184926081780590195 169181233777389122670885293)
    ·
      refine ⟨63442962666520921001581985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169181233777389122670885293 63442962666520921001581985)
      ·
        refine ⟨47582221999890690751186489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63442962666520921001581985 47582221999890690751186489)
        ·
          refine ⟨35686666499918018063389867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47582221999890690751186489 35686666499918018063389867)
          ·
            refine ⟨53529999749877027095084801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35686666499918018063389867 53529999749877027095084801)
            ·
              refine ⟨40147499812407770321313601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53529999749877027095084801 40147499812407770321313601)
              ·
                refine ⟨30110624859305827740985201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40147499812407770321313601 30110624859305827740985201)
                ·
                  refine ⟨22582968644479370805738901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30110624859305827740985201 22582968644479370805738901)
                  ·
                    refine ⟨1058576655209970506519011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22582968644479370805738901 1058576655209970506519011)
                    ·
                      rfl

theorem cell23_6184712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_6184712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184712 prefixEnd_6184712 := by exact prefixLift 6184712
  have htrace : WordTrace (prefixWord ++ tailWord_6184712) baseStart_6184712 baseEnd_6184712 := by
    simpa [prefixWord, tailWord_6184712, baseEnd_6184712] using wordTrace_append hprefix tailTrace_6184712
  have hstable : (prefixWord ++ tailWord_6184712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184712).length < 2 ^ (prefixWord ++ tailWord_6184712).sum := by decide
  have hdescent : baseEnd_6184712 < baseStart_6184712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184736 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 1, 4, 2]
def baseStart_6184736 : Nat := 118140960795 + 6184736 * 2 ^ 59
def prefixEnd_6184736 : Nat := 4983230072969 + 3 ^ 40 * 6184736 * 2
def baseEnd_6184736 : Nat := 3175742289165619425656923

theorem tailTrace_6184736 : CollatzResearch.WordTrace tailWord_6184736 prefixEnd_6184736 3175742289165619425656923 := by
  unfold tailWord_6184736
  simp only [CollatzResearch.WordTrace]
  refine ⟨112787926860882607830027031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150383902481176810440036041 112787926860882607830027031)
  ·
    refine ⟨169181890291323911745040547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112787926860882607830027031 169181890291323911745040547)
    ·
      refine ⟨253772835436985867617560821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169181890291323911745040547 253772835436985867617560821)
      ·
        refine ⟨23791203322217425089146327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253772835436985867617560821 23791203322217425089146327)
        ·
          refine ⟨35686804983326137633719491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23791203322217425089146327 35686804983326137633719491)
          ·
            refine ⟨53530207474989206450579237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35686804983326137633719491 53530207474989206450579237)
            ·
              refine ⟨10036913901560476209483607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53530207474989206450579237 10036913901560476209483607)
              ·
                refine ⟨15055370852340714314225411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10036913901560476209483607 15055370852340714314225411)
                ·
                  refine ⟨22583056278511071471338117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15055370852340714314225411 22583056278511071471338117)
                  ·
                    refine ⟨4234323052220825900875897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22583056278511071471338117 4234323052220825900875897)
                    ·
                      refine ⟨3175742289165619425656923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234323052220825900875897 3175742289165619425656923)
                      ·
                        rfl

theorem cell23_6184736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_6184736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184736 prefixEnd_6184736 := by exact prefixLift 6184736
  have htrace : WordTrace (prefixWord ++ tailWord_6184736) baseStart_6184736 baseEnd_6184736 := by
    simpa [prefixWord, tailWord_6184736, baseEnd_6184736] using wordTrace_append hprefix tailTrace_6184736
  have hstable : (prefixWord ++ tailWord_6184736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184736).length < 2 ^ (prefixWord ++ tailWord_6184736).sum := by decide
  have hdescent : baseEnd_6184736 < baseStart_6184736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184757 : List Nat := [1, 3, 3, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_6184757 : Nat := 118140960795 + 6184757 * 2 ^ 59
def prefixEnd_6184757 : Nat := 4983230072969 + 3 ^ 40 * 6184757 * 2
def baseEnd_6184757 : Nat := 3175753072259363843494327

theorem tailTrace_6184757 : CollatzResearch.WordTrace tailWord_6184757 prefixEnd_6184757 3175753072259363843494327 := by
  unfold tailWord_6184757
  simp only [CollatzResearch.WordTrace]
  refine ⟨225576619654689136246568525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150384413103126090831045683 225576619654689136246568525)
  ·
    refine ⟨84591232370508426092463197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225576619654689136246568525 84591232370508426092463197)
    ·
      refine ⟨31721712138940659784673699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84591232370508426092463197 31721712138940659784673699)
      ·
        refine ⟨47582568208410989677010549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31721712138940659784673699 47582568208410989677010549)
        ·
          refine ⟨4460865769538530282219739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47582568208410989677010549 4460865769538530282219739)
          ·
            refine ⟨6691298654307795423329609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460865769538530282219739 6691298654307795423329609)
            ·
              refine ⟨5018473990730846567497207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6691298654307795423329609 5018473990730846567497207)
              ·
                refine ⟨7527710986096269851245811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018473990730846567497207 7527710986096269851245811)
                ·
                  refine ⟨11291566479144404776868717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7527710986096269851245811 11291566479144404776868717)
                  ·
                    refine ⟨4234337429679151791325769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11291566479144404776868717 4234337429679151791325769)
                    ·
                      refine ⟨3175753072259363843494327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234337429679151791325769 3175753072259363843494327)
                      ·
                        rfl

theorem cell23_6184757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_6184757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184757 prefixEnd_6184757 := by exact prefixLift 6184757
  have htrace : WordTrace (prefixWord ++ tailWord_6184757) baseStart_6184757 baseEnd_6184757 := by
    simpa [prefixWord, tailWord_6184757, baseEnd_6184757] using wordTrace_append hprefix tailTrace_6184757
  have hstable : (prefixWord ++ tailWord_6184757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184757).length < 2 ^ (prefixWord ++ tailWord_6184757).sum := by decide
  have hdescent : baseEnd_6184757 < baseStart_6184757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184809 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 1, 6, 2]
def baseStart_6184809 : Nat := 118140960795 + 6184809 * 2 ^ 59
def prefixEnd_6184809 : Nat := 4983230072969 + 3 ^ 40 * 6184809 * 2
def baseEnd_6184809 : Nat := 3175779773253397640044087

theorem tailTrace_6184809 : CollatzResearch.WordTrace tailWord_6184809 prefixEnd_6184809 3175779773253397640044087 := by
  unfold tailWord_6184809
  simp only [CollatzResearch.WordTrace]
  refine ⟨225578516250500749127461481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150385677500333832751640987 225578516250500749127461481)
  ·
    refine ⟨169183887187875561845596111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225578516250500749127461481 169183887187875561845596111)
    ·
      refine ⟨253775830781813342768394167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169183887187875561845596111 253775830781813342768394167)
      ·
        refine ⟨380663746172720014152591251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253775830781813342768394167 380663746172720014152591251)
        ·
          refine ⟨570995619259080021228886877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380663746172720014152591251 570995619259080021228886877)
          ·
            refine ⟨214123357222155007960832579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 570995619259080021228886877 214123357222155007960832579)
            ·
              refine ⟨321185035833232511941248869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214123357222155007960832579 321185035833232511941248869)
              ·
                refine ⟨60222194218731095988984163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321185035833232511941248869 60222194218731095988984163)
                ·
                  refine ⟨90333291328096643983476245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60222194218731095988984163 90333291328096643983476245)
                  ·
                    refine ⟨4234373031004530186725449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90333291328096643983476245 4234373031004530186725449)
                    ·
                      refine ⟨3175779773253397640044087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234373031004530186725449 3175779773253397640044087)
                      ·
                        rfl

theorem cell23_6184809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 6, 2].length) (baseStart_6184809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184809 prefixEnd_6184809 := by exact prefixLift 6184809
  have htrace : WordTrace (prefixWord ++ tailWord_6184809) baseStart_6184809 baseEnd_6184809 := by
    simpa [prefixWord, tailWord_6184809, baseEnd_6184809] using wordTrace_append hprefix tailTrace_6184809
  have hstable : (prefixWord ++ tailWord_6184809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184809).length < 2 ^ (prefixWord ++ tailWord_6184809).sum := by decide
  have hdescent : baseEnd_6184809 < baseStart_6184809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184810 : List Nat := [3, 1, 3, 4, 1, 2, 1, 3, 5]
def baseStart_6184810 : Nat := 118140960795 + 6184810 * 2 ^ 59
def prefixEnd_6184810 : Nat := 4983230072969 + 3 ^ 40 * 6184810 * 2
def baseEnd_6184810 : Nat := 352864476303783570681287

theorem tailTrace_6184810 : CollatzResearch.WordTrace tailWord_6184810 prefixEnd_6184810 352864476303783570681287 := by
  unfold tailWord_6184810
  simp only [CollatzResearch.WordTrace]
  refine ⟨56394638180874281574561971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150385701815664750865498589 56394638180874281574561971)
  ·
    refine ⟨84591957271311422361842957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56394638180874281574561971 84591957271311422361842957)
    ·
      refine ⟨31721983976741783385691109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84591957271311422361842957 31721983976741783385691109)
      ·
        refine ⟨5947871995639084384817083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31721983976741783385691109 5947871995639084384817083)
        ·
          refine ⟨8921807993458626577225625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947871995639084384817083 8921807993458626577225625)
          ·
            refine ⟨6691355995093969932919219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8921807993458626577225625 6691355995093969932919219)
            ·
              refine ⟨10037033992640954899378829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691355995093969932919219 10037033992640954899378829)
              ·
                refine ⟨3763887747240358087267061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10037033992640954899378829 3763887747240358087267061)
                ·
                  refine ⟨352864476303783570681287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3763887747240358087267061 352864476303783570681287)
                  ·
                    rfl

theorem cell23_6184810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_6184810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184810 prefixEnd_6184810 := by exact prefixLift 6184810
  have htrace : WordTrace (prefixWord ++ tailWord_6184810) baseStart_6184810 baseEnd_6184810 := by
    simpa [prefixWord, tailWord_6184810, baseEnd_6184810] using wordTrace_append hprefix tailTrace_6184810
  have hstable : (prefixWord ++ tailWord_6184810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184810).length < 2 ^ (prefixWord ++ tailWord_6184810).sum := by decide
  have hdescent : baseEnd_6184810 < baseStart_6184810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184832 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 8]
def baseStart_6184832 : Nat := 118140960795 + 6184832 * 2 ^ 59
def prefixEnd_6184832 : Nat := 4983230072969 + 3 ^ 40 * 6184832 * 2
def baseEnd_6184832 : Nat := 352865731478716783339609

theorem tailTrace_6184832 : CollatzResearch.WordTrace tailWord_6184832 prefixEnd_6184832 352865731478716783339609 := by
  unfold tailWord_6184832
  simp only [CollatzResearch.WordTrace]
  refine ⟨112789677564708712027774375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150386236752944949370365833 112789677564708712027774375)
  ·
    refine ⟨169184516347063068041661563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112789677564708712027774375 169184516347063068041661563)
    ·
      refine ⟨253776774520594602062492345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169184516347063068041661563 253776774520594602062492345)
      ·
        refine ⟨190332580890445951546869259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253776774520594602062492345 190332580890445951546869259)
        ·
          refine ⟨285498871335668927320303889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190332580890445951546869259 285498871335668927320303889)
          ·
            refine ⟨214124153501751695490227917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285498871335668927320303889 214124153501751695490227917)
            ·
              refine ⟨80296557563156885808835469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214124153501751695490227917 80296557563156885808835469)
              ·
                refine ⟨30111209086183832178313301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80296557563156885808835469 30111209086183832178313301)
                ·
                  refine ⟨352865731478716783339609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30111209086183832178313301 352865731478716783339609)
                  ·
                    rfl

theorem cell23_6184832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_6184832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184832 prefixEnd_6184832 := by exact prefixLift 6184832
  have htrace : WordTrace (prefixWord ++ tailWord_6184832) baseStart_6184832 baseEnd_6184832 := by
    simpa [prefixWord, tailWord_6184832, baseEnd_6184832] using wordTrace_append hprefix tailTrace_6184832
  have hstable : (prefixWord ++ tailWord_6184832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184832).length < 2 ^ (prefixWord ++ tailWord_6184832).sum := by decide
  have hdescent : baseEnd_6184832 < baseStart_6184832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184836 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_6184836 : Nat := 118140960795 + 6184836 * 2 ^ 59
def prefixEnd_6184836 : Nat := 4983230072969 + 3 ^ 40 * 6184836 * 2
def baseEnd_6184836 : Nat := 1058597879077023011468821

theorem tailTrace_6184836 : CollatzResearch.WordTrace tailWord_6184836 prefixEnd_6184836 1058597879077023011468821 := by
  unfold tailWord_6184836
  simp only [CollatzResearch.WordTrace]
  refine ⟨112789750510701466369347181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150386334014268621825796241 112789750510701466369347181)
  ·
    refine ⟨42296156441513049888505193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112789750510701466369347181 42296156441513049888505193)
    ·
      refine ⟨31722117331134787416378895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42296156441513049888505193 31722117331134787416378895)
      ·
        refine ⟨47583175996702181124568343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31722117331134787416378895 47583175996702181124568343)
        ·
          refine ⟨71374763995053271686852515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47583175996702181124568343 71374763995053271686852515)
          ·
            refine ⟨107062145992579907530278773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71374763995053271686852515 107062145992579907530278773)
            ·
              refine ⟨10037076186804366330963635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107062145992579907530278773 10037076186804366330963635)
              ·
                refine ⟨15055614280206549496445453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10037076186804366330963635 15055614280206549496445453)
                ·
                  refine ⟨5645855355077456061167045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15055614280206549496445453 5645855355077456061167045)
                  ·
                    refine ⟨1058597879077023011468821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5645855355077456061167045 1058597879077023011468821)
                    ·
                      rfl

theorem cell23_6184836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_6184836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184836 prefixEnd_6184836 := by exact prefixLift 6184836
  have htrace : WordTrace (prefixWord ++ tailWord_6184836) baseStart_6184836 baseEnd_6184836 := by
    simpa [prefixWord, tailWord_6184836, baseEnd_6184836] using wordTrace_append hprefix tailTrace_6184836
  have hstable : (prefixWord ++ tailWord_6184836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184836).length < 2 ^ (prefixWord ++ tailWord_6184836).sum := by decide
  have hdescent : baseEnd_6184836 < baseStart_6184836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184863 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 3]
def baseStart_6184863 : Nat := 118140960795 + 6184863 * 2 ^ 59
def prefixEnd_6184863 : Nat := 4983230072969 + 3 ^ 40 * 6184863 * 2
def baseEnd_6184863 : Nat := 3175807501208740428768839

theorem tailTrace_6184863 : CollatzResearch.WordTrace tailWord_6184863 prefixEnd_6184863 3175807501208740428768839 := by
  unfold tailWord_6184863
  simp only [CollatzResearch.WordTrace]
  refine ⟨225580485792305116349927243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150386990528203410899951495 225580485792305116349927243)
  ·
    refine ⟨338370728688457674524890865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225580485792305116349927243 338370728688457674524890865)
    ·
      refine ⟨253778046516343255893668149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338370728688457674524890865 253778046516343255893668149)
      ·
        refine ⟨23791691860907180240031389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253778046516343255893668149 23791691860907180240031389)
        ·
          refine ⟨8921884447840192590011771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23791691860907180240031389 8921884447840192590011771)
          ·
            refine ⟨13382826671760288885017657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8921884447840192590011771 13382826671760288885017657)
            ·
              refine ⟨10037120003820216663763243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13382826671760288885017657 10037120003820216663763243)
              ·
                refine ⟨15055680005730324995644865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10037120003820216663763243 15055680005730324995644865)
                ·
                  refine ⟨11291760004297743746733649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15055680005730324995644865 11291760004297743746733649)
                  ·
                    refine ⟨8468820003223307810050237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11291760004297743746733649 8468820003223307810050237)
                    ·
                      refine ⟨3175807501208740428768839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8468820003223307810050237 3175807501208740428768839)
                      ·
                        rfl

theorem cell23_6184863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_6184863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184863 prefixEnd_6184863 := by exact prefixLift 6184863
  have htrace : WordTrace (prefixWord ++ tailWord_6184863) baseStart_6184863 baseEnd_6184863 := by
    simpa [prefixWord, tailWord_6184863, baseEnd_6184863] using wordTrace_append hprefix tailTrace_6184863
  have hstable : (prefixWord ++ tailWord_6184863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184863).length < 2 ^ (prefixWord ++ tailWord_6184863).sum := by decide
  have hdescent : baseEnd_6184863 < baseStart_6184863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184916 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6184916 : Nat := 118140960795 + 6184916 * 2 ^ 59
def prefixEnd_6184916 : Nat := 4983230072969 + 3 ^ 40 * 6184916 * 2
def baseEnd_6184916 : Nat := 3175834715683428721406095

theorem tailTrace_6184916 : CollatzResearch.WordTrace tailWord_6184916 prefixEnd_6184916 3175834715683428721406095 := by
  unfold tailWord_6184916
  simp only [CollatzResearch.WordTrace]
  refine ⟨112791209430556553200803301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150388279240742070934404401 112791209430556553200803301)
  ·
    refine ⟨21148351768229353725150619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112791209430556553200803301 21148351768229353725150619)
    ·
      refine ⟨31722527652344030587725929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21148351768229353725150619 31722527652344030587725929)
      ·
        refine ⟨23791895739258022940794447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31722527652344030587725929 23791895739258022940794447)
        ·
          refine ⟨35687843608887034411191671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23791895739258022940794447 35687843608887034411191671)
          ·
            refine ⟨53531765413330551616787507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35687843608887034411191671 53531765413330551616787507)
            ·
              refine ⟨80297648119995827425181261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53531765413330551616787507 80297648119995827425181261)
              ·
                refine ⟨30111618044998435284442973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80297648119995827425181261 30111618044998435284442973)
                ·
                  refine ⟨11291856766874413231666115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30111618044998435284442973 11291856766874413231666115)
                  ·
                    refine ⟨16937785150311619847499173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11291856766874413231666115 16937785150311619847499173)
                    ·
                      refine ⟨3175834715683428721406095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16937785150311619847499173 3175834715683428721406095)
                      ·
                        rfl

theorem cell23_6184916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6184916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184916 prefixEnd_6184916 := by exact prefixLift 6184916
  have htrace : WordTrace (prefixWord ++ tailWord_6184916) baseStart_6184916 baseEnd_6184916 := by
    simpa [prefixWord, tailWord_6184916, baseEnd_6184916] using wordTrace_append hprefix tailTrace_6184916
  have hstable : (prefixWord ++ tailWord_6184916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184916).length < 2 ^ (prefixWord ++ tailWord_6184916).sum := by decide
  have hdescent : baseEnd_6184916 < baseStart_6184916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184930 : List Nat := [3, 3, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6184930 : Nat := 118140960795 + 6184930 * 2 ^ 59
def prefixEnd_6184930 : Nat := 4983230072969 + 3 ^ 40 * 6184930 * 2
def baseEnd_6184930 : Nat := 1058613968137530555543677

theorem tailTrace_6184930 : CollatzResearch.WordTrace tailWord_6184930 prefixEnd_6184930 1058613968137530555543677 := by
  unfold tailWord_6184930
  simp only [CollatzResearch.WordTrace]
  refine ⟨56395732370765596698154061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150388619655374924528410829 56395732370765596698154061)
  ·
    refine ⟨21148399639037098761807773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56395732370765596698154061 21148399639037098761807773)
    ·
      refine ⟨7930649864638912035677915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21148399639037098761807773 7930649864638912035677915)
      ·
        refine ⟨11895974796958368053516873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7930649864638912035677915 11895974796958368053516873)
        ·
          refine ⟨8921981097718776040137655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11895974796958368053516873 8921981097718776040137655)
          ·
            refine ⟨13382971646578164060206483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8921981097718776040137655 13382971646578164060206483)
            ·
              refine ⟨20074457469867246090309725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13382971646578164060206483 20074457469867246090309725)
              ·
                refine ⟨7527921551200217283866147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20074457469867246090309725 7527921551200217283866147)
                ·
                  refine ⟨11291882326800325925799221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7527921551200217283866147 11291882326800325925799221)
                  ·
                    refine ⟨1058613968137530555543677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11291882326800325925799221 1058613968137530555543677)
                    ·
                      rfl

theorem cell23_6184930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6184930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184930 prefixEnd_6184930 := by exact prefixLift 6184930
  have htrace : WordTrace (prefixWord ++ tailWord_6184930) baseStart_6184930 baseEnd_6184930 := by
    simpa [prefixWord, tailWord_6184930, baseEnd_6184930] using wordTrace_append hprefix tailTrace_6184930
  have hstable : (prefixWord ++ tailWord_6184930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184930).length < 2 ^ (prefixWord ++ tailWord_6184930).sum := by decide
  have hdescent : baseEnd_6184930 < baseStart_6184930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184970 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3]
def baseStart_6184970 : Nat := 118140960795 + 6184970 * 2 ^ 59
def prefixEnd_6184970 : Nat := 4983230072969 + 3 ^ 40 * 6184970 * 2
def baseEnd_6184970 : Nat := 3175862443638771510130847

theorem tailTrace_6184970 : CollatzResearch.WordTrace tailWord_6184970 prefixEnd_6184970 3175862443638771510130847 := by
  unfold tailWord_6184970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56396097100729368406018091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150389592268611649082714909 56396097100729368406018091)
  ·
    refine ⟨84594145651094052609027137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56396097100729368406018091 84594145651094052609027137)
    ·
      refine ⟨63445609238320539456770353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84594145651094052609027137 63445609238320539456770353)
      ·
        refine ⟨47584206928740404592577765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63445609238320539456770353 47584206928740404592577765)
        ·
          refine ⟨8922038799138825861108331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47584206928740404592577765 8922038799138825861108331)
          ·
            refine ⟨13383058198708238791662497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8922038799138825861108331 13383058198708238791662497)
            ·
              refine ⟨10037293649031179093746873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13383058198708238791662497 10037293649031179093746873)
              ·
                refine ⟨7527970236773384320310155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10037293649031179093746873 7527970236773384320310155)
                ·
                  refine ⟨11291955355160076480465233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7527970236773384320310155 11291955355160076480465233)
                  ·
                    refine ⟨8468966516370057360348925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11291955355160076480465233 8468966516370057360348925)
                    ·
                      refine ⟨3175862443638771510130847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8468966516370057360348925 3175862443638771510130847)
                      ·
                        rfl

theorem cell23_6184970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_6184970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184970 prefixEnd_6184970 := by exact prefixLift 6184970
  have htrace : WordTrace (prefixWord ++ tailWord_6184970) baseStart_6184970 baseEnd_6184970 := by
    simpa [prefixWord, tailWord_6184970, baseEnd_6184970] using wordTrace_append hprefix tailTrace_6184970
  have hstable : (prefixWord ++ tailWord_6184970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184970).length < 2 ^ (prefixWord ++ tailWord_6184970).sum := by decide
  have hdescent : baseEnd_6184970 < baseStart_6184970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6184979 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5]
def baseStart_6184979 : Nat := 118140960795 + 6184979 * 2 ^ 59
def prefixEnd_6184979 : Nat := 4983230072969 + 3 ^ 40 * 6184979 * 2
def baseEnd_6184979 : Nat := 3175867064964661974918305

theorem tailTrace_6184979 : CollatzResearch.WordTrace tailWord_6184979 prefixEnd_6184979 3175867064964661974918305 := by
  unfold tailWord_6184979
  simp only [CollatzResearch.WordTrace]
  refine ⟨225584716659884868161149991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150389811106589912107433327 225584716659884868161149991)
  ·
    refine ⟨338377074989827302241724987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225584716659884868161149991 338377074989827302241724987)
    ·
      refine ⟨507565612484740953362587481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338377074989827302241724987 507565612484740953362587481)
      ·
        refine ⟨380674209363555715021940611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507565612484740953362587481 380674209363555715021940611)
        ·
          refine ⟨571011314045333572532910917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380674209363555715021940611 571011314045333572532910917)
          ·
            refine ⟨107064621383500044849920797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 571011314045333572532910917 107064621383500044849920797)
            ·
              refine ⟨40149233018812516818720299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107064621383500044849920797 40149233018812516818720299)
              ·
                refine ⟨60223849528218775228080449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40149233018812516818720299 60223849528218775228080449)
                ·
                  refine ⟨45167887146164081421060337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60223849528218775228080449 45167887146164081421060337)
                  ·
                    refine ⟨33875915359623061065795253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45167887146164081421060337 33875915359623061065795253)
                    ·
                      refine ⟨3175867064964661974918305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33875915359623061065795253 3175867064964661974918305)
                      ·
                        rfl

theorem cell23_6184979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_6184979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6184979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6184979 prefixEnd_6184979 := by exact prefixLift 6184979
  have htrace : WordTrace (prefixWord ++ tailWord_6184979) baseStart_6184979 baseEnd_6184979 := by
    simpa [prefixWord, tailWord_6184979, baseEnd_6184979] using wordTrace_append hprefix tailTrace_6184979
  have hstable : (prefixWord ++ tailWord_6184979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6184979).length < 2 ^ (prefixWord ++ tailWord_6184979).sum := by decide
  have hdescent : baseEnd_6184979 < baseStart_6184979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6184979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185029 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 9]
def baseStart_6185029 : Nat := 118140960795 + 6185029 * 2 ^ 59
def prefixEnd_6185029 : Nat := 4983230072969 + 3 ^ 40 * 6185029 * 2
def baseEnd_6185029 : Nat := 352876970999709642143675

theorem tailTrace_6185029 : CollatzResearch.WordTrace tailWord_6185029 prefixEnd_6185029 352876970999709642143675 := by
  unfold tailWord_6185029
  simp only [CollatzResearch.WordTrace]
  refine ⟨225586540309703726700470141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150391026873135817800313427 225586540309703726700470141)
  ·
    refine ⟨84594952616138897512676303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225586540309703726700470141 84594952616138897512676303)
    ·
      refine ⟨126892428924208346269014455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84594952616138897512676303 126892428924208346269014455)
      ·
        refine ⟨190338643386312519403521683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126892428924208346269014455 190338643386312519403521683)
        ·
          refine ⟨285507965079468779105282525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190338643386312519403521683 285507965079468779105282525)
          ·
            refine ⟨107065486904800792164480947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285507965079468779105282525 107065486904800792164480947)
            ·
              refine ⟨160598230357201188246721421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107065486904800792164480947 160598230357201188246721421)
              ·
                refine ⟨60224336383950445592520533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160598230357201188246721421 60224336383950445592520533)
                ·
                  refine ⟨352876970999709642143675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60224336383950445592520533 352876970999709642143675)
                  ·
                    rfl

theorem cell23_6185029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_6185029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185029 prefixEnd_6185029 := by exact prefixLift 6185029
  have htrace : WordTrace (prefixWord ++ tailWord_6185029) baseStart_6185029 baseEnd_6185029 := by
    simpa [prefixWord, tailWord_6185029, baseEnd_6185029] using wordTrace_append hprefix tailTrace_6185029
  have hstable : (prefixWord ++ tailWord_6185029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185029).length < 2 ^ (prefixWord ++ tailWord_6185029).sum := by decide
  have hdescent : baseEnd_6185029 < baseStart_6185029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185063 : List Nat := [1, 1, 5, 1, 1, 2, 3, 4, 5]
def baseStart_6185063 : Nat := 118140960795 + 6185063 * 2 ^ 59
def prefixEnd_6185063 : Nat := 4983230072969 + 3 ^ 40 * 6185063 * 2
def baseEnd_6185063 : Nat := 352878910815515516251991

theorem tailTrace_6185063 : CollatzResearch.WordTrace tailWord_6185063 prefixEnd_6185063 352878910815515516251991 := by
  unfold tailWord_6185063
  simp only [CollatzResearch.WordTrace]
  refine ⟨225587780391580550507207843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150391853594387033671471895 225587780391580550507207843)
  ·
    refine ⟨338381670587370825760811765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225587780391580550507207843 338381670587370825760811765)
    ·
      refine ⟨31723281617566014915076103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 338381670587370825760811765 31723281617566014915076103)
      ·
        refine ⟨47584922426349022372614155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31723281617566014915076103 47584922426349022372614155)
        ·
          refine ⟨71377383639523533558921233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47584922426349022372614155 71377383639523533558921233)
          ·
            refine ⟨53533037729642650169190925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71377383639523533558921233 53533037729642650169190925)
            ·
              refine ⟨20074889148615993813446597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53533037729642650169190925 20074889148615993813446597)
              ·
                refine ⟨3764041715365498840021237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20074889148615993813446597 3764041715365498840021237)
                ·
                  refine ⟨352878910815515516251991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3764041715365498840021237 352878910815515516251991)
                  ·
                    rfl

theorem cell23_6185063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 5].length) (baseStart_6185063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185063 prefixEnd_6185063 := by exact prefixLift 6185063
  have htrace : WordTrace (prefixWord ++ tailWord_6185063) baseStart_6185063 baseEnd_6185063 := by
    simpa [prefixWord, tailWord_6185063, baseEnd_6185063] using wordTrace_append hprefix tailTrace_6185063
  have hstable : (prefixWord ++ tailWord_6185063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185063).length < 2 ^ (prefixWord ++ tailWord_6185063).sum := by decide
  have hdescent : baseEnd_6185063 < baseStart_6185063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185093 : List Nat := [1, 3, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_6185093 : Nat := 118140960795 + 6185093 * 2 ^ 59
def prefixEnd_6185093 : Nat := 4983230072969 + 3 ^ 40 * 6185093 * 2
def baseEnd_6185093 : Nat := 1058641867253091509630927

theorem tailTrace_6185093 : CollatzResearch.WordTrace tailWord_6185093 prefixEnd_6185093 1058641867253091509630927 := by
  unfold tailWord_6185093
  simp only [CollatzResearch.WordTrace]
  refine ⟨225588874581471865630799933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150392583054314577087199955 225588874581471865630799933)
  ·
    refine ⟨84595827968051949611549975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225588874581471865630799933 84595827968051949611549975)
    ·
      refine ⟨126893741952077924417324963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84595827968051949611549975 126893741952077924417324963)
      ·
        refine ⟨190340612928116886625987445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126893741952077924417324963 190340612928116886625987445)
        ·
          refine ⟨17844432462010958121186323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190340612928116886625987445 17844432462010958121186323)
          ·
            refine ⟨26766648693016437181779485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17844432462010958121186323 26766648693016437181779485)
            ·
              refine ⟨10037493259881163943167307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26766648693016437181779485 10037493259881163943167307)
              ·
                refine ⟨15056239889821745914750961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10037493259881163943167307 15056239889821745914750961)
                ·
                  refine ⟨11292179917366309436063221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15056239889821745914750961 11292179917366309436063221)
                  ·
                    refine ⟨1058641867253091509630927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11292179917366309436063221 1058641867253091509630927)
                    ·
                      rfl

theorem cell23_6185093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_6185093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185093 prefixEnd_6185093 := by exact prefixLift 6185093
  have htrace : WordTrace (prefixWord ++ tailWord_6185093) baseStart_6185093 baseEnd_6185093 := by
    simpa [prefixWord, tailWord_6185093, baseEnd_6185093] using wordTrace_append hprefix tailTrace_6185093
  have hstable : (prefixWord ++ tailWord_6185093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185093).length < 2 ^ (prefixWord ++ tailWord_6185093).sum := by decide
  have hdescent : baseEnd_6185093 < baseStart_6185093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185108 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6185108 : Nat := 118140960795 + 6185108 * 2 ^ 59
def prefixEnd_6185108 : Nat := 4983230072969 + 3 ^ 40 * 6185108 * 2
def baseEnd_6185108 : Nat := 3175933303969091970205213

theorem tailTrace_6185108 : CollatzResearch.WordTrace tailWord_6185108 prefixEnd_6185108 3175933303969091970205213 := by
  unfold tailWord_6185108
  simp only [CollatzResearch.WordTrace]
  refine ⟨112794710838208761596297989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150392947784278348795063985 112794710838208761596297989)
  ·
    refine ⟨21149008282164142799305873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112794710838208761596297989 21149008282164142799305873)
    ·
      refine ⟨15861756211623107099479405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21149008282164142799305873 15861756211623107099479405)
      ·
        refine ⟨5948158579358665162304777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15861756211623107099479405 5948158579358665162304777)
        ·
          refine ⟨4461118934518998871728583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5948158579358665162304777 4461118934518998871728583)
          ·
            refine ⟨6691678401778498307592875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461118934518998871728583 6691678401778498307592875)
            ·
              refine ⟨10037517602667747461389313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691678401778498307592875 10037517602667747461389313)
              ·
                refine ⟨7528138202000810596041985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10037517602667747461389313 7528138202000810596041985)
                ·
                  refine ⟨5646103651500607947031489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7528138202000810596041985 5646103651500607947031489)
                  ·
                    refine ⟨4234577738625455960273617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5646103651500607947031489 4234577738625455960273617)
                    ·
                      refine ⟨3175933303969091970205213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234577738625455960273617 3175933303969091970205213)
                      ·
                        rfl

theorem cell23_6185108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6185108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185108 prefixEnd_6185108 := by exact prefixLift 6185108
  have htrace : WordTrace (prefixWord ++ tailWord_6185108) baseStart_6185108 baseEnd_6185108 := by
    simpa [prefixWord, tailWord_6185108, baseEnd_6185108] using wordTrace_append hprefix tailTrace_6185108
  have hstable : (prefixWord ++ tailWord_6185108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185108).length < 2 ^ (prefixWord ++ tailWord_6185108).sum := by decide
  have hdescent : baseEnd_6185108 < baseStart_6185108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185174 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_6185174 : Nat := 118140960795 + 6185174 * 2 ^ 59
def prefixEnd_6185174 : Nat := 4983230072969 + 3 ^ 40 * 6185174 * 2
def baseEnd_6185174 : Nat := 1058655731230762903993303

theorem tailTrace_6185174 : CollatzResearch.WordTrace tailWord_6185174 prefixEnd_6185174 1058655731230762903993303 := by
  unfold tailWord_6185174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14099489305886151029031161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150394552596118944309665717 14099489305886151029031161)
  ·
    refine ⟨10574616979414613271773371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14099489305886151029031161 10574616979414613271773371)
    ·
      refine ⟨15861925469121919907660057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10574616979414613271773371 15861925469121919907660057)
      ·
        refine ⟨11896444101841439930745043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15861925469121919907660057 11896444101841439930745043)
        ·
          refine ⟨17844666152762159896117565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11896444101841439930745043 17844666152762159896117565)
          ·
            refine ⟨6691749807285809961044087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17844666152762159896117565 6691749807285809961044087)
            ·
              refine ⟨10037624710928714941566131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691749807285809961044087 10037624710928714941566131)
              ·
                refine ⟨15056437066393072412349197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10037624710928714941566131 15056437066393072412349197)
                ·
                  refine ⟨5646163899897402154630949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15056437066393072412349197 5646163899897402154630949)
                  ·
                    refine ⟨1058655731230762903993303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646163899897402154630949 1058655731230762903993303)
                    ·
                      rfl

theorem cell23_6185174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_6185174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185174 prefixEnd_6185174 := by exact prefixLift 6185174
  have htrace : WordTrace (prefixWord ++ tailWord_6185174) baseStart_6185174 baseEnd_6185174 := by
    simpa [prefixWord, tailWord_6185174, baseEnd_6185174] using wordTrace_append hprefix tailTrace_6185174
  have hstable : (prefixWord ++ tailWord_6185174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185174).length < 2 ^ (prefixWord ++ tailWord_6185174).sum := by decide
  have hdescent : baseEnd_6185174 < baseStart_6185174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185203 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 4]
def baseStart_6185203 : Nat := 118140960795 + 6185203 * 2 ^ 59
def prefixEnd_6185203 : Nat := 4983230072969 + 3 ^ 40 * 6185203 * 2
def baseEnd_6185203 : Nat := 3175982084631269098517275

theorem tailTrace_6185203 : CollatzResearch.WordTrace tailWord_6185203 prefixEnd_6185203 3175982084631269098517275 := by
  unfold tailWord_6185203
  simp only [CollatzResearch.WordTrace]
  refine ⟨225592886611073354417304263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150395257740715569611536175 225592886611073354417304263)
  ·
    refine ⟨338389329916610031625956395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225592886611073354417304263 338389329916610031625956395)
    ·
      refine ⟨507583994874915047438934593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338389329916610031625956395 507583994874915047438934593)
      ·
        refine ⟨380687996156186285579200945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507583994874915047438934593 380687996156186285579200945)
        ·
          refine ⟨285515997117139714184400709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380687996156186285579200945 285515997117139714184400709)
          ·
            refine ⟨53534249459463696409575133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285515997117139714184400709 53534249459463696409575133)
            ·
              refine ⟨20075343547298886153590675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53534249459463696409575133 20075343547298886153590675)
              ·
                refine ⟨30113015320948329230386013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20075343547298886153590675 30113015320948329230386013)
                ·
                  refine ⟨11292380745355623461394755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30113015320948329230386013 11292380745355623461394755)
                  ·
                    refine ⟨16938571118033435192092133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11292380745355623461394755 16938571118033435192092133)
                    ·
                      refine ⟨3175982084631269098517275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16938571118033435192092133 3175982084631269098517275)
                      ·
                        rfl

theorem cell23_6185203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_6185203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185203 prefixEnd_6185203 := by exact prefixLift 6185203
  have htrace : WordTrace (prefixWord ++ tailWord_6185203) baseStart_6185203 baseEnd_6185203 := by
    simpa [prefixWord, tailWord_6185203, baseEnd_6185203] using wordTrace_append hprefix tailTrace_6185203
  have hstable : (prefixWord ++ tailWord_6185203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185203).length < 2 ^ (prefixWord ++ tailWord_6185203).sum := by decide
  have hdescent : baseEnd_6185203 < baseStart_6185203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185213 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_6185213 : Nat := 118140960795 + 6185213 * 2 ^ 59
def prefixEnd_6185213 : Nat := 4983230072969 + 3 ^ 40 * 6185213 * 2
def baseEnd_6185213 : Nat := 1058662406479271353130743

theorem tailTrace_6185213 : CollatzResearch.WordTrace tailWord_6185213 prefixEnd_6185213 1058662406479271353130743 := by
  unfold tailWord_6185213
  simp only [CollatzResearch.WordTrace]
  refine ⟨225593251341037126125168293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150395500894024750750112195 225593251341037126125168293)
  ·
    refine ⟨42298734626444461148469055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225593251341037126125168293 42298734626444461148469055)
    ·
      refine ⟨63448101939666691722703583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42298734626444461148469055 63448101939666691722703583)
      ·
        refine ⟨95172152909500037584055375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63448101939666691722703583 95172152909500037584055375)
        ·
          refine ⟨142758229364250056376083063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95172152909500037584055375 142758229364250056376083063)
          ·
            refine ⟨214137344046375084564124595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142758229364250056376083063 214137344046375084564124595)
            ·
              refine ⟨321206016069562626846186893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214137344046375084564124595 321206016069562626846186893)
              ·
                refine ⟨120452256026085985067320085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321206016069562626846186893 120452256026085985067320085)
                ·
                  refine ⟨5646199501222780550030629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120452256026085985067320085 5646199501222780550030629)
                  ·
                    refine ⟨1058662406479271353130743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646199501222780550030629 1058662406479271353130743)
                    ·
                      rfl

theorem cell23_6185213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_6185213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185213 prefixEnd_6185213 := by exact prefixLift 6185213
  have htrace : WordTrace (prefixWord ++ tailWord_6185213) baseStart_6185213 baseEnd_6185213 := by
    simpa [prefixWord, tailWord_6185213, baseEnd_6185213] using wordTrace_append hprefix tailTrace_6185213
  have hstable : (prefixWord ++ tailWord_6185213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185213).length < 2 ^ (prefixWord ++ tailWord_6185213).sum := by decide
  have hdescent : baseEnd_6185213 < baseStart_6185213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185214 : List Nat := [4, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_6185214 : Nat := 118140960795 + 6185214 * 2 ^ 59
def prefixEnd_6185214 : Nat := 4983230072969 + 3 ^ 40 * 6185214 * 2
def baseEnd_6185214 : Nat := 3175987732918468555479725

theorem tailTrace_6185214 : CollatzResearch.WordTrace tailWord_6185214 prefixEnd_6185214 3175987732918468555479725 := by
  unfold tailWord_6185214
  simp only [CollatzResearch.WordTrace]
  refine ⟨28199160976754187911994337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150395525209355668863969797 28199160976754187911994337)
  ·
    refine ⟨21149370732565640933995753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28199160976754187911994337 21149370732565640933995753)
    ·
      refine ⟨15862028049424230700496815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21149370732565640933995753 15862028049424230700496815)
      ·
        refine ⟨23793042074136346050745223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15862028049424230700496815 23793042074136346050745223)
        ·
          refine ⟨35689563111204519076117835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23793042074136346050745223 35689563111204519076117835)
          ·
            refine ⟨53534344666806778614176753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35689563111204519076117835 53534344666806778614176753)
            ·
              refine ⟨40150758500105083960632565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53534344666806778614176753 40150758500105083960632565)
              ·
                refine ⟨3764133609384851621309303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40150758500105083960632565 3764133609384851621309303)
                ·
                  refine ⟨5646200414077277431963955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764133609384851621309303 5646200414077277431963955)
                  ·
                    refine ⟨8469300621115916147945933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5646200414077277431963955 8469300621115916147945933)
                    ·
                      refine ⟨3175987732918468555479725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8469300621115916147945933 3175987732918468555479725)
                      ·
                        rfl

theorem cell23_6185214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_6185214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185214 prefixEnd_6185214 := by exact prefixLift 6185214
  have htrace : WordTrace (prefixWord ++ tailWord_6185214) baseStart_6185214 baseEnd_6185214 := by
    simpa [prefixWord, tailWord_6185214, baseEnd_6185214] using wordTrace_append hprefix tailTrace_6185214
  have hstable : (prefixWord ++ tailWord_6185214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185214).length < 2 ^ (prefixWord ++ tailWord_6185214).sum := by decide
  have hdescent : baseEnd_6185214 < baseStart_6185214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185250 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 1, 2, 4]
def baseStart_6185250 : Nat := 118140960795 + 6185250 * 2 ^ 59
def prefixEnd_6185250 : Nat := 4983230072969 + 3 ^ 40 * 6185250 * 2
def baseEnd_6185250 : Nat := 3176006218222030414629559

theorem tailTrace_6185250 : CollatzResearch.WordTrace tailWord_6185250 prefixEnd_6185250 3176006218222030414629559 := by
  unfold tailWord_6185250
  simp only [CollatzResearch.WordTrace]
  refine ⟨56398650210475770361066301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150396400561268720962843469 56398650210475770361066301)
  ·
    refine ⟨21149493828928413885399863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56398650210475770361066301 21149493828928413885399863)
    ·
      refine ⟨31724240743392620828099795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21149493828928413885399863 31724240743392620828099795)
      ·
        refine ⟨47586361115088931242149693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31724240743392620828099795 47586361115088931242149693)
        ·
          refine ⟨17844885418158349215806135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47586361115088931242149693 17844885418158349215806135)
          ·
            refine ⟨26767328127237523823709203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17844885418158349215806135 26767328127237523823709203)
            ·
              refine ⟨40150992190856285735563805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26767328127237523823709203 40150992190856285735563805)
              ·
                refine ⟨15056622071571107150836427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40150992190856285735563805 15056622071571107150836427)
                ·
                  refine ⟨22584933107356660726254641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15056622071571107150836427 22584933107356660726254641)
                  ·
                    refine ⟨16938699830517495544690981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22584933107356660726254641 16938699830517495544690981)
                    ·
                      refine ⟨3176006218222030414629559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16938699830517495544690981 3176006218222030414629559)
                      ·
                        rfl

theorem cell23_6185250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_6185250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185250 prefixEnd_6185250 := by exact prefixLift 6185250
  have htrace : WordTrace (prefixWord ++ tailWord_6185250) baseStart_6185250 baseEnd_6185250 := by
    simpa [prefixWord, tailWord_6185250, baseEnd_6185250] using wordTrace_append hprefix tailTrace_6185250
  have hstable : (prefixWord ++ tailWord_6185250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185250).length < 2 ^ (prefixWord ++ tailWord_6185250).sum := by decide
  have hdescent : baseEnd_6185250 < baseStart_6185250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185274 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3]
def baseStart_6185274 : Nat := 118140960795 + 6185274 * 2 ^ 59
def prefixEnd_6185274 : Nat := 4983230072969 + 3 ^ 40 * 6185274 * 2
def baseEnd_6185274 : Nat := 3176018541757738320729449

theorem tailTrace_6185274 : CollatzResearch.WordTrace tailWord_6185274 prefixEnd_6185274 3176018541757738320729449 := by
  unfold tailWord_6185274
  simp only [CollatzResearch.WordTrace]
  refine ⟨56398869048454033385784719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150396984129210755695425917 56398869048454033385784719)
  ·
    refine ⟨84598303572681050078677079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56398869048454033385784719 84598303572681050078677079)
    ·
      refine ⟨126897455359021575118015619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84598303572681050078677079 126897455359021575118015619)
      ·
        refine ⟨190346183038532362677023429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126897455359021575118015619 190346183038532362677023429)
        ·
          refine ⟨35689909319724818001941893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190346183038532362677023429 35689909319724818001941893)
          ·
            refine ⟨6691857997448403375364105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35689909319724818001941893 6691857997448403375364105)
            ·
              refine ⟨5018893498086302531523079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6691857997448403375364105 5018893498086302531523079)
              ·
                refine ⟨7528340247129453797284619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5018893498086302531523079 7528340247129453797284619)
                ·
                  refine ⟨11292510370694180695926929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528340247129453797284619 11292510370694180695926929)
                  ·
                    refine ⟨8469382778020635521945197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11292510370694180695926929 8469382778020635521945197)
                    ·
                      refine ⟨3176018541757738320729449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8469382778020635521945197 3176018541757738320729449)
                      ·
                        rfl

theorem cell23_6185274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_6185274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185274 prefixEnd_6185274 := by exact prefixLift 6185274
  have htrace : WordTrace (prefixWord ++ tailWord_6185274) baseStart_6185274 baseEnd_6185274 := by
    simpa [prefixWord, tailWord_6185274, baseEnd_6185274] using wordTrace_append hprefix tailTrace_6185274
  have hstable : (prefixWord ++ tailWord_6185274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185274).length < 2 ^ (prefixWord ++ tailWord_6185274).sum := by decide
  have hdescent : baseEnd_6185274 < baseStart_6185274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185280 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 5, 3, 2]
def baseStart_6185280 : Nat := 118140960795 + 6185280 * 2 ^ 59
def prefixEnd_6185280 : Nat := 4983230072969 + 3 ^ 40 * 6185280 * 2
def baseEnd_6185280 : Nat := 3176021622641665297254421

theorem tailTrace_6185280 : CollatzResearch.WordTrace tailWord_6185280 prefixEnd_6185280 3176021622641665297254421 := by
  unfold tailWord_6185280
  simp only [CollatzResearch.WordTrace]
  refine ⟨112797847515897198283928647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150397130021196264378571529 112797847515897198283928647)
  ·
    refine ⟨169196771273845797425892971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112797847515897198283928647 169196771273845797425892971)
    ·
      refine ⟨253795156910768696138839457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169196771273845797425892971 253795156910768696138839457)
      ·
        refine ⟨190346367683076522104129593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253795156910768696138839457 190346367683076522104129593)
        ·
          refine ⟨142759775762307391578097195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190346367683076522104129593 142759775762307391578097195)
          ·
            refine ⟨214139663643461087367145793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142759775762307391578097195 214139663643461087367145793)
            ·
              refine ⟨160604747732595815525359345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214139663643461087367145793 160604747732595815525359345)
              ·
                refine ⟨120453560799446861644019509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160604747732595815525359345 120453560799446861644019509)
                ·
                  refine ⟨11292521324948143279126829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120453560799446861644019509 11292521324948143279126829)
                  ·
                    refine ⟨4234695496855553729672561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11292521324948143279126829 4234695496855553729672561)
                    ·
                      refine ⟨3176021622641665297254421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234695496855553729672561 3176021622641665297254421)
                      ·
                        rfl

theorem cell23_6185280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_6185280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185280 prefixEnd_6185280 := by exact prefixLift 6185280
  have htrace : WordTrace (prefixWord ++ tailWord_6185280) baseStart_6185280 baseEnd_6185280 := by
    simpa [prefixWord, tailWord_6185280, baseEnd_6185280] using wordTrace_append hprefix tailTrace_6185280
  have hstable : (prefixWord ++ tailWord_6185280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185280).length < 2 ^ (prefixWord ++ tailWord_6185280).sum := by decide
  have hdescent : baseEnd_6185280 < baseStart_6185280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185281 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 2, 4]
def baseStart_6185281 : Nat := 118140960795 + 6185281 * 2 ^ 59
def prefixEnd_6185281 : Nat := 4983230072969 + 3 ^ 40 * 6185281 * 2
def baseEnd_6185281 : Nat := 1058674045374106597780639

theorem tailTrace_6185281 : CollatzResearch.WordTrace tailWord_6185281 prefixEnd_6185281 1058674045374106597780639 := by
  unfold tailWord_6185281
  simp only [CollatzResearch.WordTrace]
  refine ⟨225595731504790773738643697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150397154336527182492429131 225595731504790773738643697)
  ·
    refine ⟨169196798628593080303982773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225595731504790773738643697 169196798628593080303982773)
    ·
      refine ⟨15862199871430601278498385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169196798628593080303982773 15862199871430601278498385)
      ·
        refine ⟨11896649903572950958873789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15862199871430601278498385 11896649903572950958873789)
        ·
          refine ⟨4461243713839856609577671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11896649903572950958873789 4461243713839856609577671)
          ·
            refine ⟨6691865570759784914366507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461243713839856609577671 6691865570759784914366507)
            ·
              refine ⟨10037798356139677371549761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691865570759784914366507 10037798356139677371549761)
              ·
                refine ⟨7528348767104758028662321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10037798356139677371549761 7528348767104758028662321)
                ·
                  refine ⟨5646261575328568521496741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7528348767104758028662321 5646261575328568521496741)
                  ·
                    refine ⟨1058674045374106597780639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646261575328568521496741 1058674045374106597780639)
                    ·
                      rfl

theorem cell23_6185281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_6185281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185281 prefixEnd_6185281 := by exact prefixLift 6185281
  have htrace : WordTrace (prefixWord ++ tailWord_6185281) baseStart_6185281 baseEnd_6185281 := by
    simpa [prefixWord, tailWord_6185281, baseEnd_6185281] using wordTrace_append hprefix tailTrace_6185281
  have hstable : (prefixWord ++ tailWord_6185281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185281).length < 2 ^ (prefixWord ++ tailWord_6185281).sum := by decide
  have hdescent : baseEnd_6185281 < baseStart_6185281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185303 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 2, 6]
def baseStart_6185303 : Nat := 118140960795 + 6185303 * 2 ^ 59
def prefixEnd_6185303 : Nat := 4983230072969 + 3 ^ 40 * 6185303 * 2
def baseEnd_6185303 : Nat := 1058677810898906235755605

theorem tailTrace_6185303 : CollatzResearch.WordTrace tailWord_6185303 prefixEnd_6185303 1058677810898906235755605 := by
  unfold tailWord_6185303
  simp only [CollatzResearch.WordTrace]
  refine ⟨225596533910711071495944563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150397689273807380997296375 225596533910711071495944563)
  ·
    refine ⟨338394800866066607243916845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225596533910711071495944563 338394800866066607243916845)
    ·
      refine ⟨126898050324774977716468817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338394800866066607243916845 126898050324774977716468817)
      ·
        refine ⟨95173537743581233287351613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126898050324774977716468817 95173537743581233287351613)
        ·
          refine ⟨35690076653842962482756855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95173537743581233287351613 35690076653842962482756855)
          ·
            refine ⟨53535114980764443724135283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35690076653842962482756855 53535114980764443724135283)
            ·
              refine ⟨80302672471146665586202925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53535114980764443724135283 80302672471146665586202925)
              ·
                refine ⟨30113502176679999594826097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80302672471146665586202925 30113502176679999594826097)
                ·
                  refine ⟨22585126632509999696119573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30113502176679999594826097 22585126632509999696119573)
                  ·
                    refine ⟨1058677810898906235755605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22585126632509999696119573 1058677810898906235755605)
                    ·
                      rfl

theorem cell23_6185303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_6185303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185303 prefixEnd_6185303 := by exact prefixLift 6185303
  have htrace : WordTrace (prefixWord ++ tailWord_6185303) baseStart_6185303 baseEnd_6185303 := by
    simpa [prefixWord, tailWord_6185303, baseEnd_6185303] using wordTrace_append hprefix tailTrace_6185303
  have hstable : (prefixWord ++ tailWord_6185303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185303).length < 2 ^ (prefixWord ++ tailWord_6185303).sum := by decide
  have hdescent : baseEnd_6185303 < baseStart_6185303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185314 : List Nat := [3, 3, 2, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6185314 : Nat := 118140960795 + 6185314 * 2 ^ 59
def prefixEnd_6185314 : Nat := 4983230072969 + 3 ^ 40 * 6185314 * 2
def baseEnd_6185314 : Nat := 3176039080983918164229265

theorem tailTrace_6185314 : CollatzResearch.WordTrace tailWord_6185314 prefixEnd_6185314 3176039080983918164229265 := by
  unfold tailWord_6185314
  simp only [CollatzResearch.WordTrace]
  refine ⟨56399233778417805093648749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150397956742447480249729997 56399233778417805093648749)
  ·
    refine ⟨21149712666906676910118281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56399233778417805093648749 21149712666906676910118281)
    ·
      refine ⟨15862284500180007682588711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21149712666906676910118281 15862284500180007682588711)
      ·
        refine ⟨23793426750270011523883067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15862284500180007682588711 23793426750270011523883067)
        ·
          refine ⟨35690140125405017285824601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23793426750270011523883067 35690140125405017285824601)
          ·
            refine ⟨26767605094053762964368451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35690140125405017285824601 26767605094053762964368451)
            ·
              refine ⟨40151407641080644446552677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26767605094053762964368451 40151407641080644446552677)
              ·
                refine ⟨7528388932702620833728627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40151407641080644446552677 7528388932702620833728627)
                ·
                  refine ⟨11292583399053931250592941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528388932702620833728627 11292583399053931250592941)
                  ·
                    refine ⟨4234718774645224218972353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11292583399053931250592941 4234718774645224218972353)
                    ·
                      refine ⟨3176039080983918164229265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234718774645224218972353 3176039080983918164229265)
                      ·
                        rfl

theorem cell23_6185314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6185314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185314 prefixEnd_6185314 := by exact prefixLift 6185314
  have htrace : WordTrace (prefixWord ++ tailWord_6185314) baseStart_6185314 baseEnd_6185314 := by
    simpa [prefixWord, tailWord_6185314, baseEnd_6185314] using wordTrace_append hprefix tailTrace_6185314
  have hstable : (prefixWord ++ tailWord_6185314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185314).length < 2 ^ (prefixWord ++ tailWord_6185314).sum := by decide
  have hdescent : baseEnd_6185314 < baseStart_6185314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185330 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_6185330 : Nat := 118140960795 + 6185330 * 2 ^ 59
def prefixEnd_6185330 : Nat := 4983230072969 + 3 ^ 40 * 6185330 * 2
def baseEnd_6185330 : Nat := 3176047296674390101629191

theorem tailTrace_6185330 : CollatzResearch.WordTrace tailWord_6185330 prefixEnd_6185330 3176047296674390101629191 := by
  unfold tailWord_6185330
  simp only [CollatzResearch.WordTrace]
  refine ⟨56399379670403313776794361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150398345787742170071451629 56399379670403313776794361)
  ·
    refine ⟨42299534752802485332595771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56399379670403313776794361 42299534752802485332595771)
    ·
      refine ⟨63449302129203727998893657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42299534752802485332595771 63449302129203727998893657)
      ·
        refine ⟨47586976596902795999170243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63449302129203727998893657 47586976596902795999170243)
        ·
          refine ⟨71380464895354193998755365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47586976596902795999170243 71380464895354193998755365)
          ·
            refine ⟨13383837167878911374766631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71380464895354193998755365 13383837167878911374766631)
            ·
              refine ⟨20075755751818367062149947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13383837167878911374766631 20075755751818367062149947)
              ·
                refine ⟨30113633627727550593224921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20075755751818367062149947 30113633627727550593224921)
                ·
                  refine ⟨22585225220795662944918691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30113633627727550593224921 22585225220795662944918691)
                  ·
                    refine ⟨33877837831193494417378037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22585225220795662944918691 33877837831193494417378037)
                    ·
                      refine ⟨3176047296674390101629191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33877837831193494417378037 3176047296674390101629191)
                      ·
                        rfl

theorem cell23_6185330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_6185330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185330 prefixEnd_6185330 := by exact prefixLift 6185330
  have htrace : WordTrace (prefixWord ++ tailWord_6185330) baseStart_6185330 baseEnd_6185330 := by
    simpa [prefixWord, tailWord_6185330, baseEnd_6185330] using wordTrace_append hprefix tailTrace_6185330
  have hstable : (prefixWord ++ tailWord_6185330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185330).length < 2 ^ (prefixWord ++ tailWord_6185330).sum := by decide
  have hdescent : baseEnd_6185330 < baseStart_6185330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185380 : List Nat := [2, 3, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_6185380 : Nat := 118140960795 + 6185380 * 2 ^ 59
def prefixEnd_6185380 : Nat := 4983230072969 + 3 ^ 40 * 6185380 * 2
def baseEnd_6185380 : Nat := 1058690990235704968667987

theorem tailTrace_6185380 : CollatzResearch.WordTrace tailWord_6185380 prefixEnd_6185380 1058690990235704968667987 := by
  unfold tailWord_6185380
  simp only [CollatzResearch.WordTrace]
  refine ⟨112799671165716056823248797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150399561554288075764331729 112799671165716056823248797)
  ·
    refine ⟨42299876687143521308718299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112799671165716056823248797 42299876687143521308718299)
    ·
      refine ⟨63449815030715281963077449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42299876687143521308718299 63449815030715281963077449)
      ·
        refine ⟨47587361273036461472308087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63449815030715281963077449 47587361273036461472308087)
        ·
          refine ⟨71381041909554692208462131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47587361273036461472308087 71381041909554692208462131)
          ·
            refine ⟨107071562864332038312693197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71381041909554692208462131 107071562864332038312693197)
            ·
              refine ⟨40151836074124514367259949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107071562864332038312693197 40151836074124514367259949)
              ·
                refine ⟨15056938527796692887722481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40151836074124514367259949 15056938527796692887722481)
                ·
                  refine ⟨11292703895847519665791861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15056938527796692887722481 11292703895847519665791861)
                  ·
                    refine ⟨1058690990235704968667987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11292703895847519665791861 1058690990235704968667987)
                    ·
                      rfl

theorem cell23_6185380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_6185380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185380 prefixEnd_6185380 := by exact prefixLift 6185380
  have htrace : WordTrace (prefixWord ++ tailWord_6185380) baseStart_6185380 baseEnd_6185380 := by
    simpa [prefixWord, tailWord_6185380, baseEnd_6185380] using wordTrace_append hprefix tailTrace_6185380
  have hstable : (prefixWord ++ tailWord_6185380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185380).length < 2 ^ (prefixWord ++ tailWord_6185380).sum := by decide
  have hdescent : baseEnd_6185380 < baseStart_6185380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185423 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 10]
def baseStart_6185423 : Nat := 118140960795 + 6185423 * 2 ^ 59
def prefixEnd_6185423 : Nat := 4983230072969 + 3 ^ 40 * 6185423 * 2
def baseEnd_6185423 : Nat := 352899450041695359751807

theorem tailTrace_6185423 : CollatzResearch.WordTrace tailWord_6185423 prefixEnd_6185423 352899450041695359751807 := by
  unfold tailWord_6185423
  simp only [CollatzResearch.WordTrace]
  refine ⟨225600910670276331990312923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150400607113517554660208615 225600910670276331990312923)
  ·
    refine ⟨338401366005414497985469385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225600910670276331990312923 338401366005414497985469385)
    ·
      refine ⟨253801024504060873489102039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338401366005414497985469385 253801024504060873489102039)
      ·
        refine ⟨380701536756091310233653059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253801024504060873489102039 380701536756091310233653059)
        ·
          refine ⟨571052305134136965350479589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380701536756091310233653059 571052305134136965350479589)
          ·
            refine ⟨107072307212650681003214923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 571052305134136965350479589 107072307212650681003214923)
            ·
              refine ⟨160608460818976021504822385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107072307212650681003214923 160608460818976021504822385)
              ·
                refine ⟨120456345614232016128616789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160608460818976021504822385 120456345614232016128616789)
                ·
                  refine ⟨352899450041695359751807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 120456345614232016128616789 352899450041695359751807)
                  ·
                    rfl

theorem cell23_6185423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 10].length) (baseStart_6185423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185423 prefixEnd_6185423 := by exact prefixLift 6185423
  have htrace : WordTrace (prefixWord ++ tailWord_6185423) baseStart_6185423 baseEnd_6185423 := by
    simpa [prefixWord, tailWord_6185423, baseEnd_6185423] using wordTrace_append hprefix tailTrace_6185423
  have hstable : (prefixWord ++ tailWord_6185423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185423).length < 2 ^ (prefixWord ++ tailWord_6185423).sum := by decide
  have hdescent : baseEnd_6185423 < baseStart_6185423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185437 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_6185437 : Nat := 118140960795 + 6185437 * 2 ^ 59
def prefixEnd_6185437 : Nat := 4983230072969 + 3 ^ 40 * 6185437 * 2
def baseEnd_6185437 : Nat := 3176102239104421182991199

theorem tailTrace_6185437 : CollatzResearch.WordTrace tailWord_6185437 prefixEnd_6185437 3176102239104421182991199 := by
  unfold tailWord_6185437
  simp only [CollatzResearch.WordTrace]
  refine ⟨225601421292225612381322565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150400947528150408254215043 225601421292225612381322565)
  ·
    refine ⟨42300266492292302321497981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225601421292225612381322565 42300266492292302321497981)
    ·
      refine ⟨15862599934609613370561743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42300266492292302321497981 15862599934609613370561743)
      ·
        refine ⟨23793899901914420055842615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15862599934609613370561743 23793899901914420055842615)
        ·
          refine ⟨35690849852871630083763923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23793899901914420055842615 35690849852871630083763923)
          ·
            refine ⟨53536274779307445125645885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35690849852871630083763923 53536274779307445125645885)
            ·
              refine ⟨20076103042240291922117207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53536274779307445125645885 20076103042240291922117207)
              ·
                refine ⟨30114154563360437883175811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20076103042240291922117207 30114154563360437883175811)
                ·
                  refine ⟨45171231845040656824763717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30114154563360437883175811 45171231845040656824763717)
                  ·
                    refine ⟨8469605970945123154643197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45171231845040656824763717 8469605970945123154643197)
                    ·
                      refine ⟨3176102239104421182991199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8469605970945123154643197 3176102239104421182991199)
                      ·
                        rfl

theorem cell23_6185437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_6185437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185437 prefixEnd_6185437 := by exact prefixLift 6185437
  have htrace : WordTrace (prefixWord ++ tailWord_6185437) baseStart_6185437 baseEnd_6185437 := by
    simpa [prefixWord, tailWord_6185437, baseEnd_6185437] using wordTrace_append hprefix tailTrace_6185437
  have hstable : (prefixWord ++ tailWord_6185437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185437).length < 2 ^ (prefixWord ++ tailWord_6185437).sum := by decide
  have hdescent : baseEnd_6185437 < baseStart_6185437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185461 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6185461 : Nat := 118140960795 + 6185461 * 2 ^ 59
def prefixEnd_6185461 : Nat := 4983230072969 + 3 ^ 40 * 6185461 * 2
def baseEnd_6185461 : Nat := 1058704854213376363030363

theorem tailTrace_6185461 : CollatzResearch.WordTrace tailWord_6185461 prefixEnd_6185461 1058704854213376363030363 := by
  unfold tailWord_6185461
  simp only [CollatzResearch.WordTrace]
  refine ⟨225602296644138664480196237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150401531096092442986797491 225602296644138664480196237)
  ·
    refine ⟨84600861241551999180073589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225602296644138664480196237 84600861241551999180073589)
    ·
      refine ⟨7931330741395499923131899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84600861241551999180073589 7931330741395499923131899)
      ·
        refine ⟨11896996112093249884697849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7931330741395499923131899 11896996112093249884697849)
        ·
          refine ⟨8922747084069937413523387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11896996112093249884697849 8922747084069937413523387)
          ·
            refine ⟨13384120626104906120285081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8922747084069937413523387 13384120626104906120285081)
            ·
              refine ⟨10038090469578679590213811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13384120626104906120285081 10038090469578679590213811)
              ·
                refine ⟨15057135704368019385320717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10038090469578679590213811 15057135704368019385320717)
                ·
                  refine ⟨5646425889138007269495269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15057135704368019385320717 5646425889138007269495269)
                  ·
                    refine ⟨1058704854213376363030363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646425889138007269495269 1058704854213376363030363)
                    ·
                      rfl

theorem cell23_6185461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6185461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185461 prefixEnd_6185461 := by exact prefixLift 6185461
  have htrace : WordTrace (prefixWord ++ tailWord_6185461) baseStart_6185461 baseEnd_6185461 := by
    simpa [prefixWord, tailWord_6185461, baseEnd_6185461] using wordTrace_append hprefix tailTrace_6185461
  have hstable : (prefixWord ++ tailWord_6185461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185461).length < 2 ^ (prefixWord ++ tailWord_6185461).sum := by decide
  have hdescent : baseEnd_6185461 < baseStart_6185461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185477 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 1, 5, 2]
def baseStart_6185477 : Nat := 118140960795 + 6185477 * 2 ^ 59
def prefixEnd_6185477 : Nat := 4983230072969 + 3 ^ 40 * 6185477 * 2
def baseEnd_6185477 : Nat := 3176122778330601026491015

theorem tailTrace_6185477 : CollatzResearch.WordTrace tailWord_6185477 prefixEnd_6185477 3176122778330601026491015 := by
  unfold tailWord_6185477
  simp only [CollatzResearch.WordTrace]
  refine ⟨225602880212080699212778685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150401920141387132808519123 225602880212080699212778685)
  ·
    refine ⟨84601080079530262204792007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225602880212080699212778685 84601080079530262204792007)
    ·
      refine ⟨126901620119295393307188011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84601080079530262204792007 126901620119295393307188011)
      ·
        refine ⟨190352430178943089960782017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126901620119295393307188011 190352430178943089960782017)
        ·
          refine ⟨142764322634207317470586513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190352430178943089960782017 142764322634207317470586513)
          ·
            refine ⟨107073241975655488102939885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142764322634207317470586513 107073241975655488102939885)
            ·
              refine ⟨40152465740870808038602457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107073241975655488102939885 40152465740870808038602457)
              ·
                refine ⟨30114349305653106028951843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40152465740870808038602457 30114349305653106028951843)
                ·
                  refine ⟨45171523958479659043427765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30114349305653106028951843 45171523958479659043427765)
                  ·
                    refine ⟨4234830371107468035321353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45171523958479659043427765 4234830371107468035321353)
                    ·
                      refine ⟨3176122778330601026491015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234830371107468035321353 3176122778330601026491015)
                      ·
                        rfl

theorem cell23_6185477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_6185477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185477 prefixEnd_6185477 := by exact prefixLift 6185477
  have htrace : WordTrace (prefixWord ++ tailWord_6185477) baseStart_6185477 baseEnd_6185477 := by
    simpa [prefixWord, tailWord_6185477, baseEnd_6185477] using wordTrace_append hprefix tailTrace_6185477
  have hstable : (prefixWord ++ tailWord_6185477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185477).length < 2 ^ (prefixWord ++ tailWord_6185477).sum := by decide
  have hdescent : baseEnd_6185477 < baseStart_6185477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185478 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6185478 : Nat := 118140960795 + 6185478 * 2 ^ 59
def prefixEnd_6185478 : Nat := 4983230072969 + 3 ^ 40 * 6185478 * 2
def baseEnd_6185478 : Nat := 1058707763937085174192837

theorem tailTrace_6185478 : CollatzResearch.WordTrace tailWord_6185478 prefixEnd_6185478 1058707763937085174192837 := by
  unfold tailWord_6185478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050091146408658636986409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150401944456718050922376725 7050091146408658636986409)
  ·
    refine ⟨5287568359806493977739807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7050091146408658636986409 5287568359806493977739807)
    ·
      refine ⟨7931352539709740966609711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5287568359806493977739807 7931352539709740966609711)
      ·
        refine ⟨11897028809564611449914567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7931352539709740966609711 11897028809564611449914567)
        ·
          refine ⟨17845543214346917174871851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11897028809564611449914567 17845543214346917174871851)
          ·
            refine ⟨26768314821520375762307777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17845543214346917174871851 26768314821520375762307777)
            ·
              refine ⟨20076236116140281821730833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26768314821520375762307777 20076236116140281821730833)
              ·
                refine ⟨15057177087105211366298125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20076236116140281821730833 15057177087105211366298125)
                ·
                  refine ⟨5646441407664454262361797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15057177087105211366298125 5646441407664454262361797)
                  ·
                    refine ⟨1058707763937085174192837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646441407664454262361797 1058707763937085174192837)
                    ·
                      rfl

theorem cell23_6185478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6185478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185478 prefixEnd_6185478 := by exact prefixLift 6185478
  have htrace : WordTrace (prefixWord ++ tailWord_6185478) baseStart_6185478 baseEnd_6185478 := by
    simpa [prefixWord, tailWord_6185478, baseEnd_6185478] using wordTrace_append hprefix tailTrace_6185478
  have hstable : (prefixWord ++ tailWord_6185478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185478).length < 2 ^ (prefixWord ++ tailWord_6185478).sum := by decide
  have hdescent : baseEnd_6185478 < baseStart_6185478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185484 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 3, 1, 3]
def baseStart_6185484 : Nat := 118140960795 + 6185484 * 2 ^ 59
def prefixEnd_6185484 : Nat := 4983230072969 + 3 ^ 40 * 6185484 * 2
def baseEnd_6185484 : Nat := 3176126372695182499103483

theorem tailTrace_6185484 : CollatzResearch.WordTrace tailWord_6185484 prefixEnd_6185484 3176126372695182499103483 := by
  unfold tailWord_6185484
  simp only [CollatzResearch.WordTrace]
  refine ⟨112801567761527669704141753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150402090348703559605522337 112801567761527669704141753)
  ·
    refine ⟨84601175821145752278106315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112801567761527669704141753 84601175821145752278106315)
    ·
      refine ⟨126901763731718628417159473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84601175821145752278106315 126901763731718628417159473)
      ·
        refine ⟨95176322798788971312869605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126901763731718628417159473 95176322798788971312869605)
        ·
          refine ⟨17845560524772932121163051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95176322798788971312869605 17845560524772932121163051)
          ·
            refine ⟨26768340787159398181744577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17845560524772932121163051 26768340787159398181744577)
            ·
              refine ⟨20076255590369548636308433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26768340787159398181744577 20076255590369548636308433)
              ·
                refine ⟨15057191692777161477231325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20076255590369548636308433 15057191692777161477231325)
                ·
                  refine ⟨5646446884791435553961747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15057191692777161477231325 5646446884791435553961747)
                  ·
                    refine ⟨8469670327187153330942621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5646446884791435553961747 8469670327187153330942621)
                    ·
                      refine ⟨3176126372695182499103483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8469670327187153330942621 3176126372695182499103483)
                      ·
                        rfl

theorem cell23_6185484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_6185484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185484 prefixEnd_6185484 := by exact prefixLift 6185484
  have htrace : WordTrace (prefixWord ++ tailWord_6185484) baseStart_6185484 baseEnd_6185484 := by
    simpa [prefixWord, tailWord_6185484, baseEnd_6185484] using wordTrace_append hprefix tailTrace_6185484
  have hstable : (prefixWord ++ tailWord_6185484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185484).length < 2 ^ (prefixWord ++ tailWord_6185484).sum := by decide
  have hdescent : baseEnd_6185484 < baseStart_6185484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185495 : List Nat := [1, 1, 3, 6, 2, 1, 1, 3, 1, 4]
def baseStart_6185495 : Nat := 118140960795 + 6185495 * 2 ^ 59
def prefixEnd_6185495 : Nat := 4983230072969 + 3 ^ 40 * 6185495 * 2
def baseEnd_6185495 : Nat := 1058710673660793985355311

theorem tailTrace_6185495 : CollatzResearch.WordTrace tailWord_6185495 prefixEnd_6185495 1058710673660793985355311 := by
  unfold tailWord_6185495
  simp only [CollatzResearch.WordTrace]
  refine ⟨225603536726015488286933939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150402357817343658857955959 225603536726015488286933939)
  ·
    refine ⟨338405305089023232430400909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225603536726015488286933939 338405305089023232430400909)
    ·
      refine ⟨126901989408383712161400341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338405305089023232430400909 126901989408383712161400341)
      ·
        refine ⟨5948530753517986507565641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126901989408383712161400341 5948530753517986507565641)
        ·
          refine ⟨4461398065138489880674231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5948530753517986507565641 4461398065138489880674231)
          ·
            refine ⟨6692097097707734821011347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461398065138489880674231 6692097097707734821011347)
            ·
              refine ⟨10038145646561602231517021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692097097707734821011347 10038145646561602231517021)
              ·
                refine ⟨3764304617460600836818883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10038145646561602231517021 3764304617460600836818883)
                ·
                  refine ⟨5646456926190901255228325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764304617460600836818883 5646456926190901255228325)
                  ·
                    refine ⟨1058710673660793985355311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646456926190901255228325 1058710673660793985355311)
                    ·
                      rfl

theorem cell23_6185495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_6185495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185495 prefixEnd_6185495 := by exact prefixLift 6185495
  have htrace : WordTrace (prefixWord ++ tailWord_6185495) baseStart_6185495 baseEnd_6185495 := by
    simpa [prefixWord, tailWord_6185495, baseEnd_6185495] using wordTrace_append hprefix tailTrace_6185495
  have hstable : (prefixWord ++ tailWord_6185495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185495).length < 2 ^ (prefixWord ++ tailWord_6185495).sum := by decide
  have hdescent : baseEnd_6185495 < baseStart_6185495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185518 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_6185518 : Nat := 118140960795 + 6185518 * 2 ^ 59
def prefixEnd_6185518 : Nat := 4983230072969 + 3 ^ 40 * 6185518 * 2
def baseEnd_6185518 : Nat := 3176143831037435366078327

theorem tailTrace_6185518 : CollatzResearch.WordTrace tailWord_6185518 prefixEnd_6185518 3176143831037435366078327 := by
  unfold tailWord_6185518
  simp only [CollatzResearch.WordTrace]
  refine ⟨28200546950616520401877651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150402917069954775476680805 28200546950616520401877651)
  ·
    refine ⟨42300820425924780602816477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28200546950616520401877651 42300820425924780602816477)
    ·
      refine ⟨15862807659721792726056179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42300820425924780602816477 15862807659721792726056179)
      ·
        refine ⟨23794211489582689089084269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15862807659721792726056179 23794211489582689089084269)
        ·
          refine ⟨8922829308593508408406601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23794211489582689089084269 8922829308593508408406601)
          ·
            refine ⟨6692121981445131306304951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8922829308593508408406601 6692121981445131306304951)
            ·
              refine ⟨10038182972167696959457427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692121981445131306304951 10038182972167696959457427)
              ·
                refine ⟨15057274458251545439186141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10038182972167696959457427 15057274458251545439186141)
                ·
                  refine ⟨5646477921844329539694803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15057274458251545439186141 5646477921844329539694803)
                  ·
                    refine ⟨8469716882766494309542205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5646477921844329539694803 8469716882766494309542205)
                    ·
                      refine ⟨3176143831037435366078327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8469716882766494309542205 3176143831037435366078327)
                      ·
                        rfl

theorem cell23_6185518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_6185518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185518 prefixEnd_6185518 := by exact prefixLift 6185518
  have htrace : WordTrace (prefixWord ++ tailWord_6185518) baseStart_6185518 baseEnd_6185518 := by
    simpa [prefixWord, tailWord_6185518, baseEnd_6185518] using wordTrace_append hprefix tailTrace_6185518
  have hstable : (prefixWord ++ tailWord_6185518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185518).length < 2 ^ (prefixWord ++ tailWord_6185518).sum := by decide
  have hdescent : baseEnd_6185518 < baseStart_6185518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185520 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6]
def baseStart_6185520 : Nat := 118140960795 + 6185520 * 2 ^ 59
def prefixEnd_6185520 : Nat := 4983230072969 + 3 ^ 40 * 6185520 * 2
def baseEnd_6185520 : Nat := 3176144857998744358253317

theorem tailTrace_6185520 : CollatzResearch.WordTrace tailWord_6185520 prefixEnd_6185520 3176144857998744358253317 := by
  unfold tailWord_6185520
  simp only [CollatzResearch.WordTrace]
  refine ⟨112802224275462458778297007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150402965700616611704396009 112802224275462458778297007)
  ·
    refine ⟨169203336413193688167445511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112802224275462458778297007 169203336413193688167445511)
    ·
      refine ⟨253805004619790532251168267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169203336413193688167445511 253805004619790532251168267)
      ·
        refine ⟨380707506929685798376752401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253805004619790532251168267 380707506929685798376752401)
        ·
          refine ⟨285530630197264348782564301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380707506929685798376752401 285530630197264348782564301)
          ·
            refine ⟨107073986323974130793461613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285530630197264348782564301 107073986323974130793461613)
            ·
              refine ⟨40152744871490299047548105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107073986323974130793461613 40152744871490299047548105)
              ·
                refine ⟨30114558653617724285661079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40152744871490299047548105 30114558653617724285661079)
                ·
                  refine ⟨45171837980426586428491619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30114558653617724285661079 45171837980426586428491619)
                  ·
                    refine ⟨67757756970639879642737429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45171837980426586428491619 67757756970639879642737429)
                    ·
                      refine ⟨3176144857998744358253317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67757756970639879642737429 3176144857998744358253317)
                      ·
                        rfl

theorem cell23_6185520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_6185520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185520 prefixEnd_6185520 := by exact prefixLift 6185520
  have htrace : WordTrace (prefixWord ++ tailWord_6185520) baseStart_6185520 baseEnd_6185520 := by
    simpa [prefixWord, tailWord_6185520, baseEnd_6185520] using wordTrace_append hprefix tailTrace_6185520
  have hstable : (prefixWord ++ tailWord_6185520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185520).length < 2 ^ (prefixWord ++ tailWord_6185520).sum := by decide
  have hdescent : baseEnd_6185520 < baseStart_6185520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185527 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_6185527 : Nat := 118140960795 + 6185527 * 2 ^ 59
def prefixEnd_6185527 : Nat := 4983230072969 + 3 ^ 40 * 6185527 * 2
def baseEnd_6185527 : Nat := 3176148452363325830865785

theorem tailTrace_6185527 : CollatzResearch.WordTrace tailWord_6185527 prefixEnd_6185527 3176148452363325830865785 := by
  unfold tailWord_6185527
  simp only [CollatzResearch.WordTrace]
  refine ⟨225604703861899557752098835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150403135907933038501399223 225604703861899557752098835)
  ·
    refine ⟨338407055792849336628148253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225604703861899557752098835 338407055792849336628148253)
    ·
      refine ⟨126902645922318501235555595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 338407055792849336628148253 126902645922318501235555595)
      ·
        refine ⟨190353968883477751853333393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126902645922318501235555595 190353968883477751853333393)
        ·
          refine ⟨142765476662608313890000045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190353968883477751853333393 142765476662608313890000045)
          ·
            refine ⟨53537053748478117708750017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142765476662608313890000045 53537053748478117708750017)
            ·
              refine ⟨40152790311358588281562513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53537053748478117708750017 40152790311358588281562513)
              ·
                refine ⟨30114592733518941211171885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40152790311358588281562513 30114592733518941211171885)
                ·
                  refine ⟨11292972275069602954189457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30114592733518941211171885 11292972275069602954189457)
                  ·
                    refine ⟨8469729206302202215642093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11292972275069602954189457 8469729206302202215642093)
                    ·
                      refine ⟨3176148452363325830865785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8469729206302202215642093 3176148452363325830865785)
                      ·
                        rfl

theorem cell23_6185527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_6185527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185527 prefixEnd_6185527 := by exact prefixLift 6185527
  have htrace : WordTrace (prefixWord ++ tailWord_6185527) baseStart_6185527 baseEnd_6185527 := by
    simpa [prefixWord, tailWord_6185527, baseEnd_6185527] using wordTrace_append hprefix tailTrace_6185527
  have hstable : (prefixWord ++ tailWord_6185527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185527).length < 2 ^ (prefixWord ++ tailWord_6185527).sum := by decide
  have hdescent : baseEnd_6185527 < baseStart_6185527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185530 : List Nat := [3, 1, 1, 1, 3, 3, 1, 10]
def baseStart_6185530 : Nat := 118140960795 + 6185530 * 2 ^ 59
def prefixEnd_6185530 : Nat := 4983230072969 + 3 ^ 40 * 6185530 * 2
def baseEnd_6185530 : Nat := 117635184918714419226973

theorem tailTrace_6185530 : CollatzResearch.WordTrace tailWord_6185530 prefixEnd_6185530 117635184918714419226973 := by
  unfold tailWord_6185530
  simp only [CollatzResearch.WordTrace]
  refine ⟨56401203320222172316114511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150403208853925792842972029 56401203320222172316114511)
  ·
    refine ⟨84601804980333258474171767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56401203320222172316114511 84601804980333258474171767)
    ·
      refine ⟨126902707470499887711257651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84601804980333258474171767 126902707470499887711257651)
      ·
        refine ⟨190354061205749831566886477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126902707470499887711257651 190354061205749831566886477)
        ·
          refine ⟨71382772952156186837582429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190354061205749831566886477 71382772952156186837582429)
          ·
            refine ⟨26768539857058570064093411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71382772952156186837582429 26768539857058570064093411)
            ·
              refine ⟨40152809785587855096140117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26768539857058570064093411 40152809785587855096140117)
              ·
                refine ⟨117635184918714419226973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40152809785587855096140117 117635184918714419226973)
                ·
                  rfl

theorem cell23_6185530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_6185530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185530 prefixEnd_6185530 := by exact prefixLift 6185530
  have htrace : WordTrace (prefixWord ++ tailWord_6185530) baseStart_6185530 baseEnd_6185530 := by
    simpa [prefixWord, tailWord_6185530, baseEnd_6185530] using wordTrace_append hprefix tailTrace_6185530
  have hstable : (prefixWord ++ tailWord_6185530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185530).length < 2 ^ (prefixWord ++ tailWord_6185530).sum := by decide
  have hdescent : baseEnd_6185530 < baseStart_6185530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185537 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6185537 : Nat := 118140960795 + 6185537 * 2 ^ 59
def prefixEnd_6185537 : Nat := 4983230072969 + 3 ^ 40 * 6185537 * 2
def baseEnd_6185537 : Nat := 3176153587169870791740739

theorem tailTrace_6185537 : CollatzResearch.WordTrace tailWord_6185537 prefixEnd_6185537 3176153587169870791740739 := by
  unfold tailWord_6185537
  simp only [CollatzResearch.WordTrace]
  refine ⟨225605068591863329459962865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150403379061242219639975243 225605068591863329459962865)
  ·
    refine ⟨169203801443897497094972149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225605068591863329459962865 169203801443897497094972149)
    ·
      refine ⟨15862856385365390352653639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169203801443897497094972149 15862856385365390352653639)
      ·
        refine ⟨23794284578048085528980459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15862856385365390352653639 23794284578048085528980459)
        ·
          refine ⟨35691426867072128293470689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23794284578048085528980459 35691426867072128293470689)
          ·
            refine ⟨26768570150304096220103017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35691426867072128293470689 26768570150304096220103017)
            ·
              refine ⟨20076427612728072165077263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26768570150304096220103017 20076427612728072165077263)
              ·
                refine ⟨30114641419092108247615895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20076427612728072165077263 30114641419092108247615895)
                ·
                  refine ⟨45171962128638162371423843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30114641419092108247615895 45171962128638162371423843)
                  ·
                    refine ⟨67757943192957243557135765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45171962128638162371423843 67757943192957243557135765)
                    ·
                      refine ⟨3176153587169870791740739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67757943192957243557135765 3176153587169870791740739)
                      ·
                        rfl

theorem cell23_6185537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6185537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185537 prefixEnd_6185537 := by exact prefixLift 6185537
  have htrace : WordTrace (prefixWord ++ tailWord_6185537) baseStart_6185537 baseEnd_6185537 := by
    simpa [prefixWord, tailWord_6185537, baseEnd_6185537] using wordTrace_append hprefix tailTrace_6185537
  have hstable : (prefixWord ++ tailWord_6185537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185537).length < 2 ^ (prefixWord ++ tailWord_6185537).sum := by decide
  have hdescent : baseEnd_6185537 < baseStart_6185537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185557 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 3]
def baseStart_6185557 : Nat := 118140960795 + 6185557 * 2 ^ 59
def prefixEnd_6185557 : Nat := 4983230072969 + 3 ^ 40 * 6185557 * 2
def baseEnd_6185557 : Nat := 3176163856782960713490647

theorem tailTrace_6185557 : CollatzResearch.WordTrace tailWord_6185557 prefixEnd_6185557 3176163856782960713490647 := by
  unfold tailWord_6185557
  simp only [CollatzResearch.WordTrace]
  refine ⟨225605798051790872875690925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150403865367860581917127283 225605798051790872875690925)
  ·
    refine ⟨84602174269421577328384097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225605798051790872875690925 84602174269421577328384097)
    ·
      refine ⟨63451630702066182996288073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84602174269421577328384097 63451630702066182996288073)
      ·
        refine ⟨47588723026549637247216055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63451630702066182996288073 47588723026549637247216055)
        ·
          refine ⟨71383084539824455870824083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47588723026549637247216055 71383084539824455870824083)
          ·
            refine ⟨107074626809736683806236125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71383084539824455870824083 107074626809736683806236125)
            ·
              refine ⟨40152985053651256427338547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107074626809736683806236125 40152985053651256427338547)
              ·
                refine ⟨60229477580476884641007821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40152985053651256427338547 60229477580476884641007821)
                ·
                  refine ⟨22586054092678831740377933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60229477580476884641007821 22586054092678831740377933)
                  ·
                    refine ⟨8469770284754561902641725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22586054092678831740377933 8469770284754561902641725)
                    ·
                      refine ⟨3176163856782960713490647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8469770284754561902641725 3176163856782960713490647)
                      ·
                        rfl

theorem cell23_6185557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_6185557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185557 prefixEnd_6185557 := by exact prefixLift 6185557
  have htrace : WordTrace (prefixWord ++ tailWord_6185557) baseStart_6185557 baseEnd_6185557 := by
    simpa [prefixWord, tailWord_6185557, baseEnd_6185557] using wordTrace_append hprefix tailTrace_6185557
  have hstable : (prefixWord ++ tailWord_6185557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185557).length < 2 ^ (prefixWord ++ tailWord_6185557).sum := by decide
  have hdescent : baseEnd_6185557 < baseStart_6185557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185601 : List Nat := [1, 2, 4, 2, 1, 1, 2, 4, 1, 3, 2]
def baseStart_6185601 : Nat := 118140960795 + 6185601 * 2 ^ 59
def prefixEnd_6185601 : Nat := 4983230072969 + 3 ^ 40 * 6185601 * 2
def baseEnd_6185601 : Nat := 3176186449931758541340445

theorem tailTrace_6185601 : CollatzResearch.WordTrace tailWord_6185601 prefixEnd_6185601 3176186449931758541340445 := by
  unfold tailWord_6185601
  simp only [CollatzResearch.WordTrace]
  refine ⟨225607402863631468390292657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150404935242420978926861771 225607402863631468390292657)
  ·
    refine ⟨169205552147723601292719493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225607402863631468390292657 169205552147723601292719493)
    ·
      refine ⟨31726041027698175242384905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169205552147723601292719493 31726041027698175242384905)
      ·
        refine ⟨23794530770773631431788679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31726041027698175242384905 23794530770773631431788679)
        ·
          refine ⟨35691796156160447147683019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23794530770773631431788679 35691796156160447147683019)
          ·
            refine ⟨53537694234240670721524529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35691796156160447147683019 53537694234240670721524529)
            ·
              refine ⟨40153270675680503041143397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53537694234240670721524529 40153270675680503041143397)
              ·
                refine ⟨7528738251690094320214387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40153270675680503041143397 7528738251690094320214387)
                ·
                  refine ⟨11293107377535141480321581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528738251690094320214387 11293107377535141480321581)
                  ·
                    refine ⟨4234915266575678055120593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11293107377535141480321581 4234915266575678055120593)
                    ·
                      refine ⟨3176186449931758541340445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234915266575678055120593 3176186449931758541340445)
                      ·
                        rfl

theorem cell23_6185601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_6185601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185601 prefixEnd_6185601 := by exact prefixLift 6185601
  have htrace : WordTrace (prefixWord ++ tailWord_6185601) baseStart_6185601 baseEnd_6185601 := by
    simpa [prefixWord, tailWord_6185601, baseEnd_6185601] using wordTrace_append hprefix tailTrace_6185601
  have hstable : (prefixWord ++ tailWord_6185601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185601).length < 2 ^ (prefixWord ++ tailWord_6185601).sum := by decide
  have hdescent : baseEnd_6185601 < baseStart_6185601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185618 : List Nat := [3, 2, 3, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_6185618 : Nat := 118140960795 + 6185618 * 2 ^ 59
def prefixEnd_6185618 : Nat := 4983230072969 + 3 ^ 40 * 6185618 * 2
def baseEnd_6185618 : Nat := 3176195179102884974827867

theorem tailTrace_6185618 : CollatzResearch.WordTrace tailWord_6185618 prefixEnd_6185618 3176195179102884974827867 := by
  unfold tailWord_6185618
  simp only [CollatzResearch.WordTrace]
  refine ⟨56402005726142470073415377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150405348603046586862441005 56402005726142470073415377)
  ·
    refine ⟨42301504294606852555061533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56402005726142470073415377 42301504294606852555061533)
    ·
      refine ⟨15863064110477569708148075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42301504294606852555061533 15863064110477569708148075)
      ·
        refine ⟨23794596165716354562222113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15863064110477569708148075 23794596165716354562222113)
        ·
          refine ⟨17845947124287265921666585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23794596165716354562222113 17845947124287265921666585)
          ·
            refine ⟨13384460343215449441249939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17845947124287265921666585 13384460343215449441249939)
            ·
              refine ⟨20076690514823174161874909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13384460343215449441249939 20076690514823174161874909)
              ·
                refine ⟨7528758943058690310703091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20076690514823174161874909 7528758943058690310703091)
                ·
                  refine ⟨11293138414588035466054637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528758943058690310703091 11293138414588035466054637)
                  ·
                    refine ⟨4234926905470513299770489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11293138414588035466054637 4234926905470513299770489)
                    ·
                      refine ⟨3176195179102884974827867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4234926905470513299770489 3176195179102884974827867)
                      ·
                        rfl

theorem cell23_6185618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_6185618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185618 prefixEnd_6185618 := by exact prefixLift 6185618
  have htrace : WordTrace (prefixWord ++ tailWord_6185618) baseStart_6185618 baseEnd_6185618 := by
    simpa [prefixWord, tailWord_6185618, baseEnd_6185618] using wordTrace_append hprefix tailTrace_6185618
  have hstable : (prefixWord ++ tailWord_6185618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185618).length < 2 ^ (prefixWord ++ tailWord_6185618).sum := by decide
  have hdescent : baseEnd_6185618 < baseStart_6185618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185642 : List Nat := [3, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6185642 : Nat := 118140960795 + 6185642 * 2 ^ 59
def prefixEnd_6185642 : Nat := 4983230072969 + 3 ^ 40 * 6185642 * 2
def baseEnd_6185642 : Nat := 3176207502638592880927757

theorem tailTrace_6185642 : CollatzResearch.WordTrace tailWord_6185642 prefixEnd_6185642 3176207502638592880927757 := by
  unfold tailWord_6185642
  simp only [CollatzResearch.WordTrace]
  refine ⟨56402224564120733098133795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150405932170988621595023453 56402224564120733098133795)
  ·
    refine ⟨84603336846181099647200693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56402224564120733098133795 84603336846181099647200693)
    ·
      refine ⟨7931562829329478091925065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84603336846181099647200693 7931562829329478091925065)
      ·
        refine ⟨5948672121997108568943799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7931562829329478091925065 5948672121997108568943799)
        ·
          refine ⟨8923008182995662853415699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5948672121997108568943799 8923008182995662853415699)
          ·
            refine ⟨13384512274493494280123549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923008182995662853415699 13384512274493494280123549)
            ·
              refine ⟨5019192102935060355046331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13384512274493494280123549 5019192102935060355046331)
              ·
                refine ⟨7528788154402590532569497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5019192102935060355046331 7528788154402590532569497)
                ·
                  refine ⟨5646591115801942899427123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7528788154402590532569497 5646591115801942899427123)
                  ·
                    refine ⟨8469886673702914349140685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5646591115801942899427123 8469886673702914349140685)
                    ·
                      refine ⟨3176207502638592880927757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8469886673702914349140685 3176207502638592880927757)
                      ·
                        rfl

theorem cell23_6185642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6185642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185642 prefixEnd_6185642 := by exact prefixLift 6185642
  have htrace : WordTrace (prefixWord ++ tailWord_6185642) baseStart_6185642 baseEnd_6185642 := by
    simpa [prefixWord, tailWord_6185642, baseEnd_6185642] using wordTrace_append hprefix tailTrace_6185642
  have hstable : (prefixWord ++ tailWord_6185642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185642).length < 2 ^ (prefixWord ++ tailWord_6185642).sum := by decide
  have hdescent : baseEnd_6185642 < baseStart_6185642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185731 : List Nat := [1, 1, 1, 3, 2, 2, 1, 7, 1, 4]
def baseStart_6185731 : Nat := 118140960795 + 6185731 * 2 ^ 59
def prefixEnd_6185731 : Nat := 4983230072969 + 3 ^ 40 * 6185731 * 2
def baseEnd_6185731 : Nat := 1058751067472281010904949

theorem tailTrace_6185731 : CollatzResearch.WordTrace tailWord_6185731 prefixEnd_6185731 1058751067472281010904949 := by
  unfold tailWord_6185731
  simp only [CollatzResearch.WordTrace]
  refine ⟨225612144353160500592525047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150408096235440333728350031 225612144353160500592525047)
  ·
    refine ⟨338418216529740750888787571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225612144353160500592525047 338418216529740750888787571)
    ·
      refine ⟨507627324794611126333181357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338418216529740750888787571 507627324794611126333181357)
      ·
        refine ⟨190360246797979172374943009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 507627324794611126333181357 190360246797979172374943009)
        ·
          refine ⟨142770185098484379281207257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190360246797979172374943009 142770185098484379281207257)
          ·
            refine ⟨107077638823863284460905443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142770185098484379281207257 107077638823863284460905443)
            ·
              refine ⟨160616458235794926691358165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107077638823863284460905443 160616458235794926691358165)
              ·
                refine ⟨3764448239901443594328707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 160616458235794926691358165 3764448239901443594328707)
                ·
                  refine ⟨5646672359852165391493061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764448239901443594328707 5646672359852165391493061)
                  ·
                    refine ⟨1058751067472281010904949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646672359852165391493061 1058751067472281010904949)
                    ·
                      rfl

theorem cell23_6185731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 1, 4].length) (baseStart_6185731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185731 prefixEnd_6185731 := by exact prefixLift 6185731
  have htrace : WordTrace (prefixWord ++ tailWord_6185731) baseStart_6185731 baseEnd_6185731 := by
    simpa [prefixWord, tailWord_6185731, baseEnd_6185731] using wordTrace_append hprefix tailTrace_6185731
  have hstable : (prefixWord ++ tailWord_6185731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185731).length < 2 ^ (prefixWord ++ tailWord_6185731).sum := by decide
  have hdescent : baseEnd_6185731 < baseStart_6185731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185747 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6]
def baseStart_6185747 : Nat := 118140960795 + 6185747 * 2 ^ 59
def prefixEnd_6185747 : Nat := 4983230072969 + 3 ^ 40 * 6185747 * 2
def baseEnd_6185747 : Nat := 3176261418107314970114773

theorem tailTrace_6185747 : CollatzResearch.WordTrace tailWord_6185747 prefixEnd_6185747 3176261418107314970114773 := by
  unfold tailWord_6185747
  simp only [CollatzResearch.WordTrace]
  refine ⟨225612727921102535325107495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150408485280735023550071663 225612727921102535325107495)
  ·
    refine ⟨338419091881653802987661243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225612727921102535325107495 338419091881653802987661243)
    ·
      refine ⟨507628637822480704481491865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338419091881653802987661243 507628637822480704481491865)
      ·
        refine ⟨380721478366860528361118899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507628637822480704481491865 380721478366860528361118899)
        ·
          refine ⟨571082217550290792541678349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380721478366860528361118899 571082217550290792541678349)
          ·
            refine ⟨214155831581359047203129381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 571082217550290792541678349 214155831581359047203129381)
            ·
              refine ⟨40154218421504821350586759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214155831581359047203129381 40154218421504821350586759)
              ·
                refine ⟨60231327632257232025880139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40154218421504821350586759 60231327632257232025880139)
                ·
                  refine ⟨90346991448385848038820209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60231327632257232025880139 90346991448385848038820209)
                  ·
                    refine ⟨67760243586289386029115157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90346991448385848038820209 67760243586289386029115157)
                    ·
                      refine ⟨3176261418107314970114773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67760243586289386029115157 3176261418107314970114773)
                      ·
                        rfl

theorem cell23_6185747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_6185747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185747 prefixEnd_6185747 := by exact prefixLift 6185747
  have htrace : WordTrace (prefixWord ++ tailWord_6185747) baseStart_6185747 baseEnd_6185747 := by
    simpa [prefixWord, tailWord_6185747, baseEnd_6185747] using wordTrace_append hprefix tailTrace_6185747
  have hstable : (prefixWord ++ tailWord_6185747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185747).length < 2 ^ (prefixWord ++ tailWord_6185747).sum := by decide
  have hdescent : baseEnd_6185747 < baseStart_6185747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185782 : List Nat := [5, 1, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_6185782 : Nat := 118140960795 + 6185782 * 2 ^ 59
def prefixEnd_6185782 : Nat := 4983230072969 + 3 ^ 40 * 6185782 * 2
def baseEnd_6185782 : Nat := 1058759796643407444392371

theorem tailTrace_6185782 : CollatzResearch.WordTrace tailWord_6185782 prefixEnd_6185782 1058759796643407444392371 := by
  unfold tailWord_6185782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14100875279748483518914475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150409336317317157535087733 14100875279748483518914475)
  ·
    refine ⟨21151312919622725278371713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14100875279748483518914475 21151312919622725278371713)
    ·
      refine ⟨15863484689717043958778785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21151312919622725278371713 15863484689717043958778785)
      ·
        refine ⟨11897613517287782969084089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15863484689717043958778785 11897613517287782969084089)
        ·
          refine ⟨8923210137965837226813067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11897613517287782969084089 8923210137965837226813067)
          ·
            refine ⟨13384815206948755840219601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923210137965837226813067 13384815206948755840219601)
            ·
              refine ⟨10038611405211566880164701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13384815206948755840219601 10038611405211566880164701)
              ·
                refine ⟨3764479276954337580061763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10038611405211566880164701 3764479276954337580061763)
                ·
                  refine ⟨5646718915431506370092645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764479276954337580061763 5646718915431506370092645)
                  ·
                    refine ⟨1058759796643407444392371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646718915431506370092645 1058759796643407444392371)
                    ·
                      rfl

theorem cell23_6185782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_6185782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185782 prefixEnd_6185782 := by exact prefixLift 6185782
  have htrace : WordTrace (prefixWord ++ tailWord_6185782) baseStart_6185782 baseEnd_6185782 := by
    simpa [prefixWord, tailWord_6185782, baseEnd_6185782] using wordTrace_append hprefix tailTrace_6185782
  have hstable : (prefixWord ++ tailWord_6185782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185782).length < 2 ^ (prefixWord ++ tailWord_6185782).sum := by decide
  have hdescent : baseEnd_6185782 < baseStart_6185782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185791 : List Nat := [1, 1, 2, 2, 5, 2, 1, 3, 1, 5]
def baseStart_6185791 : Nat := 118140960795 + 6185791 * 2 ^ 59
def prefixEnd_6185791 : Nat := 4983230072969 + 3 ^ 40 * 6185791 * 2
def baseEnd_6185791 : Nat := 1058761337085370932654857

theorem tailTrace_6185791 : CollatzResearch.WordTrace tailWord_6185791 prefixEnd_6185791 1058761337085370932654857 := by
  unfold tailWord_6185791
  simp only [CollatzResearch.WordTrace]
  refine ⟨225614332732943130839709227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150409555155295420559806151 225614332732943130839709227)
  ·
    refine ⟨338421499099414696259563841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225614332732943130839709227 338421499099414696259563841)
    ·
      refine ⟨253816124324561022194672881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338421499099414696259563841 253816124324561022194672881)
      ·
        refine ⟨190362093243420766646004661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253816124324561022194672881 190362093243420766646004661)
        ·
          refine ⟨17846446241570696873062937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190362093243420766646004661 17846446241570696873062937)
          ·
            refine ⟨13384834681178022654797203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17846446241570696873062937 13384834681178022654797203)
            ·
              refine ⟨20077252021767033982195805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13384834681178022654797203 20077252021767033982195805)
              ·
                refine ⟨7528969508162637743323427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20077252021767033982195805 7528969508162637743323427)
                ·
                  refine ⟨11293454262243956614985141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528969508162637743323427 11293454262243956614985141)
                  ·
                    refine ⟨1058761337085370932654857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11293454262243956614985141 1058761337085370932654857)
                    ·
                      rfl

theorem cell23_6185791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_6185791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185791 prefixEnd_6185791 := by exact prefixLift 6185791
  have htrace : WordTrace (prefixWord ++ tailWord_6185791) baseStart_6185791 baseEnd_6185791 := by
    simpa [prefixWord, tailWord_6185791, baseEnd_6185791] using wordTrace_append hprefix tailTrace_6185791
  have hstable : (prefixWord ++ tailWord_6185791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185791).length < 2 ^ (prefixWord ++ tailWord_6185791).sum := by decide
  have hdescent : baseEnd_6185791 < baseStart_6185791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185824 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6]
def baseStart_6185824 : Nat := 118140960795 + 6185824 * 2 ^ 59
def prefixEnd_6185824 : Nat := 4983230072969 + 3 ^ 40 * 6185824 * 2
def baseEnd_6185824 : Nat := 3176300956117711168851919

theorem tailTrace_6185824 : CollatzResearch.WordTrace tailWord_6185824 prefixEnd_6185824 3176300956117711168851919 := by
  unfold tailWord_6185824
  simp only [CollatzResearch.WordTrace]
  refine ⟨112807768170911788737830263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150410357561215718317107017 112807768170911788737830263)
  ·
    refine ⟨169211652256367683106745395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112807768170911788737830263 169211652256367683106745395)
    ·
      refine ⟨253817478384551524660118093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169211652256367683106745395 253817478384551524660118093)
      ·
        refine ⟨95181554394206821747544285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 253817478384551524660118093 95181554394206821747544285)
        ·
          refine ⟨35693082897827558155329107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95181554394206821747544285 35693082897827558155329107)
          ·
            refine ⟨53539624346741337232993661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35693082897827558155329107 53539624346741337232993661)
            ·
              refine ⟨20077359130028001462372623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53539624346741337232993661 20077359130028001462372623)
              ·
                refine ⟨30116038695042002193558935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20077359130028001462372623 30116038695042002193558935)
                ·
                  refine ⟨45174058042563003290338403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30116038695042002193558935 45174058042563003290338403)
                  ·
                    refine ⟨67761087063844504935507605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45174058042563003290338403 67761087063844504935507605)
                    ·
                      refine ⟨3176300956117711168851919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67761087063844504935507605 3176300956117711168851919)
                      ·
                        rfl

theorem cell23_6185824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_6185824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185824 prefixEnd_6185824 := by exact prefixLift 6185824
  have htrace : WordTrace (prefixWord ++ tailWord_6185824) baseStart_6185824 baseEnd_6185824 := by
    simpa [prefixWord, tailWord_6185824, baseEnd_6185824] using wordTrace_append hprefix tailTrace_6185824
  have hstable : (prefixWord ++ tailWord_6185824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185824).length < 2 ^ (prefixWord ++ tailWord_6185824).sum := by decide
  have hdescent : baseEnd_6185824 < baseStart_6185824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185828 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_6185828 : Nat := 118140960795 + 6185828 * 2 ^ 59
def prefixEnd_6185828 : Nat := 4983230072969 + 3 ^ 40 * 6185828 * 2
def baseEnd_6185828 : Nat := 3176303010040329153201901

theorem tailTrace_6185828 : CollatzResearch.WordTrace tailWord_6185828 prefixEnd_6185828 3176303010040329153201901 := by
  unfold tailWord_6185828
  simp only [CollatzResearch.WordTrace]
  refine ⟨112807841116904543079403069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150410454822539390772537425 112807841116904543079403069)
  ·
    refine ⟨42302940418839203654776151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112807841116904543079403069 42302940418839203654776151)
    ·
      refine ⟨63454410628258805482164227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42302940418839203654776151 63454410628258805482164227)
      ·
        refine ⟨95181615942388208223246341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63454410628258805482164227 95181615942388208223246341)
        ·
          refine ⟨17846552989197789041858689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95181615942388208223246341 17846552989197789041858689)
          ·
            refine ⟨13384914741898341781394017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17846552989197789041858689 13384914741898341781394017)
            ·
              refine ⟨10038686056423756336045513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13384914741898341781394017 10038686056423756336045513)
              ·
                refine ⟨7529014542317817252034135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10038686056423756336045513 7529014542317817252034135)
                ·
                  refine ⟨11293521813476725878051203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529014542317817252034135 11293521813476725878051203)
                  ·
                    refine ⟨16940282720215088817076805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11293521813476725878051203 16940282720215088817076805)
                    ·
                      refine ⟨3176303010040329153201901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16940282720215088817076805 3176303010040329153201901)
                      ·
                        rfl

theorem cell23_6185828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_6185828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185828 prefixEnd_6185828 := by exact prefixLift 6185828
  have htrace : WordTrace (prefixWord ++ tailWord_6185828) baseStart_6185828 baseEnd_6185828 := by
    simpa [prefixWord, tailWord_6185828, baseEnd_6185828] using wordTrace_append hprefix tailTrace_6185828
  have hstable : (prefixWord ++ tailWord_6185828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185828).length < 2 ^ (prefixWord ++ tailWord_6185828).sum := by decide
  have hdescent : baseEnd_6185828 < baseStart_6185828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185882 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3]
def baseStart_6185882 : Nat := 118140960795 + 6185882 * 2 ^ 59
def prefixEnd_6185882 : Nat := 4983230072969 + 3 ^ 40 * 6185882 * 2
def baseEnd_6185882 : Nat := 3176330737995671941926653

theorem tailTrace_6185882 : CollatzResearch.WordTrace tailWord_6185882 prefixEnd_6185882 3176330737995671941926653 := by
  unfold tailWord_6185882
  simp only [CollatzResearch.WordTrace]
  refine ⟨56404412943903363345317975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150411767850408968920847933 56404412943903363345317975)
  ·
    refine ⟨84606619415855045017976963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56404412943903363345317975 84606619415855045017976963)
    ·
      refine ⟨126909929123782567526965445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84606619415855045017976963 126909929123782567526965445)
      ·
        refine ⟨23795611710709231411306021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126909929123782567526965445 23795611710709231411306021)
        ·
          refine ⟨4461677195757980889619879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23795611710709231411306021 4461677195757980889619879)
          ·
            refine ⟨6692515793636971334429819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461677195757980889619879 6692515793636971334429819)
            ·
              refine ⟨10038773690455457001644729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692515793636971334429819 10038773690455457001644729)
              ·
                refine ⟨7529080267841592751233547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10038773690455457001644729 7529080267841592751233547)
                ·
                  refine ⟨11293620401762389126850321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529080267841592751233547 11293620401762389126850321)
                  ·
                    refine ⟨8470215301321791845137741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11293620401762389126850321 8470215301321791845137741)
                    ·
                      refine ⟨3176330737995671941926653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8470215301321791845137741 3176330737995671941926653)
                      ·
                        rfl

theorem cell23_6185882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_6185882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185882 prefixEnd_6185882 := by exact prefixLift 6185882
  have htrace : WordTrace (prefixWord ++ tailWord_6185882) baseStart_6185882 baseEnd_6185882 := by
    simpa [prefixWord, tailWord_6185882, baseEnd_6185882] using wordTrace_append hprefix tailTrace_6185882
  have hstable : (prefixWord ++ tailWord_6185882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185882).length < 2 ^ (prefixWord ++ tailWord_6185882).sum := by decide
  have hdescent : baseEnd_6185882 < baseStart_6185882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185918 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_6185918 : Nat := 118140960795 + 6185918 * 2 ^ 59
def prefixEnd_6185918 : Nat := 4983230072969 + 3 ^ 40 * 6185918 * 2
def baseEnd_6185918 : Nat := 3176349223299233801076487

theorem tailTrace_6185918 : CollatzResearch.WordTrace tailWord_6185918 prefixEnd_6185918 3176349223299233801076487 := by
  unfold tailWord_6185918
  simp only [CollatzResearch.WordTrace]
  refine ⟨28202370600435378941197801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150412643202322021019721605 28202370600435378941197801)
  ·
    refine ⟨21151777950326534205898351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28202370600435378941197801 21151777950326534205898351)
    ·
      refine ⟨31727666925489801308847527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21151777950326534205898351 31727666925489801308847527)
      ·
        refine ⟨47591500388234701963271291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31727666925489801308847527 47591500388234701963271291)
        ·
          refine ⟨71387250582352052944906937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47591500388234701963271291 71387250582352052944906937)
          ·
            refine ⟨53540437936764039708680203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71387250582352052944906937 53540437936764039708680203)
            ·
              refine ⟨80310656905146059563020305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53540437936764039708680203 80310656905146059563020305)
              ·
                refine ⟨60232992678859544672265229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80310656905146059563020305 60232992678859544672265229)
                ·
                  refine ⟨22587372254572329252099461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60232992678859544672265229 22587372254572329252099461)
                  ·
                    refine ⟨4235132297732311734768649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22587372254572329252099461 4235132297732311734768649)
                    ·
                      refine ⟨3176349223299233801076487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235132297732311734768649 3176349223299233801076487)
                      ·
                        rfl

theorem cell23_6185918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_6185918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185918 prefixEnd_6185918 := by exact prefixLift 6185918
  have htrace : WordTrace (prefixWord ++ tailWord_6185918) baseStart_6185918 baseEnd_6185918 := by
    simpa [prefixWord, tailWord_6185918, baseEnd_6185918] using wordTrace_append hprefix tailTrace_6185918
  have hstable : (prefixWord ++ tailWord_6185918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185918).length < 2 ^ (prefixWord ++ tailWord_6185918).sum := by decide
  have hdescent : baseEnd_6185918 < baseStart_6185918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185931 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4]
def baseStart_6185931 : Nat := 118140960795 + 6185931 * 2 ^ 59
def prefixEnd_6185931 : Nat := 4983230072969 + 3 ^ 40 * 6185931 * 2
def baseEnd_6185931 : Nat := 3176355898547742250213927

theorem tailTrace_6185931 : CollatzResearch.WordTrace tailWord_6185931 prefixEnd_6185931 3176355898547742250213927 := by
  unfold tailWord_6185931
  simp only [CollatzResearch.WordTrace]
  refine ⟨225619438952435934749805647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150412959301623956499870431 225619438952435934749805647)
  ·
    refine ⟨338429158428653902124708471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225619438952435934749805647 338429158428653902124708471)
    ·
      refine ⟨507643737642980853187062707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338429158428653902124708471 507643737642980853187062707)
      ·
        refine ⟨761465606464471279780594061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507643737642980853187062707 761465606464471279780594061)
        ·
          refine ⟨285549602424176729917722773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 761465606464471279780594061 285549602424176729917722773)
          ·
            refine ⟨13385137613633284214893255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 285549602424176729917722773 13385137613633284214893255)
            ·
              refine ⟨20077706420449926322339883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13385137613633284214893255 20077706420449926322339883)
              ·
                refine ⟨30116559630674889483509825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20077706420449926322339883 30116559630674889483509825)
                ·
                  refine ⟨22587419723006167112632369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30116559630674889483509825 22587419723006167112632369)
                  ·
                    refine ⟨16940564792254625334474277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22587419723006167112632369 16940564792254625334474277)
                    ·
                      refine ⟨3176355898547742250213927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16940564792254625334474277 3176355898547742250213927)
                      ·
                        rfl

theorem cell23_6185931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 4].length) (baseStart_6185931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185931 prefixEnd_6185931 := by exact prefixLift 6185931
  have htrace : WordTrace (prefixWord ++ tailWord_6185931) baseStart_6185931 baseEnd_6185931 := by
    simpa [prefixWord, tailWord_6185931, baseEnd_6185931] using wordTrace_append hprefix tailTrace_6185931
  have hstable : (prefixWord ++ tailWord_6185931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185931).length < 2 ^ (prefixWord ++ tailWord_6185931).sum := by decide
  have hdescent : baseEnd_6185931 < baseStart_6185931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185935 : List Nat := [1, 1, 2, 1, 1, 6, 2, 3, 2, 2, 2]
def baseStart_6185935 : Nat := 118140960795 + 6185935 * 2 ^ 59
def prefixEnd_6185935 : Nat := 4983230072969 + 3 ^ 40 * 6185935 * 2
def baseEnd_6185935 : Nat := 3176357952470360234563909

theorem tailTrace_6185935 : CollatzResearch.WordTrace tailWord_6185935 prefixEnd_6185935 3176357952470360234563909 := by
  unfold tailWord_6185935
  simp only [CollatzResearch.WordTrace]
  refine ⟨225619584844421443432951259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150413056562947628955300839 225619584844421443432951259)
  ·
    refine ⟨338429377266632165149426889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225619584844421443432951259 338429377266632165149426889)
    ·
      refine ⟨253822032949974123862070167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338429377266632165149426889 253822032949974123862070167)
      ·
        refine ⟨380733049424961185793105251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253822032949974123862070167 380733049424961185793105251)
        ·
          refine ⟨571099574137441778689657877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380733049424961185793105251 571099574137441778689657877)
          ·
            refine ⟨26770292537692583376077713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 571099574137441778689657877 26770292537692583376077713)
            ·
              refine ⟨20077719403269437532058285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26770292537692583376077713 20077719403269437532058285)
              ·
                refine ⟨7529144776226039074521857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20077719403269437532058285 7529144776226039074521857)
                ·
                  refine ⟨5646858582169529305891393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7529144776226039074521857 5646858582169529305891393)
                  ·
                    refine ⟨4235143936627146979418545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5646858582169529305891393 4235143936627146979418545)
                    ·
                      refine ⟨3176357952470360234563909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235143936627146979418545 3176357952470360234563909)
                      ·
                        rfl

theorem cell23_6185935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 2, 2].length) (baseStart_6185935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185935 prefixEnd_6185935 := by exact prefixLift 6185935
  have htrace : WordTrace (prefixWord ++ tailWord_6185935) baseStart_6185935 baseEnd_6185935 := by
    simpa [prefixWord, tailWord_6185935, baseEnd_6185935] using wordTrace_append hprefix tailTrace_6185935
  have hstable : (prefixWord ++ tailWord_6185935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185935).length < 2 ^ (prefixWord ++ tailWord_6185935).sum := by decide
  have hdescent : baseEnd_6185935 < baseStart_6185935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185986 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6185986 : Nat := 118140960795 + 6185986 * 2 ^ 59
def prefixEnd_6185986 : Nat := 4983230072969 + 3 ^ 40 * 6185986 * 2
def baseEnd_6185986 : Nat := 3176384139983739535026175

theorem tailTrace_6185986 : CollatzResearch.WordTrace tailWord_6185986 prefixEnd_6185986 3176384139983739535026175 := by
  unfold tailWord_6185986
  simp only [CollatzResearch.WordTrace]
  refine ⟨56405361241809169785764453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150414296644824452762038541 56405361241809169785764453)
  ·
    refine ⟨10576005232839219334830835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56405361241809169785764453 10576005232839219334830835)
    ·
      refine ⟨15864007849258829002246253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10576005232839219334830835 15864007849258829002246253)
      ·
        refine ⟨5949002943472060875842345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15864007849258829002246253 5949002943472060875842345)
        ·
          refine ⟨4461752207604045656881759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5949002943472060875842345 4461752207604045656881759)
          ·
            refine ⟨6692628311406068485322639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461752207604045656881759 6692628311406068485322639)
            ·
              refine ⟨10038942467109102727983959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692628311406068485322639 10038942467109102727983959)
              ·
                refine ⟨15058413700663654091975939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10038942467109102727983959 15058413700663654091975939)
                ·
                  refine ⟨22587620550995481137963909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15058413700663654091975939 22587620550995481137963909)
                  ·
                    refine ⟨4235178853311652713368233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22587620550995481137963909 4235178853311652713368233)
                    ·
                      refine ⟨3176384139983739535026175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235178853311652713368233 3176384139983739535026175)
                      ·
                        rfl

theorem cell23_6185986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6185986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185986 prefixEnd_6185986 := by exact prefixLift 6185986
  have htrace : WordTrace (prefixWord ++ tailWord_6185986) baseStart_6185986 baseEnd_6185986 := by
    simpa [prefixWord, tailWord_6185986, baseEnd_6185986] using wordTrace_append hprefix tailTrace_6185986
  have hstable : (prefixWord ++ tailWord_6185986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185986).length < 2 ^ (prefixWord ++ tailWord_6185986).sum := by decide
  have hdescent : baseEnd_6185986 < baseStart_6185986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6185991 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6185991 : Nat := 118140960795 + 6185991 * 2 ^ 59
def prefixEnd_6185991 : Nat := 4983230072969 + 3 ^ 40 * 6185991 * 2
def baseEnd_6185991 : Nat := 3176386707387012015463651

theorem tailTrace_6185991 : CollatzResearch.WordTrace tailWord_6185991 prefixEnd_6185991 3176386707387012015463651 := by
  unfold tailWord_6185991
  simp only [CollatzResearch.WordTrace]
  refine ⟨225621627332218564996989827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150414418221479043331326551 225621627332218564996989827)
  ·
    refine ⟨338432440998327847495484741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225621627332218564996989827 338432440998327847495484741)
    ·
      refine ⟨63456082687186471405403389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338432440998327847495484741 63456082687186471405403389)
      ·
        refine ⟨23796031007694926777026271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63456082687186471405403389 23796031007694926777026271)
        ·
          refine ⟨35694046511542390165539407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23796031007694926777026271 35694046511542390165539407)
          ·
            refine ⟨53541069767313585248309111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35694046511542390165539407 53541069767313585248309111)
            ·
              refine ⟨80311604650970377872463667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53541069767313585248309111 80311604650970377872463667)
              ·
                refine ⟨120467406976455566808695501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80311604650970377872463667 120467406976455566808695501)
                ·
                  refine ⟨45175277616170837553260813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120467406976455566808695501 45175277616170837553260813)
                  ·
                    refine ⟨16940729106064064082472805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45175277616170837553260813 16940729106064064082472805)
                    ·
                      refine ⟨3176386707387012015463651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16940729106064064082472805 3176386707387012015463651)
                      ·
                        rfl

theorem cell23_6185991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6185991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6185991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6185991 prefixEnd_6185991 := by exact prefixLift 6185991
  have htrace : WordTrace (prefixWord ++ tailWord_6185991) baseStart_6185991 baseEnd_6185991 := by
    simpa [prefixWord, tailWord_6185991, baseEnd_6185991] using wordTrace_append hprefix tailTrace_6185991
  have hstable : (prefixWord ++ tailWord_6185991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6185991).length < 2 ^ (prefixWord ++ tailWord_6185991).sum := by decide
  have hdescent : baseEnd_6185991 < baseStart_6185991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6185991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186028 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 3]
def baseStart_6186028 : Nat := 118140960795 + 6186028 * 2 ^ 59
def prefixEnd_6186028 : Nat := 4983230072969 + 3 ^ 40 * 6186028 * 2
def baseEnd_6186028 : Nat := 3176405706171228370700981

theorem tailTrace_6186028 : CollatzResearch.WordTrace tailWord_6186028 prefixEnd_6186028 3176405706171228370700981 := by
  unfold tailWord_6186028
  simp only [CollatzResearch.WordTrace]
  refine ⟨112811488416542260158043369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150415317888723013544057825 112811488416542260158043369)
  ·
    refine ⟨84608616312406695118532527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112811488416542260158043369 84608616312406695118532527)
    ·
      refine ⟨126912924468610042677798791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84608616312406695118532527 126912924468610042677798791)
      ·
        refine ⟨190369386702915064016698187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126912924468610042677798791 190369386702915064016698187)
        ·
          refine ⟨285554080054372596025047281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190369386702915064016698187 285554080054372596025047281)
          ·
            refine ⟨214165560040779447018785461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285554080054372596025047281 214165560040779447018785461)
            ·
              refine ⟨20078021253823073158011137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214165560040779447018785461 20078021253823073158011137)
              ·
                refine ⟨15058515940367304868508353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20078021253823073158011137 15058515940367304868508353)
                ·
                  refine ⟨11293886955275478651381265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15058515940367304868508353 11293886955275478651381265)
                  ·
                    refine ⟨8470415216456608988535949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11293886955275478651381265 8470415216456608988535949)
                    ·
                      refine ⟨3176405706171228370700981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8470415216456608988535949 3176405706171228370700981)
                      ·
                        rfl

theorem cell23_6186028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 3].length) (baseStart_6186028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186028 prefixEnd_6186028 := by exact prefixLift 6186028
  have htrace : WordTrace (prefixWord ++ tailWord_6186028) baseStart_6186028 baseEnd_6186028 := by
    simpa [prefixWord, tailWord_6186028, baseEnd_6186028] using wordTrace_append hprefix tailTrace_6186028
  have hstable : (prefixWord ++ tailWord_6186028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186028).length < 2 ^ (prefixWord ++ tailWord_6186028).sum := by decide
  have hdescent : baseEnd_6186028 < baseStart_6186028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186085 : List Nat := [1, 3, 1, 3, 2, 1, 1, 4, 2, 3, 2]
def baseStart_6186085 : Nat := 118140960795 + 6186085 * 2 ^ 59
def prefixEnd_6186085 : Nat := 4983230072969 + 3 ^ 40 * 6186085 * 2
def baseEnd_6186085 : Nat := 3176434974568534647688219

theorem tailTrace_6186085 : CollatzResearch.WordTrace tailWord_6186085 prefixEnd_6186085 3176434974568534647688219 := by
  unfold tailWord_6186085
  simp only [CollatzResearch.WordTrace]
  refine ⟨225625055793878019050911709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150416703862585346033941139 225625055793878019050911709)
  ·
    refine ⟨84609395922704257144091891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225625055793878019050911709 84609395922704257144091891)
    ·
      refine ⟨126914093884056385716137837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84609395922704257144091891 126914093884056385716137837)
      ·
        refine ⟨47592785206521144643551689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126914093884056385716137837 47592785206521144643551689)
        ·
          refine ⟨35694588904890858482663767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47592785206521144643551689 35694588904890858482663767)
          ·
            refine ⟨53541883357336287723995651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35694588904890858482663767 53541883357336287723995651)
            ·
              refine ⟨80312825036004431585993477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53541883357336287723995651 80312825036004431585993477)
              ·
                refine ⟨15058654694250830922373777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80312825036004431585993477 15058654694250830922373777)
                ·
                  refine ⟨11293991020688123191780333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15058654694250830922373777 11293991020688123191780333)
                  ·
                    refine ⟨4235246632758046196917625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11293991020688123191780333 4235246632758046196917625)
                    ·
                      refine ⟨3176434974568534647688219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235246632758046196917625 3176434974568534647688219)
                      ·
                        rfl

theorem cell23_6186085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_6186085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186085 prefixEnd_6186085 := by exact prefixLift 6186085
  have htrace : WordTrace (prefixWord ++ tailWord_6186085) baseStart_6186085 baseEnd_6186085 := by
    simpa [prefixWord, tailWord_6186085, baseEnd_6186085] using wordTrace_append hprefix tailTrace_6186085
  have hstable : (prefixWord ++ tailWord_6186085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186085).length < 2 ^ (prefixWord ++ tailWord_6186085).sum := by decide
  have hdescent : baseEnd_6186085 < baseStart_6186085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186092 : List Nat := [2, 2, 1, 1, 3, 2, 3, 4, 1, 1, 3]
def baseStart_6186092 : Nat := 118140960795 + 6186092 * 2 ^ 59
def prefixEnd_6186092 : Nat := 4983230072969 + 3 ^ 40 * 6186092 * 2
def baseEnd_6186092 : Nat := 3176438568933116120300687

theorem tailTrace_6186092 : CollatzResearch.WordTrace tailWord_6186092 prefixEnd_6186092 3176438568933116120300687 := by
  unfold tailWord_6186092
  simp only [CollatzResearch.WordTrace]
  refine ⟨112812655552426329623208265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150416874069901772830944353 112812655552426329623208265)
  ·
    refine ⟨84609491664319747217406199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112812655552426329623208265 84609491664319747217406199)
    ·
      refine ⟨126914237496479620826109299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84609491664319747217406199 126914237496479620826109299)
      ·
        refine ⟨190371356244719431239163949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126914237496479620826109299 190371356244719431239163949)
        ·
          refine ⟨71389258591769786714686481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190371356244719431239163949 71389258591769786714686481)
          ·
            refine ⟨53541943943827340036014861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71389258591769786714686481 53541943943827340036014861)
            ·
              refine ⟨20078228978935252513505573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53541943943827340036014861 20078228978935252513505573)
              ·
                refine ⟨3764667933550359846282295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20078228978935252513505573 3764667933550359846282295)
                ·
                  refine ⟨5647001900325539769423443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764667933550359846282295 5647001900325539769423443)
                  ·
                    refine ⟨8470502850488309654135165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5647001900325539769423443 8470502850488309654135165)
                    ·
                      refine ⟨3176438568933116120300687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8470502850488309654135165 3176438568933116120300687)
                      ·
                        rfl

theorem cell23_6186092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 4, 1, 1, 3].length) (baseStart_6186092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186092 prefixEnd_6186092 := by exact prefixLift 6186092
  have htrace : WordTrace (prefixWord ++ tailWord_6186092) baseStart_6186092 baseEnd_6186092 := by
    simpa [prefixWord, tailWord_6186092, baseEnd_6186092] using wordTrace_append hprefix tailTrace_6186092
  have hstable : (prefixWord ++ tailWord_6186092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186092).length < 2 ^ (prefixWord ++ tailWord_6186092).sum := by decide
  have hdescent : baseEnd_6186092 < baseStart_6186092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186098 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_6186098 : Nat := 118140960795 + 6186098 * 2 ^ 59
def prefixEnd_6186098 : Nat := 4983230072969 + 3 ^ 40 * 6186098 * 2
def baseEnd_6186098 : Nat := 3176441649817043096825659

theorem tailTrace_6186098 : CollatzResearch.WordTrace tailWord_6186098 prefixEnd_6186098 3176441649817043096825659 := by
  unfold tailWord_6186098
  simp only [CollatzResearch.WordTrace]
  refine ⟨56406382485707730567783737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150417019961887281514089965 56406382485707730567783737)
  ·
    refine ⟨42304786864280797925837803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56406382485707730567783737 42304786864280797925837803)
    ·
      refine ⟨63457180296421196888756705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42304786864280797925837803 63457180296421196888756705)
      ·
        refine ⟨47592885222315897666567529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63457180296421196888756705 47592885222315897666567529)
        ·
          refine ⟨35694663916736923249925647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47592885222315897666567529 35694663916736923249925647)
          ·
            refine ⟨53541995875105384874888471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35694663916736923249925647 53541995875105384874888471)
            ·
              refine ⟨80312993812658077312332707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53541995875105384874888471 80312993812658077312332707)
              ·
                refine ⟨120469490718987115968499061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80312993812658077312332707 120469490718987115968499061)
                ·
                  refine ⟨11294014754905042122046787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120469490718987115968499061 11294014754905042122046787)
                  ·
                    refine ⟨16941022132357563183070181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11294014754905042122046787 16941022132357563183070181)
                    ·
                      refine ⟨3176441649817043096825659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16941022132357563183070181 3176441649817043096825659)
                      ·
                        rfl

theorem cell23_6186098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_6186098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186098 prefixEnd_6186098 := by exact prefixLift 6186098
  have htrace : WordTrace (prefixWord ++ tailWord_6186098) baseStart_6186098 baseEnd_6186098 := by
    simpa [prefixWord, tailWord_6186098, baseEnd_6186098] using wordTrace_append hprefix tailTrace_6186098
  have hstable : (prefixWord ++ tailWord_6186098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186098).length < 2 ^ (prefixWord ++ tailWord_6186098).sum := by decide
  have hdescent : baseEnd_6186098 < baseStart_6186098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186108 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 1, 6]
def baseStart_6186108 : Nat := 118140960795 + 6186108 * 2 ^ 59
def prefixEnd_6186108 : Nat := 4983230072969 + 3 ^ 40 * 6186108 * 2
def baseEnd_6186108 : Nat := 1058815594874529352566871

theorem tailTrace_6186108 : CollatzResearch.WordTrace tailWord_6186108 prefixEnd_6186108 1058815594874529352566871 := by
  unfold tailWord_6186108
  simp only [CollatzResearch.WordTrace]
  refine ⟨112812947336397346989499489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150417263115196462652665985 112812947336397346989499489)
  ·
    refine ⟨84609710502298010242124617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112812947336397346989499489 84609710502298010242124617)
    ·
      refine ⟨63457282876723507681593463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84609710502298010242124617 63457282876723507681593463)
      ·
        refine ⟨95185924315085261522390195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63457282876723507681593463 95185924315085261522390195)
        ·
          refine ⟨142778886472627892283585293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95185924315085261522390195 142778886472627892283585293)
          ·
            refine ⟨53542082427235459606344485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142778886472627892283585293 53542082427235459606344485)
            ·
              refine ⟨10039140455106648676189591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53542082427235459606344485 10039140455106648676189591)
              ·
                refine ⟨15058710682659973014284387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10039140455106648676189591 15058710682659973014284387)
                ·
                  refine ⟨22588066023989959521426581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15058710682659973014284387 22588066023989959521426581)
                  ·
                    refine ⟨1058815594874529352566871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22588066023989959521426581 1058815594874529352566871)
                    ·
                      rfl

theorem cell23_6186108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_6186108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186108 prefixEnd_6186108 := by exact prefixLift 6186108
  have htrace : WordTrace (prefixWord ++ tailWord_6186108) baseStart_6186108 baseEnd_6186108 := by
    simpa [prefixWord, tailWord_6186108, baseEnd_6186108] using wordTrace_append hprefix tailTrace_6186108
  have hstable : (prefixWord ++ tailWord_6186108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186108).length < 2 ^ (prefixWord ++ tailWord_6186108).sum := by decide
  have hdescent : baseEnd_6186108 < baseStart_6186108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186138 : List Nat := [3, 1, 1, 5, 1, 2, 10]
def baseStart_6186138 : Nat := 118140960795 + 6186138 * 2 ^ 59
def prefixEnd_6186138 : Nat := 4983230072969 + 3 ^ 40 * 6186138 * 2
def baseEnd_6186138 : Nat := 39215582580780530127475

theorem tailTrace_6186138 : CollatzResearch.WordTrace tailWord_6186138 prefixEnd_6186138 39215582580780530127475 := by
  unfold tailWord_6186138
  simp only [CollatzResearch.WordTrace]
  refine ⟨56406747215671502275647767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150417992575124006068394045 56406747215671502275647767)
  ·
    refine ⟨84610120823507253413471651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56406747215671502275647767 84610120823507253413471651)
    ·
      refine ⟨126915181235260880120207477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84610120823507253413471651 126915181235260880120207477)
      ·
        refine ⟨11898298240805707511269451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126915181235260880120207477 11898298240805707511269451)
        ·
          refine ⟨17847447361208561266904177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11898298240805707511269451 17847447361208561266904177)
          ·
            refine ⟨13385585520906420950178133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17847447361208561266904177 13385585520906420950178133)
            ·
              refine ⟨39215582580780530127475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13385585520906420950178133 39215582580780530127475)
              ·
                rfl

theorem cell23_6186138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 10].length) (baseStart_6186138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186138 prefixEnd_6186138 := by exact prefixLift 6186138
  have htrace : WordTrace (prefixWord ++ tailWord_6186138) baseStart_6186138 baseEnd_6186138 := by
    simpa [prefixWord, tailWord_6186138, baseEnd_6186138] using wordTrace_append hprefix tailTrace_6186138
  have hstable : (prefixWord ++ tailWord_6186138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186138).length < 2 ^ (prefixWord ++ tailWord_6186138).sum := by decide
  have hdescent : baseEnd_6186138 < baseStart_6186138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186142 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6186142 : Nat := 118140960795 + 6186142 * 2 ^ 59
def prefixEnd_6186142 : Nat := 4983230072969 + 3 ^ 40 * 6186142 * 2
def baseEnd_6186142 : Nat := 1058821414321946974891819

theorem tailTrace_6186142 : CollatzResearch.WordTrace tailWord_6186142 prefixEnd_6186142 1058821414321946974891819 := by
  unfold tailWord_6186142
  simp only [CollatzResearch.WordTrace]
  refine ⟨28203391844333939723217085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150418089836447678523824453 28203391844333939723217085)
  ·
    refine ⟨10576271941625227396206407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28203391844333939723217085 10576271941625227396206407)
    ·
      refine ⟨15864407912437841094309611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10576271941625227396206407 15864407912437841094309611)
      ·
        refine ⟨23796611868656761641464417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15864407912437841094309611 23796611868656761641464417)
        ·
          refine ⟨17847458901492571231098313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23796611868656761641464417 17847458901492571231098313)
          ·
            refine ⟨13385594176119428423323735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17847458901492571231098313 13385594176119428423323735)
            ·
              refine ⟨20078391264179142634985603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13385594176119428423323735 20078391264179142634985603)
              ·
                refine ⟨30117586896268713952478405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20078391264179142634985603 30117586896268713952478405)
                ·
                  refine ⟨5647047543050383866089701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30117586896268713952478405 5647047543050383866089701)
                  ·
                    refine ⟨1058821414321946974891819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5647047543050383866089701 1058821414321946974891819)
                    ·
                      rfl

theorem cell23_6186142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6186142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186142 prefixEnd_6186142 := by exact prefixLift 6186142
  have htrace : WordTrace (prefixWord ++ tailWord_6186142) baseStart_6186142 baseEnd_6186142 := by
    simpa [prefixWord, tailWord_6186142, baseEnd_6186142] using wordTrace_append hprefix tailTrace_6186142
  have hstable : (prefixWord ++ tailWord_6186142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186142).length < 2 ^ (prefixWord ++ tailWord_6186142).sum := by decide
  have hdescent : baseEnd_6186142 < baseStart_6186142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186149 : List Nat := [1, 3, 1, 2, 1, 4, 2, 4, 1, 2, 2]
def baseStart_6186149 : Nat := 118140960795 + 6186149 * 2 ^ 59
def prefixEnd_6186149 : Nat := 4983230072969 + 3 ^ 40 * 6186149 * 2
def baseEnd_6186149 : Nat := 3176467837330422397287925

theorem tailTrace_6186149 : CollatzResearch.WordTrace tailWord_6186149 prefixEnd_6186149 3176467837330422397287925 := by
  unfold tailWord_6186149
  simp only [CollatzResearch.WordTrace]
  refine ⟨225627390065646157981241501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150418260043764105320827667 225627390065646157981241501)
  ·
    refine ⟨84610271274617309242965563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225627390065646157981241501 84610271274617309242965563)
    ·
      refine ⟨126915406911925963864448345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84610271274617309242965563 126915406911925963864448345)
      ·
        refine ⟨95186555183944472898336259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126915406911925963864448345 95186555183944472898336259)
        ·
          refine ⟨142779832775916709347504389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95186555183944472898336259 142779832775916709347504389)
          ·
            refine ⟨26771218645484383002657073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142779832775916709347504389 26771218645484383002657073)
            ·
              refine ⟨20078413984113287251992805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26771218645484383002657073 20078413984113287251992805)
              ·
                refine ⟨3764702622021241359748651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20078413984113287251992805 3764702622021241359748651)
                ·
                  refine ⟨5647053933031862039622977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764702622021241359748651 5647053933031862039622977)
                  ·
                    refine ⟨4235290449773896529717233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5647053933031862039622977 4235290449773896529717233)
                    ·
                      refine ⟨3176467837330422397287925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235290449773896529717233 3176467837330422397287925)
                      ·
                        rfl

theorem cell23_6186149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_6186149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186149 prefixEnd_6186149 := by exact prefixLift 6186149
  have htrace : WordTrace (prefixWord ++ tailWord_6186149) baseStart_6186149 baseEnd_6186149 := by
    simpa [prefixWord, tailWord_6186149, baseEnd_6186149] using wordTrace_append hprefix tailTrace_6186149
  have hstable : (prefixWord ++ tailWord_6186149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186149).length < 2 ^ (prefixWord ++ tailWord_6186149).sum := by decide
  have hdescent : baseEnd_6186149 < baseStart_6186149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186166 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_6186166 : Nat := 118140960795 + 6186166 * 2 ^ 59
def prefixEnd_6186166 : Nat := 4983230072969 + 3 ^ 40 * 6186166 * 2
def baseEnd_6186166 : Nat := 3176476566501548830775347

theorem tailTrace_6186166 : CollatzResearch.WordTrace tailWord_6186166 prefixEnd_6186166 3176476566501548830775347 := by
  unfold tailWord_6186166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14101750631661535617788147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150418673404389713256406901 14101750631661535617788147)
  ·
    refine ⟨21152625947492303426682221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14101750631661535617788147 21152625947492303426682221)
    ·
      refine ⟨7932234730309613785005833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21152625947492303426682221 7932234730309613785005833)
      ·
        refine ⟨5949176047732210338754375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7932234730309613785005833 5949176047732210338754375)
        ·
          refine ⟨8923764071598315508131563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949176047732210338754375 8923764071598315508131563)
          ·
            refine ⟨13385646107397473262197345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923764071598315508131563 13385646107397473262197345)
            ·
              refine ⟨10039234580548104946648009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13385646107397473262197345 10039234580548104946648009)
              ·
                refine ⟨7529425935411078709986007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10039234580548104946648009 7529425935411078709986007)
                ·
                  refine ⟨11294138903116618064979011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529425935411078709986007 11294138903116618064979011)
                  ·
                    refine ⟨16941208354674927097468517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11294138903116618064979011 16941208354674927097468517)
                    ·
                      refine ⟨3176476566501548830775347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16941208354674927097468517 3176476566501548830775347)
                      ·
                        rfl

theorem cell23_6186166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_6186166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186166 prefixEnd_6186166 := by exact prefixLift 6186166
  have htrace : WordTrace (prefixWord ++ tailWord_6186166) baseStart_6186166 baseEnd_6186166 := by
    simpa [prefixWord, tailWord_6186166, baseEnd_6186166] using wordTrace_append hprefix tailTrace_6186166
  have hstable : (prefixWord ++ tailWord_6186166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186166).length < 2 ^ (prefixWord ++ tailWord_6186166).sum := by decide
  have hdescent : baseEnd_6186166 < baseStart_6186166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186171 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8]
def baseStart_6186171 : Nat := 118140960795 + 6186171 * 2 ^ 59
def prefixEnd_6186171 : Nat := 4983230072969 + 3 ^ 40 * 6186171 * 2
def baseEnd_6186171 : Nat := 3176479133904821311212823

theorem tailTrace_6186171 : CollatzResearch.WordTrace tailWord_6186171 prefixEnd_6186171 3176479133904821311212823 := by
  unfold tailWord_6186171
  simp only [CollatzResearch.WordTrace]
  refine ⟨225628192471566455738542367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150418794981044303825694911 225628192471566455738542367)
  ·
    refine ⟨338442288707349683607813551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225628192471566455738542367 338442288707349683607813551)
    ·
      refine ⟨507663433061024525411720327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338442288707349683607813551 507663433061024525411720327)
      ·
        refine ⟨761495149591536788117580491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507663433061024525411720327 761495149591536788117580491)
        ·
          refine ⟨1142242724387305182176370737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761495149591536788117580491 1142242724387305182176370737)
          ·
            refine ⟨856682043290478886632278053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142242724387305182176370737 856682043290478886632278053)
            ·
              refine ⟨160627883116964791243552135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 856682043290478886632278053 160627883116964791243552135)
              ·
                refine ⟨240941824675447186865328203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160627883116964791243552135 240941824675447186865328203)
                ·
                  refine ⟨361412737013170780297992305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240941824675447186865328203 361412737013170780297992305)
                  ·
                    refine ⟨271059552759878085223494229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 361412737013170780297992305 271059552759878085223494229)
                    ·
                      refine ⟨3176479133904821311212823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 271059552759878085223494229 3176479133904821311212823)
                      ·
                        rfl

theorem cell23_6186171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 8].length) (baseStart_6186171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186171 prefixEnd_6186171 := by exact prefixLift 6186171
  have htrace : WordTrace (prefixWord ++ tailWord_6186171) baseStart_6186171 baseEnd_6186171 := by
    simpa [prefixWord, tailWord_6186171, baseEnd_6186171] using wordTrace_append hprefix tailTrace_6186171
  have hstable : (prefixWord ++ tailWord_6186171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186171).length < 2 ^ (prefixWord ++ tailWord_6186171).sum := by decide
  have hdescent : baseEnd_6186171 < baseStart_6186171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186175 : List Nat := [1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 2]
def baseStart_6186175 : Nat := 118140960795 + 6186175 * 2 ^ 59
def prefixEnd_6186175 : Nat := 4983230072969 + 3 ^ 40 * 6186175 * 2
def baseEnd_6186175 : Nat := 3176481187827439295562805

theorem tailTrace_6186175 : CollatzResearch.WordTrace tailWord_6186175 prefixEnd_6186175 3176481187827439295562805 := by
  unfold tailWord_6186175
  simp only [CollatzResearch.WordTrace]
  refine ⟨225628338363551964421687979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150418892242367976281125319 225628338363551964421687979)
  ·
    refine ⟨338442507545327946632531969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225628338363551964421687979 338442507545327946632531969)
    ·
      refine ⟨253831880658995959974398977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338442507545327946632531969 253831880658995959974398977)
      ·
        refine ⟨190373910494246969980799233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253831880658995959974398977 190373910494246969980799233)
        ·
          refine ⟨142780432870685227485599425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190373910494246969980799233 142780432870685227485599425)
          ·
            refine ⟨107085324653013920614199569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142780432870685227485599425 107085324653013920614199569)
            ·
              refine ⟨80313993489760440460649677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107085324653013920614199569 80313993489760440460649677)
              ·
                refine ⟨30117747558660165172743629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80313993489760440460649677 30117747558660165172743629)
                ·
                  refine ⟨11294155334497561939778861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30117747558660165172743629 11294155334497561939778861)
                  ·
                    refine ⟨4235308250436585727417073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11294155334497561939778861 4235308250436585727417073)
                    ·
                      refine ⟨3176481187827439295562805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235308250436585727417073 3176481187827439295562805)
                      ·
                        rfl

theorem cell23_6186175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_6186175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186175 prefixEnd_6186175 := by exact prefixLift 6186175
  have htrace : WordTrace (prefixWord ++ tailWord_6186175) baseStart_6186175 baseEnd_6186175 := by
    simpa [prefixWord, tailWord_6186175, baseEnd_6186175] using wordTrace_append hprefix tailTrace_6186175
  have hstable : (prefixWord ++ tailWord_6186175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186175).length < 2 ^ (prefixWord ++ tailWord_6186175).sum := by decide
  have hdescent : baseEnd_6186175 < baseStart_6186175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186189 : List Nat := [1, 6, 2, 2, 2, 1, 9]
def baseStart_6186189 : Nat := 118140960795 + 6186189 * 2 ^ 59
def prefixEnd_6186189 : Nat := 4983230072969 + 3 ^ 40 * 6186189 * 2
def baseEnd_6186189 : Nat := 39215905883414842478861

theorem tailTrace_6186189 : CollatzResearch.WordTrace tailWord_6186189 prefixEnd_6186189 39215905883414842478861 := by
  unfold tailWord_6186189
  simp only [CollatzResearch.WordTrace]
  refine ⟨225628848985501244812697621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150419232657000829875131747 225628848985501244812697621)
  ·
    refine ⟨10576352296195370850595201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 225628848985501244812697621 10576352296195370850595201)
    ·
      refine ⟨7932264222146528137946401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10576352296195370850595201 7932264222146528137946401)
      ·
        refine ⟨5949198166609896103459801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7932264222146528137946401 5949198166609896103459801)
        ·
          refine ⟨4461898624957422077594851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5949198166609896103459801 4461898624957422077594851)
          ·
            refine ⟨6692847937436133116392277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461898624957422077594851 6692847937436133116392277)
            ·
              refine ⟨39215905883414842478861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6692847937436133116392277 39215905883414842478861)
              ·
                rfl

theorem cell23_6186189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 9].length) (baseStart_6186189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186189 prefixEnd_6186189 := by exact prefixLift 6186189
  have htrace : WordTrace (prefixWord ++ tailWord_6186189) baseStart_6186189 baseEnd_6186189 := by
    simpa [prefixWord, tailWord_6186189, baseEnd_6186189] using wordTrace_append hprefix tailTrace_6186189
  have hstable : (prefixWord ++ tailWord_6186189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186189).length < 2 ^ (prefixWord ++ tailWord_6186189).sum := by decide
  have hdescent : baseEnd_6186189 < baseStart_6186189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186226 : List Nat := [3, 2, 1, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_6186226 : Nat := 118140960795 + 6186226 * 2 ^ 59
def prefixEnd_6186226 : Nat := 4983230072969 + 3 ^ 40 * 6186226 * 2
def baseEnd_6186226 : Nat := 3176507375340818596025071

theorem tailTrace_6186226 : CollatzResearch.WordTrace tailWord_6186226 prefixEnd_6186226 3176507375340818596025071 := by
  unfold tailWord_6186226
  simp only [CollatzResearch.WordTrace]
  refine ⟨56407549621591800032948633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150420132324244800087863021 56407549621591800032948633)
  ·
    refine ⟨42305662216193850024711475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56407549621591800032948633 42305662216193850024711475)
    ·
      refine ⟨63458493324290775037067213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42305662216193850024711475 63458493324290775037067213)
      ·
        refine ⟨23796934996609040638900205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63458493324290775037067213 23796934996609040638900205)
        ·
          refine ⟨8923850623728390239587577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23796934996609040638900205 8923850623728390239587577)
          ·
            refine ⟨6692887967796292679690683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8923850623728390239587577 6692887967796292679690683)
            ·
              refine ⟨10039331951694439019536025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692887967796292679690683 10039331951694439019536025)
              ·
                refine ⟨7529498963770829264652019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10039331951694439019536025 7529498963770829264652019)
                ·
                  refine ⟨11294248445656243896978029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529498963770829264652019 11294248445656243896978029)
                  ·
                    refine ⟨4235343167121091461366761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11294248445656243896978029 4235343167121091461366761)
                    ·
                      refine ⟨3176507375340818596025071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4235343167121091461366761 3176507375340818596025071)
                      ·
                        rfl

theorem cell23_6186226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_6186226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186226 prefixEnd_6186226 := by exact prefixLift 6186226
  have htrace : WordTrace (prefixWord ++ tailWord_6186226) baseStart_6186226 baseEnd_6186226 := by
    simpa [prefixWord, tailWord_6186226, baseEnd_6186226] using wordTrace_append hprefix tailTrace_6186226
  have hstable : (prefixWord ++ tailWord_6186226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186226).length < 2 ^ (prefixWord ++ tailWord_6186226).sum := by decide
  have hdescent : baseEnd_6186226 < baseStart_6186226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186245 : List Nat := [1, 3, 1, 1, 2, 1, 4, 5, 5]
def baseStart_6186245 : Nat := 118140960795 + 6186245 * 2 ^ 59
def prefixEnd_6186245 : Nat := 4983230072969 + 3 ^ 40 * 6186245 * 2
def baseEnd_6186245 : Nat := 352946347941472669076387

theorem tailTrace_6186245 : CollatzResearch.WordTrace tailWord_6186245 prefixEnd_6186245 352946347941472669076387 := by
  unfold tailWord_6186245
  simp only [CollatzResearch.WordTrace]
  refine ⟨225630891473298366376736189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150420594315532244251157459 225630891473298366376736189)
  ·
    refine ⟨84611584302486887391276071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225630891473298366376736189 84611584302486887391276071)
    ·
      refine ⟨126917376453730331086914107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84611584302486887391276071 126917376453730331086914107)
      ·
        refine ⟨190376064680595496630371161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126917376453730331086914107 190376064680595496630371161)
        ·
          refine ⟨142782048510446622472778371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190376064680595496630371161 142782048510446622472778371)
          ·
            refine ⟨214173072765669933709167557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142782048510446622472778371 214173072765669933709167557)
            ·
              refine ⟨40157451143563112570468917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214173072765669933709167557 40157451143563112570468917)
              ·
                refine ⟨3764761044709041803481461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40157451143563112570468917 3764761044709041803481461)
                ·
                  refine ⟨352946347941472669076387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3764761044709041803481461 352946347941472669076387)
                  ·
                    rfl

theorem cell23_6186245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_6186245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186245 prefixEnd_6186245 := by exact prefixLift 6186245
  have htrace : WordTrace (prefixWord ++ tailWord_6186245) baseStart_6186245 baseEnd_6186245 := by
    simpa [prefixWord, tailWord_6186245, baseEnd_6186245] using wordTrace_append hprefix tailTrace_6186245
  have hstable : (prefixWord ++ tailWord_6186245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186245).length < 2 ^ (prefixWord ++ tailWord_6186245).sum := by decide
  have hdescent : baseEnd_6186245 < baseStart_6186245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186272 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3]
def baseStart_6186272 : Nat := 118140960795 + 6186272 * 2 ^ 59
def prefixEnd_6186272 : Nat := 4983230072969 + 3 ^ 40 * 6186272 * 2
def baseEnd_6186272 : Nat := 3176530995450925416049859

theorem tailTrace_6186272 : CollatzResearch.WordTrace tailWord_6186272 prefixEnd_6186272 3176530995450925416049859 := by
  unfold tailWord_6186272
  simp only [CollatzResearch.WordTrace]
  refine ⟨112815938122100274993984535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150421250829467033325312713 112815938122100274993984535)
  ·
    refine ⟨169223907183150412490976803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112815938122100274993984535 169223907183150412490976803)
    ·
      refine ⟨253835860774725618736465205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169223907183150412490976803 253835860774725618736465205)
      ·
        refine ⟨23797111947630526756543613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253835860774725618736465205 23797111947630526756543613)
        ·
          refine ⟨8923916980361447533703855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23797111947630526756543613 8923916980361447533703855)
          ·
            refine ⟨13385875470542171300555783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923916980361447533703855 13385875470542171300555783)
            ·
              refine ⟨20078813205813256950833675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13385875470542171300555783 20078813205813256950833675)
              ·
                refine ⟨30118219808719885426250513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20078813205813256950833675 30118219808719885426250513)
                ·
                  refine ⟨22588664856539914069687885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30118219808719885426250513 22588664856539914069687885)
                  ·
                    refine ⟨8470749321202467776132957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22588664856539914069687885 8470749321202467776132957)
                    ·
                      refine ⟨3176530995450925416049859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8470749321202467776132957 3176530995450925416049859)
                      ·
                        rfl

theorem cell23_6186272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_6186272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186272 prefixEnd_6186272 := by exact prefixLift 6186272
  have htrace : WordTrace (prefixWord ++ tailWord_6186272) baseStart_6186272 baseEnd_6186272 := by
    simpa [prefixWord, tailWord_6186272, baseEnd_6186272] using wordTrace_append hprefix tailTrace_6186272
  have hstable : (prefixWord ++ tailWord_6186272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186272).length < 2 ^ (prefixWord ++ tailWord_6186272).sum := by decide
  have hdescent : baseEnd_6186272 < baseStart_6186272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186385 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 4]
def baseStart_6186385 : Nat := 118140960795 + 6186385 * 2 ^ 59
def prefixEnd_6186385 : Nat := 4983230072969 + 3 ^ 40 * 6186385 * 2
def baseEnd_6186385 : Nat := 3176589018764883473936839

theorem tailTrace_6186385 : CollatzResearch.WordTrace tailWord_6186385 prefixEnd_6186385 3176589018764883473936839 := by
  unfold tailWord_6186385
  simp only [CollatzResearch.WordTrace]
  refine ⟨225635997692791170286832609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150423998461860780191221739 225635997692791170286832609)
  ·
    refine ⟨169226998269593377715124457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225635997692791170286832609 169226998269593377715124457)
    ·
      refine ⟨126920248702195033286343343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169226998269593377715124457 126920248702195033286343343)
      ·
        refine ⟨190380373053292549929515015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126920248702195033286343343 190380373053292549929515015)
        ·
          refine ⟨285570559579938824894272523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190380373053292549929515015 285570559579938824894272523)
          ·
            refine ⟨428355839369908237341408785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285570559579938824894272523 428355839369908237341408785)
            ·
              refine ⟨321266879527431178006056589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428355839369908237341408785 321266879527431178006056589)
              ·
                refine ⟨120475079822786691752271221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 321266879527431178006056589 120475079822786691752271221)
                ·
                  refine ⟨11294538733386252351775427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120475079822786691752271221 11294538733386252351775427)
                  ·
                    refine ⟨16941808100079378527663141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11294538733386252351775427 16941808100079378527663141)
                    ·
                      refine ⟨3176589018764883473936839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16941808100079378527663141 3176589018764883473936839)
                      ·
                        rfl

theorem cell23_6186385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_6186385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186385 prefixEnd_6186385 := by exact prefixLift 6186385
  have htrace : WordTrace (prefixWord ++ tailWord_6186385) baseStart_6186385 baseEnd_6186385 := by
    simpa [prefixWord, tailWord_6186385, baseEnd_6186385] using wordTrace_append hprefix tailTrace_6186385
  have hstable : (prefixWord ++ tailWord_6186385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186385).length < 2 ^ (prefixWord ++ tailWord_6186385).sum := by decide
  have hdescent : baseEnd_6186385 < baseStart_6186385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186399 : List Nat := [1, 1, 2, 5, 1, 4, 1, 2, 1, 5]
def baseStart_6186399 : Nat := 118140960795 + 6186399 * 2 ^ 59
def prefixEnd_6186399 : Nat := 4983230072969 + 3 ^ 40 * 6186399 * 2
def baseEnd_6186399 : Nat := 1058865402498015473053925

theorem tailTrace_6186399 : CollatzResearch.WordTrace tailWord_6186399 prefixEnd_6186399 1058865402498015473053925 := by
  unfold tailWord_6186399
  simp only [CollatzResearch.WordTrace]
  refine ⟨225636508314740450677842251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150424338876493633785228167 225636508314740450677842251)
  ·
    refine ⟨338454762472110676016763377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225636508314740450677842251 338454762472110676016763377)
    ·
      refine ⟨253841071854083007012572533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338454762472110676016763377 253841071854083007012572533)
      ·
        refine ⟨23797600486320281907428675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253841071854083007012572533 23797600486320281907428675)
        ·
          refine ⟨35696400729480422861143013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23797600486320281907428675 35696400729480422861143013)
          ·
            refine ⟨6693075136777579286464315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35696400729480422861143013 6693075136777579286464315)
            ·
              refine ⟨10039612705166368929696473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693075136777579286464315 10039612705166368929696473)
              ·
                refine ⟨7529709528874776697272355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10039612705166368929696473 7529709528874776697272355)
                ·
                  refine ⟨11294564293312165045908533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529709528874776697272355 11294564293312165045908533)
                  ·
                    refine ⟨1058865402498015473053925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11294564293312165045908533 1058865402498015473053925)
                    ·
                      rfl

theorem cell23_6186399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_6186399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186399 prefixEnd_6186399 := by exact prefixLift 6186399
  have htrace : WordTrace (prefixWord ++ tailWord_6186399) baseStart_6186399 baseEnd_6186399 := by
    simpa [prefixWord, tailWord_6186399, baseEnd_6186399] using wordTrace_append hprefix tailTrace_6186399
  have hstable : (prefixWord ++ tailWord_6186399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186399).length < 2 ^ (prefixWord ++ tailWord_6186399).sum := by decide
  have hdescent : baseEnd_6186399 < baseStart_6186399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186425 : List Nat := [1, 2, 1, 4, 4, 11]
def baseStart_6186425 : Nat := 118140960795 + 6186425 * 2 ^ 59
def prefixEnd_6186425 : Nat := 4983230072969 + 3 ^ 40 * 6186425 * 2
def baseEnd_6186425 : Nat := 13072467316835651512085

theorem tailTrace_6186425 : CollatzResearch.WordTrace tailWord_6186425 prefixEnd_6186425 13072467316835651512085 := by
  unfold tailWord_6186425
  simp only [CollatzResearch.WordTrace]
  refine ⟨225637456612646257118288729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150424971075097504745525819 225637456612646257118288729)
  ·
    refine ⟨169228092459484692838716547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 225637456612646257118288729 169228092459484692838716547)
    ·
      refine ⟨253842138689227039258074821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169228092459484692838716547 253842138689227039258074821)
      ·
        refine ⟨47595401004230069860889029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253842138689227039258074821 47595401004230069860889029)
        ·
          refine ⟨8924137688293138098916693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47595401004230069860889029 8924137688293138098916693)
          ·
            refine ⟨13072467316835651512085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8924137688293138098916693 13072467316835651512085)
            ·
              rfl

theorem cell23_6186425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 11].length) (baseStart_6186425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186425 prefixEnd_6186425 := by exact prefixLift 6186425
  have htrace : WordTrace (prefixWord ++ tailWord_6186425) baseStart_6186425 baseEnd_6186425 := by
    simpa [prefixWord, tailWord_6186425, baseEnd_6186425] using wordTrace_append hprefix tailTrace_6186425
  have hstable : (prefixWord ++ tailWord_6186425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186425).length < 2 ^ (prefixWord ++ tailWord_6186425).sum := by decide
  have hdescent : baseEnd_6186425 < baseStart_6186425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186429 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_6186429 : Nat := 118140960795 + 6186429 * 2 ^ 59
def prefixEnd_6186429 : Nat := 4983230072969 + 3 ^ 40 * 6186429 * 2
def baseEnd_6186429 : Nat := 1058870537304560433928879

theorem tailTrace_6186429 : CollatzResearch.WordTrace tailWord_6186429 prefixEnd_6186429 1058870537304560433928879 := by
  unfold tailWord_6186429
  simp only [CollatzResearch.WordTrace]
  refine ⟨225637602504631765801434341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150425068336421177200956227 225637602504631765801434341)
  ·
    refine ⟨42307050469618456087768939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 225637602504631765801434341 42307050469618456087768939)
    ·
      refine ⟨63460575704427684131653409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42307050469618456087768939 63460575704427684131653409)
      ·
        refine ⟨47595431778320763098740057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63460575704427684131653409 47595431778320763098740057)
        ·
          refine ⟨35696573833740572324055043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47595431778320763098740057 35696573833740572324055043)
          ·
            refine ⟨53544860750610858486082565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35696573833740572324055043 53544860750610858486082565)
            ·
              refine ⟨10039661390739535966140481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53544860750610858486082565 10039661390739535966140481)
              ·
                refine ⟨7529746043054651974605361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10039661390739535966140481 7529746043054651974605361)
                ·
                  refine ⟨5647309532290988980954021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7529746043054651974605361 5647309532290988980954021)
                  ·
                    refine ⟨1058870537304560433928879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5647309532290988980954021 1058870537304560433928879)
                    ·
                      rfl

theorem cell23_6186429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_6186429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186429 prefixEnd_6186429 := by exact prefixLift 6186429
  have htrace : WordTrace (prefixWord ++ tailWord_6186429) baseStart_6186429 baseEnd_6186429 := by
    simpa [prefixWord, tailWord_6186429, baseEnd_6186429] using wordTrace_append hprefix tailTrace_6186429
  have hstable : (prefixWord ++ tailWord_6186429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186429).length < 2 ^ (prefixWord ++ tailWord_6186429).sum := by decide
  have hdescent : baseEnd_6186429 < baseStart_6186429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186442 : List Nat := [3, 1, 2, 1, 2, 5, 1, 8]
def baseStart_6186442 : Nat := 118140960795 + 6186442 * 2 ^ 59
def prefixEnd_6186442 : Nat := 4983230072969 + 3 ^ 40 * 6186442 * 2
def baseEnd_6186442 : Nat := 117652529154155175960151

theorem tailTrace_6186442 : CollatzResearch.WordTrace tailWord_6186442 prefixEnd_6186442 117652529154155175960151 := by
  unfold tailWord_6186442
  simp only [CollatzResearch.WordTrace]
  refine ⟨56409519163396167255414395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150425384435723112681105053 56409519163396167255414395)
  ·
    refine ⟨84614278745094250883121593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56409519163396167255414395 84614278745094250883121593)
    ·
      refine ⟨63460709058820688162341195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84614278745094250883121593 63460709058820688162341195)
      ·
        refine ⟨95191063588231032243511793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63460709058820688162341195 95191063588231032243511793)
        ·
          refine ⟨71393297691173274182633845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95191063588231032243511793 71393297691173274182633845)
          ·
            refine ⟨6693121658547494454621923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71393297691173274182633845 6693121658547494454621923)
            ·
              refine ⟨10039682487821241681932885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693121658547494454621923 10039682487821241681932885)
              ·
                refine ⟨117652529154155175960151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10039682487821241681932885 117652529154155175960151)
                ·
                  rfl

theorem cell23_6186442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_6186442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186442 prefixEnd_6186442 := by exact prefixLift 6186442
  have htrace : WordTrace (prefixWord ++ tailWord_6186442) baseStart_6186442 baseEnd_6186442 := by
    simpa [prefixWord, tailWord_6186442, baseEnd_6186442] using wordTrace_append hprefix tailTrace_6186442
  have hstable : (prefixWord ++ tailWord_6186442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186442).length < 2 ^ (prefixWord ++ tailWord_6186442).sum := by decide
  have hdescent : baseEnd_6186442 < baseStart_6186442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186469 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 3]
def baseStart_6186469 : Nat := 118140960795 + 6186469 * 2 ^ 59
def prefixEnd_6186469 : Nat := 4983230072969 + 3 ^ 40 * 6186469 * 2
def baseEnd_6186469 : Nat := 3176632151139861145286453

theorem tailTrace_6186469 : CollatzResearch.WordTrace tailWord_6186469 prefixEnd_6186469 3176632151139861145286453 := by
  unfold tailWord_6186469
  simp only [CollatzResearch.WordTrace]
  refine ⟨225639061424486852632890461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150426040949657901755260307 225639061424486852632890461)
  ·
    refine ⟨84614648034182569737333923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225639061424486852632890461 84614648034182569737333923)
    ·
      refine ⟨126921972051273854606000885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84614648034182569737333923 126921972051273854606000885)
      ·
        refine ⟨11898934879806923869312583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126921972051273854606000885 11898934879806923869312583)
        ·
          refine ⟨17848402319710385803968875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11898934879806923869312583 17848402319710385803968875)
          ·
            refine ⟨26772603479565578705953313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17848402319710385803968875 26772603479565578705953313)
            ·
              refine ⟨20079452609674184029464985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26772603479565578705953313 20079452609674184029464985)
              ·
                refine ⟨15059589457255638022098739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20079452609674184029464985 15059589457255638022098739)
                ·
                  refine ⟨22589384185883457033148109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15059589457255638022098739 22589384185883457033148109)
                  ·
                    refine ⟨8471019069706296387430541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22589384185883457033148109 8471019069706296387430541)
                    ·
                      refine ⟨3176632151139861145286453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8471019069706296387430541 3176632151139861145286453)
                      ·
                        rfl

theorem cell23_6186469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_6186469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186469 prefixEnd_6186469 := by exact prefixLift 6186469
  have htrace : WordTrace (prefixWord ++ tailWord_6186469) baseStart_6186469 baseEnd_6186469 := by
    simpa [prefixWord, tailWord_6186469, baseEnd_6186469] using wordTrace_append hprefix tailTrace_6186469
  have hstable : (prefixWord ++ tailWord_6186469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186469).length < 2 ^ (prefixWord ++ tailWord_6186469).sum := by decide
  have hdescent : baseEnd_6186469 < baseStart_6186469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186475 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4]
def baseStart_6186475 : Nat := 118140960795 + 6186475 * 2 ^ 59
def prefixEnd_6186475 : Nat := 4983230072969 + 3 ^ 40 * 6186475 * 2
def baseEnd_6186475 : Nat := 3176635232023788121811425

theorem tailTrace_6186475 : CollatzResearch.WordTrace tailWord_6186475 prefixEnd_6186475 3176635232023788121811425 := by
  unfold tailWord_6186475
  simp only [CollatzResearch.WordTrace]
  refine ⟨225639280262465115657608879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150426186841643410438405919 225639280262465115657608879)
  ·
    refine ⟨338458920393697673486413319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225639280262465115657608879 338458920393697673486413319)
    ·
      refine ⟨507688380590546510229619979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 338458920393697673486413319 507688380590546510229619979)
      ·
        refine ⟨761532570885819765344429969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507688380590546510229619979 761532570885819765344429969)
        ·
          refine ⟨571149428164364824008322477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761532570885819765344429969 571149428164364824008322477)
          ·
            refine ⟨214181035561636809003120929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 571149428164364824008322477 214181035561636809003120929)
            ·
              refine ⟨160635776671227606752340697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214181035561636809003120929 160635776671227606752340697)
              ·
                refine ⟨120476832503420705064255523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160635776671227606752340697 120476832503420705064255523)
                ·
                  refine ⟨180715248755131057596383285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120476832503420705064255523 180715248755131057596383285)
                  ·
                    refine ⟨16942054570793536649660933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 180715248755131057596383285 16942054570793536649660933)
                    ·
                      refine ⟨3176635232023788121811425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16942054570793536649660933 3176635232023788121811425)
                      ·
                        rfl

theorem cell23_6186475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 5, 4].length) (baseStart_6186475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186475 prefixEnd_6186475 := by exact prefixLift 6186475
  have htrace : WordTrace (prefixWord ++ tailWord_6186475) baseStart_6186475 baseEnd_6186475 := by
    simpa [prefixWord, tailWord_6186475, baseEnd_6186475] using wordTrace_append hprefix tailTrace_6186475
  have hstable : (prefixWord ++ tailWord_6186475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186475).length < 2 ^ (prefixWord ++ tailWord_6186475).sum := by decide
  have hdescent : baseEnd_6186475 < baseStart_6186475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186486 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_6186486 : Nat := 118140960795 + 6186486 * 2 ^ 59
def prefixEnd_6186486 : Nat := 4983230072969 + 3 ^ 40 * 6186486 * 2
def baseEnd_6186486 : Nat := 3176640880310987578773875

theorem tailTrace_6186486 : CollatzResearch.WordTrace tailWord_6186486 prefixEnd_6186486 3176640880310987578773875 := by
  unfold tailWord_6186486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14102480091589079033516207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150426454310283509690839541 14102480091589079033516207)
  ·
    refine ⟨21153720137383618550274311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14102480091589079033516207 21153720137383618550274311)
    ·
      refine ⟨31730580206075427825411467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21153720137383618550274311 31730580206075427825411467)
      ·
        refine ⟨47595870309113141738117201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31730580206075427825411467 47595870309113141738117201)
        ·
          refine ⟨35696902731834856303587901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47595870309113141738117201 35696902731834856303587901)
          ·
            refine ⟨13386338524438071113845463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35696902731834856303587901 13386338524438071113845463)
            ·
              refine ⟨20079507786657106670768195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13386338524438071113845463 20079507786657106670768195)
              ·
                refine ⟨30119261679985660006152293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20079507786657106670768195 30119261679985660006152293)
                ·
                  refine ⟨5647361564997311251153555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30119261679985660006152293 5647361564997311251153555)
                  ·
                    refine ⟨8471042347495966876730333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5647361564997311251153555 8471042347495966876730333)
                    ·
                      refine ⟨3176640880310987578773875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8471042347495966876730333 3176640880310987578773875)
                      ·
                        rfl

theorem cell23_6186486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_6186486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186486 prefixEnd_6186486 := by exact prefixLift 6186486
  have htrace : WordTrace (prefixWord ++ tailWord_6186486) baseStart_6186486 baseEnd_6186486 := by
    simpa [prefixWord, tailWord_6186486, baseEnd_6186486] using wordTrace_append hprefix tailTrace_6186486
  have hstable : (prefixWord ++ tailWord_6186486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186486).length < 2 ^ (prefixWord ++ tailWord_6186486).sum := by decide
  have hdescent : baseEnd_6186486 < baseStart_6186486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186495 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_6186495 : Nat := 118140960795 + 6186495 * 2 ^ 59
def prefixEnd_6186495 : Nat := 4983230072969 + 3 ^ 40 * 6186495 * 2
def baseEnd_6186495 : Nat := 3176645501636878043561333

theorem tailTrace_6186495 : CollatzResearch.WordTrace tailWord_6186495 prefixEnd_6186495 3176645501636878043561333 := by
  unfold tailWord_6186495
  simp only [CollatzResearch.WordTrace]
  refine ⟨225640009722392659073336939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150426673148261772715557959 225640009722392659073336939)
  ·
    refine ⟨338460014583588988610005409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225640009722392659073336939 338460014583588988610005409)
    ·
      refine ⟨253845010937691741457504057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 338460014583588988610005409 253845010937691741457504057)
      ·
        refine ⟨190383758203268806093128043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253845010937691741457504057 190383758203268806093128043)
        ·
          refine ⟨285575637304903209139692065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190383758203268806093128043 285575637304903209139692065)
          ·
            refine ⟨214181727978677406854769049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285575637304903209139692065 214181727978677406854769049)
            ·
              refine ⟨160636295984008055141076787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214181727978677406854769049 160636295984008055141076787)
              ·
                refine ⟨240954443976012082711615181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160636295984008055141076787 240954443976012082711615181)
                ·
                  refine ⟨90357916491004531016855693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240954443976012082711615181 90357916491004531016855693)
                  ·
                    refine ⟨33884218684126699131320885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 90357916491004531016855693 33884218684126699131320885)
                    ·
                      refine ⟨3176645501636878043561333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33884218684126699131320885 3176645501636878043561333)
                      ·
                        rfl

theorem cell23_6186495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_6186495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186495 prefixEnd_6186495 := by exact prefixLift 6186495
  have htrace : WordTrace (prefixWord ++ tailWord_6186495) baseStart_6186495 baseEnd_6186495 := by
    simpa [prefixWord, tailWord_6186495, baseEnd_6186495] using wordTrace_append hprefix tailTrace_6186495
  have hstable : (prefixWord ++ tailWord_6186495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186495).length < 2 ^ (prefixWord ++ tailWord_6186495).sum := by decide
  have hdescent : baseEnd_6186495 < baseStart_6186495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186503 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_6186503 : Nat := 118140960795 + 6186503 * 2 ^ 59
def prefixEnd_6186503 : Nat := 4983230072969 + 3 ^ 40 * 6186503 * 2
def baseEnd_6186503 : Nat := 3176649609482114012261297

theorem tailTrace_6186503 : CollatzResearch.WordTrace tailWord_6186503 prefixEnd_6186503 3176649609482114012261297 := by
  unfold tailWord_6186503
  simp only [CollatzResearch.WordTrace]
  refine ⟨225640301506363676439628163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150426867670909117626418775 225640301506363676439628163)
  ·
    refine ⟨338460452259545514659442245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225640301506363676439628163 338460452259545514659442245)
    ·
      refine ⟨63461334798664783998645421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 338460452259545514659442245 63461334798664783998645421)
      ·
        refine ⟨23798000549499293999492033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63461334798664783998645421 23798000549499293999492033)
        ·
          refine ⟨17848500412124470499619025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23798000549499293999492033 17848500412124470499619025)
          ·
            refine ⟨13386375309093352874714269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17848500412124470499619025 13386375309093352874714269)
            ·
              refine ⟨5019890740910007328017851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13386375309093352874714269 5019890740910007328017851)
              ·
                refine ⟨7529836111365010992026777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5019890740910007328017851 7529836111365010992026777)
                ·
                  refine ⟨5647377083523758244020083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7529836111365010992026777 5647377083523758244020083)
                  ·
                    refine ⟨8471065625285637366030125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5647377083523758244020083 8471065625285637366030125)
                    ·
                      refine ⟨3176649609482114012261297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8471065625285637366030125 3176649609482114012261297)
                      ·
                        rfl

theorem cell23_6186503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_6186503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186503 prefixEnd_6186503 := by exact prefixLift 6186503
  have htrace : WordTrace (prefixWord ++ tailWord_6186503) baseStart_6186503 baseEnd_6186503 := by
    simpa [prefixWord, tailWord_6186503, baseEnd_6186503] using wordTrace_append hprefix tailTrace_6186503
  have hstable : (prefixWord ++ tailWord_6186503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186503).length < 2 ^ (prefixWord ++ tailWord_6186503).sum := by decide
  have hdescent : baseEnd_6186503 < baseStart_6186503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186549 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 7]
def baseStart_6186549 : Nat := 118140960795 + 6186549 * 2 ^ 59
def prefixEnd_6186549 : Nat := 4983230072969 + 3 ^ 40 * 6186549 * 2
def baseEnd_6186549 : Nat := 352963692176913425809565

theorem tailTrace_6186549 : CollatzResearch.WordTrace tailWord_6186549 prefixEnd_6186549 352963692176913425809565 := by
  unfold tailWord_6186549
  simp only [CollatzResearch.WordTrace]
  refine ⟨225641979264197026295802701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150427986176131350863868467 225641979264197026295802701)
  ·
    refine ⟨84615742224073884860926013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 225641979264197026295802701 84615742224073884860926013)
    ·
      refine ⟨31730903334027706822847255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84615742224073884860926013 31730903334027706822847255)
      ·
        refine ⟨47596355001041560234270883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31730903334027706822847255 47596355001041560234270883)
        ·
          refine ⟨71394532501562340351406325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47596355001041560234270883 71394532501562340351406325)
          ·
            refine ⟨6693237422021469407944343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71394532501562340351406325 6693237422021469407944343)
            ·
              refine ⟨10039856133032204111916515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693237422021469407944343 10039856133032204111916515)
              ·
                refine ⟨15059784199548306167874773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10039856133032204111916515 15059784199548306167874773)
                ·
                  refine ⟨352963692176913425809565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15059784199548306167874773 352963692176913425809565)
                  ·
                    rfl

theorem cell23_6186549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_6186549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186549 prefixEnd_6186549 := by exact prefixLift 6186549
  have htrace : WordTrace (prefixWord ++ tailWord_6186549) baseStart_6186549 baseEnd_6186549 := by
    simpa [prefixWord, tailWord_6186549, baseEnd_6186549] using wordTrace_append hprefix tailTrace_6186549
  have hstable : (prefixWord ++ tailWord_6186549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186549).length < 2 ^ (prefixWord ++ tailWord_6186549).sum := by decide
  have hdescent : baseEnd_6186549 < baseStart_6186549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186599 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_6186599 : Nat := 118140960795 + 6186599 * 2 ^ 59
def prefixEnd_6186599 : Nat := 4983230072969 + 3 ^ 40 * 6186599 * 2
def baseEnd_6186599 : Nat := 3176698903624945636660855

theorem tailTrace_6186599 : CollatzResearch.WordTrace tailWord_6186599 prefixEnd_6186599 3176698903624945636660855 := by
  unfold tailWord_6186599
  simp only [CollatzResearch.WordTrace]
  refine ⟨225643802914015884835122851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150429201942677256556748567 225643802914015884835122851)
  ·
    refine ⟨338465704371023827252684277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 225643802914015884835122851 338465704371023827252684277)
    ·
      refine ⟨31731159784783483804939151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 338465704371023827252684277 31731159784783483804939151)
      ·
        refine ⟨47596739677175225707408727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31731159784783483804939151 47596739677175225707408727)
        ·
          refine ⟨71395109515762838561113091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47596739677175225707408727 71395109515762838561113091)
          ·
            refine ⟨107092664273644257841669637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71395109515762838561113091 107092664273644257841669637)
            ·
              refine ⟨20079874551308298345313057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107092664273644257841669637 20079874551308298345313057)
              ·
                refine ⟨15059905913481223758984793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20079874551308298345313057 15059905913481223758984793)
                ·
                  refine ⟨11294929435110917819238595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15059905913481223758984793 11294929435110917819238595)
                  ·
                    refine ⟨16942394152666376728857893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11294929435110917819238595 16942394152666376728857893)
                    ·
                      refine ⟨3176698903624945636660855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16942394152666376728857893 3176698903624945636660855)
                      ·
                        rfl

theorem cell23_6186599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_6186599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186599 prefixEnd_6186599 := by exact prefixLift 6186599
  have htrace : WordTrace (prefixWord ++ tailWord_6186599) baseStart_6186599 baseEnd_6186599 := by
    simpa [prefixWord, tailWord_6186599, baseEnd_6186599] using wordTrace_append hprefix tailTrace_6186599
  have hstable : (prefixWord ++ tailWord_6186599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186599).length < 2 ^ (prefixWord ++ tailWord_6186599).sum := by decide
  have hdescent : baseEnd_6186599 < baseStart_6186599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186656 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 6]
def baseStart_6186656 : Nat := 118140960795 + 6186656 * 2 ^ 59
def prefixEnd_6186656 : Nat := 4983230072969 + 3 ^ 40 * 6186656 * 2
def baseEnd_6186656 : Nat := 352969796891361323738677

theorem tailTrace_6186656 : CollatzResearch.WordTrace tailWord_6186656 prefixEnd_6186656 352969796891361323738677 := by
  unfold tailWord_6186656
  simp only [CollatzResearch.WordTrace]
  refine ⟨112822940937404691784973911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150430587916539589046631881 112822940937404691784973911)
  ·
    refine ⟨169234411406107037677460867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112822940937404691784973911 169234411406107037677460867)
    ·
      refine ⟨253851617109160556516191301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169234411406107037677460867 253851617109160556516191301)
      ·
        refine ⟨47597178207967604346785869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253851617109160556516191301 47597178207967604346785869)
        ·
          refine ⟨17848941827987851630044701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47597178207967604346785869 17848941827987851630044701)
          ·
            refine ⟨6693353185495444361266763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17848941827987851630044701 6693353185495444361266763)
            ·
              refine ⟨10040029778243166541900145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693353185495444361266763 10040029778243166541900145)
              ·
                refine ⟨7530022333682374906425109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10040029778243166541900145 7530022333682374906425109)
                ·
                  refine ⟨352969796891361323738677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7530022333682374906425109 352969796891361323738677)
                  ·
                    rfl

theorem cell23_6186656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 6].length) (baseStart_6186656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186656 prefixEnd_6186656 := by exact prefixLift 6186656
  have htrace : WordTrace (prefixWord ++ tailWord_6186656) baseStart_6186656 baseEnd_6186656 := by
    simpa [prefixWord, tailWord_6186656, baseEnd_6186656] using wordTrace_append hprefix tailTrace_6186656
  have hstable : (prefixWord ++ tailWord_6186656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186656).length < 2 ^ (prefixWord ++ tailWord_6186656).sum := by decide
  have hdescent : baseEnd_6186656 < baseStart_6186656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6186686 : List Nat := [4, 2, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_6186686 : Nat := 118140960795 + 6186686 * 2 ^ 59
def prefixEnd_6186686 : Nat := 4983230072969 + 3 ^ 40 * 6186686 * 2
def baseEnd_6186686 : Nat := 1058914525480628932090985

theorem tailTrace_6186686 : CollatzResearch.WordTrace tailWord_6186686 prefixEnd_6186686 1058914525480628932090985 := by
  unfold tailWord_6186686
  simp only [CollatzResearch.WordTrace]
  refine ⟨28205872008087587336692489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150431317376467132462359941 28205872008087587336692489)
  ·
    refine ⟨21154404006065690502519367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28205872008087587336692489 21154404006065690502519367)
    ·
      refine ⟨31731606009098535753779051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21154404006065690502519367 31731606009098535753779051)
      ·
        refine ⟨47597409013647803630668577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31731606009098535753779051 47597409013647803630668577)
        ·
          refine ⟨35698056760235852723001433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47597409013647803630668577 35698056760235852723001433)
          ·
            refine ⟨26773542570176889542251075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35698056760235852723001433 26773542570176889542251075)
            ·
              refine ⟨40160313855265334313376613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26773542570176889542251075 40160313855265334313376613)
              ·
                refine ⟨7530058847862250183758115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40160313855265334313376613 7530058847862250183758115)
                ·
                  refine ⟨11295088271793375275637173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7530058847862250183758115 11295088271793375275637173)
                  ·
                    refine ⟨1058914525480628932090985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11295088271793375275637173 1058914525480628932090985)
                    ·
                      rfl

theorem cell23_6186686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_6186686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6186686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6186686 prefixEnd_6186686 := by exact prefixLift 6186686
  have htrace : WordTrace (prefixWord ++ tailWord_6186686) baseStart_6186686 baseEnd_6186686 := by
    simpa [prefixWord, tailWord_6186686, baseEnd_6186686] using wordTrace_append hprefix tailTrace_6186686
  have hstable : (prefixWord ++ tailWord_6186686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6186686).length < 2 ^ (prefixWord ++ tailWord_6186686).sum := by decide
  have hdescent : baseEnd_6186686 < baseStart_6186686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6186686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
