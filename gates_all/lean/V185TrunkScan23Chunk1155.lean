import V185TrunkScan23Chunk1154

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6841573 : List Nat := [1, 3, 1, 4, 3, 1, 2, 3, 1, 1, 3]
def baseStart_6841573 : Nat := 118140960795 + 6841573 * 2 ^ 59
def prefixEnd_6841573 : Nat := 4983230072969 + 3 ^ 40 * 6841573 * 2
def baseEnd_6841573 : Nat := 3513015381822866047873685

theorem tailTrace_6841573 : CollatzResearch.WordTrace tailWord_6841573 prefixEnd_6841573 3513015381822866047873685 := by
  unfold tailWord_6841573
  simp only [CollatzResearch.WordTrace]
  refine ⟨249532667243156943488641373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166355111495437962325760915 249532667243156943488641373)
  ·
    refine ⟨93574750216183853808240515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249532667243156943488641373 93574750216183853808240515)
    ·
      refine ⟨140362125324275780712360773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93574750216183853808240515 140362125324275780712360773)
      ·
        refine ⟨26317898498301708883567645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140362125324275780712360773 26317898498301708883567645)
        ·
          refine ⟨9869211936863140831337867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26317898498301708883567645 9869211936863140831337867)
          ·
            refine ⟨14803817905294711247006801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9869211936863140831337867 14803817905294711247006801)
            ·
              refine ⟨11102863428971033435255101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14803817905294711247006801 11102863428971033435255101)
              ·
                refine ⟨4163573785864137538220663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11102863428971033435255101 4163573785864137538220663)
                ·
                  refine ⟨6245360678796206307330995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163573785864137538220663 6245360678796206307330995)
                  ·
                    refine ⟨9368041018194309460996493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6245360678796206307330995 9368041018194309460996493)
                    ·
                      refine ⟨3513015381822866047873685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368041018194309460996493 3513015381822866047873685)
                      ·
                        rfl

theorem cell23_6841573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_6841573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841573 prefixEnd_6841573 := by exact prefixLift 6841573
  have htrace : WordTrace (prefixWord ++ tailWord_6841573) baseStart_6841573 baseEnd_6841573 := by
    simpa [prefixWord, tailWord_6841573, baseEnd_6841573] using wordTrace_append hprefix tailTrace_6841573
  have hstable : (prefixWord ++ tailWord_6841573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841573).length < 2 ^ (prefixWord ++ tailWord_6841573).sum := by decide
  have hdescent : baseEnd_6841573 < baseStart_6841573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841579 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 1, 1, 4]
def baseStart_6841579 : Nat := 118140960795 + 6841579 * 2 ^ 59
def prefixEnd_6841579 : Nat := 4983230072969 + 3 ^ 40 * 6841579 * 2
def baseEnd_6841579 : Nat := 3513018462706793024398657

theorem tailTrace_6841579 : CollatzResearch.WordTrace tailWord_6841579 prefixEnd_6841579 3513018462706793024398657 := by
  unfold tailWord_6841579
  simp only [CollatzResearch.WordTrace]
  refine ⟨249532886081135206513359791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166355257387423471008906527 249532886081135206513359791)
  ·
    refine ⟨374299329121702809770039687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249532886081135206513359791 374299329121702809770039687)
    ·
      refine ⟨561448993682554214655059531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374299329121702809770039687 561448993682554214655059531)
      ·
        refine ⟨842173490523831321982589297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561448993682554214655059531 842173490523831321982589297)
        ·
          refine ⟨631630117892873491486941973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842173490523831321982589297 631630117892873491486941973)
          ·
            refine ⟨29607661776228444913450405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 631630117892873491486941973 29607661776228444913450405)
            ·
              refine ⟨5551436583042833421271951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29607661776228444913450405 5551436583042833421271951)
              ·
                refine ⟨8327154874564250131907927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551436583042833421271951 8327154874564250131907927)
                ·
                  refine ⟨12490732311846375197861891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327154874564250131907927 12490732311846375197861891)
                  ·
                    refine ⟨18736098467769562796792837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12490732311846375197861891 18736098467769562796792837)
                    ·
                      refine ⟨3513018462706793024398657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18736098467769562796792837 3513018462706793024398657)
                      ·
                        rfl

theorem cell23_6841579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 1, 1, 4].length) (baseStart_6841579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841579 prefixEnd_6841579 := by exact prefixLift 6841579
  have htrace : WordTrace (prefixWord ++ tailWord_6841579) baseStart_6841579 baseEnd_6841579 := by
    simpa [prefixWord, tailWord_6841579, baseEnd_6841579] using wordTrace_append hprefix tailTrace_6841579
  have hstable : (prefixWord ++ tailWord_6841579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841579).length < 2 ^ (prefixWord ++ tailWord_6841579).sum := by decide
  have hdescent : baseEnd_6841579 < baseStart_6841579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841595 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 3]
def baseStart_6841595 : Nat := 118140960795 + 6841595 * 2 ^ 59
def prefixEnd_6841595 : Nat := 4983230072969 + 3 ^ 40 * 6841595 * 2
def baseEnd_6841595 : Nat := 3513026678397264961798583

theorem tailTrace_6841595 : CollatzResearch.WordTrace tailWord_6841595 prefixEnd_6841595 3513026678397264961798583 := by
  unfold tailWord_6841595
  simp only [CollatzResearch.WordTrace]
  refine ⟨249533469649077241245942239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166355646432718160830628159 249533469649077241245942239)
  ·
    refine ⟨374300204473615861868913359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249533469649077241245942239 374300204473615861868913359)
    ·
      refine ⟨561450306710423792803370039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374300204473615861868913359 561450306710423792803370039)
      ·
        refine ⟨842175460065635689205055059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561450306710423792803370039 842175460065635689205055059)
        ·
          refine ⟨1263263190098453533807582589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842175460065635689205055059 1263263190098453533807582589)
          ·
            refine ⟨473723696286920075177843471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263263190098453533807582589 473723696286920075177843471)
            ·
              refine ⟨710585544430380112766765207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473723696286920075177843471 710585544430380112766765207)
              ·
                refine ⟨1065878316645570169150147811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710585544430380112766765207 1065878316645570169150147811)
                ·
                  refine ⟨1598817474968355253725221717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1065878316645570169150147811 1598817474968355253725221717)
                  ·
                    refine ⟨9368071142392706564796221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1598817474968355253725221717 9368071142392706564796221)
                    ·
                      refine ⟨3513026678397264961798583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368071142392706564796221 3513026678397264961798583)
                      ·
                        rfl

theorem cell23_6841595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 3].length) (baseStart_6841595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841595 prefixEnd_6841595 := by exact prefixLift 6841595
  have htrace : WordTrace (prefixWord ++ tailWord_6841595) baseStart_6841595 baseEnd_6841595 := by
    simpa [prefixWord, tailWord_6841595, baseEnd_6841595] using wordTrace_append hprefix tailTrace_6841595
  have hstable : (prefixWord ++ tailWord_6841595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841595).length < 2 ^ (prefixWord ++ tailWord_6841595).sum := by decide
  have hdescent : baseEnd_6841595 < baseStart_6841595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841662 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_6841662 : Nat := 118140960795 + 6841662 * 2 ^ 59
def prefixEnd_6841662 : Nat := 4983230072969 + 3 ^ 40 * 6841662 * 2
def baseEnd_6841662 : Nat := 1171020360533705399886925

theorem tailTrace_6841662 : CollatzResearch.WordTrace tailWord_6841662 prefixEnd_6841662 1171020360533705399886925 := by
  unfold tailWord_6841662
  simp only [CollatzResearch.WordTrace]
  refine ⟨31191989167479313961078905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166357275559889674459087493 31191989167479313961078905)
  ·
    refine ⟨23393991875609485470809179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31191989167479313961078905 23393991875609485470809179)
    ·
      refine ⟨35090987813414228206213769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23393991875609485470809179 35090987813414228206213769)
      ·
        refine ⟨26318240860060671154660327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35090987813414228206213769 26318240860060671154660327)
        ·
          refine ⟨39477361290091006731990491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26318240860060671154660327 39477361290091006731990491)
          ·
            refine ⟨59216041935136510097985737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39477361290091006731990491 59216041935136510097985737)
            ·
              refine ⟨44412031451352382573489303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59216041935136510097985737 44412031451352382573489303)
              ·
                refine ⟨66618047177028573860233955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44412031451352382573489303 66618047177028573860233955)
                ·
                  refine ⟨99927070765542860790350933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66618047177028573860233955 99927070765542860790350933)
                  ·
                    refine ⟨1171020360533705399886925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99927070765542860790350933 1171020360533705399886925)
                    ·
                      rfl

theorem cell23_6841662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_6841662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841662 prefixEnd_6841662 := by exact prefixLift 6841662
  have htrace : WordTrace (prefixWord ++ tailWord_6841662) baseStart_6841662 baseEnd_6841662 := by
    simpa [prefixWord, tailWord_6841662, baseEnd_6841662] using wordTrace_append hprefix tailTrace_6841662
  have hstable : (prefixWord ++ tailWord_6841662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841662).length < 2 ^ (prefixWord ++ tailWord_6841662).sum := by decide
  have hdescent : baseEnd_6841662 < baseStart_6841662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841663 : List Nat := [1, 1, 2, 2, 4, 4, 2, 1, 2, 1, 3]
def baseStart_6841663 : Nat := 118140960795 + 6841663 * 2 ^ 59
def prefixEnd_6841663 : Nat := 4983230072969 + 3 ^ 40 * 6841663 * 2
def baseEnd_6841663 : Nat := 3513061595081770695748271

theorem tailTrace_6841663 : CollatzResearch.WordTrace tailWord_6841663 prefixEnd_6841663 3513061595081770695748271 := by
  unfold tailWord_6841663
  simp only [CollatzResearch.WordTrace]
  refine ⟨249535949812830888859417643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166357299875220592572945095 249535949812830888859417643)
  ·
    refine ⟨374303924719246333289126465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249535949812830888859417643 374303924719246333289126465)
    ·
      refine ⟨280727943539434749966844849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374303924719246333289126465 280727943539434749966844849)
      ·
        refine ⟨210545957654576062475133637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280727943539434749966844849 210545957654576062475133637)
        ·
          refine ⟨39477367060233011714087557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210545957654576062475133637 39477367060233011714087557)
          ·
            refine ⟨7402006323793689696391417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39477367060233011714087557 7402006323793689696391417)
            ·
              refine ⟨5551504742845267272293563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7402006323793689696391417 5551504742845267272293563)
              ·
                refine ⟨8327257114267900908440345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551504742845267272293563 8327257114267900908440345)
                ·
                  refine ⟨6245442835700925681330259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8327257114267900908440345 6245442835700925681330259)
                  ·
                    refine ⟨9368164253551388521995389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6245442835700925681330259 9368164253551388521995389)
                    ·
                      refine ⟨3513061595081770695748271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368164253551388521995389 3513061595081770695748271)
                      ·
                        rfl

theorem cell23_6841663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_6841663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841663 prefixEnd_6841663 := by exact prefixLift 6841663
  have htrace : WordTrace (prefixWord ++ tailWord_6841663) baseStart_6841663 baseEnd_6841663 := by
    simpa [prefixWord, tailWord_6841663, baseEnd_6841663] using wordTrace_append hprefix tailTrace_6841663
  have hstable : (prefixWord ++ tailWord_6841663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841663).length < 2 ^ (prefixWord ++ tailWord_6841663).sum := by decide
  have hdescent : baseEnd_6841663 < baseStart_6841663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841682 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_6841682 : Nat := 118140960795 + 6841682 * 2 ^ 59
def prefixEnd_6841682 : Nat := 4983230072969 + 3 ^ 40 * 6841682 * 2
def baseEnd_6841682 : Nat := 3513071351214206121410683

theorem tailTrace_6841682 : CollatzResearch.WordTrace tailWord_6841682 prefixEnd_6841682 3513071351214206121410683 := by
  unfold tailWord_6841682
  simp only [CollatzResearch.WordTrace]
  refine ⟨62384160699940513776089825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166357761866508036736239533 62384160699940513776089825)
  ·
    refine ⟨46788120524955385332067369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62384160699940513776089825 46788120524955385332067369)
    ·
      refine ⟨35091090393716538999050527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46788120524955385332067369 35091090393716538999050527)
      ·
        refine ⟨52636635590574808498575791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35091090393716538999050527 52636635590574808498575791)
        ·
          refine ⟨78954953385862212747863687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52636635590574808498575791 78954953385862212747863687)
          ·
            refine ⟨118432430078793319121795531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78954953385862212747863687 118432430078793319121795531)
            ·
              refine ⟨177648645118189978682693297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118432430078793319121795531 177648645118189978682693297)
              ·
                refine ⟨133236483838642484012019973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177648645118189978682693297 133236483838642484012019973)
                ·
                  refine ⟨24981840719745465752253745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133236483838642484012019973 24981840719745465752253745)
                  ·
                    refine ⟨18736380539809099314190309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24981840719745465752253745 18736380539809099314190309)
                    ·
                      refine ⟨3513071351214206121410683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18736380539809099314190309 3513071351214206121410683)
                      ·
                        rfl

theorem cell23_6841682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_6841682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841682 prefixEnd_6841682 := by exact prefixLift 6841682
  have htrace : WordTrace (prefixWord ++ tailWord_6841682) baseStart_6841682 baseEnd_6841682 := by
    simpa [prefixWord, tailWord_6841682, baseEnd_6841682] using wordTrace_append hprefix tailTrace_6841682
  have hstable : (prefixWord ++ tailWord_6841682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841682).length < 2 ^ (prefixWord ++ tailWord_6841682).sum := by decide
  have hdescent : baseEnd_6841682 < baseStart_6841682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841794 : List Nat := [3, 5, 2, 1, 1, 2, 1, 3, 5]
def baseStart_6841794 : Nat := 118140960795 + 6841794 * 2 ^ 59
def prefixEnd_6841794 : Nat := 4983230072969 + 3 ^ 40 * 6841794 * 2
def baseEnd_6841794 : Nat := 390347651227501075912241

theorem tailTrace_6841794 : CollatzResearch.WordTrace tailWord_6841794 prefixEnd_6841794 390347651227501075912241 := by
  unfold tailWord_6841794
  simp only [CollatzResearch.WordTrace]
  refine ⟨62385181943839074558109109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166360485183570865488290957 62385181943839074558109109)
  ·
    refine ⟨5848610807234913239822729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62385181943839074558109109 5848610807234913239822729)
    ·
      refine ⟨4386458105426184929867047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5848610807234913239822729 4386458105426184929867047)
      ·
        refine ⟨6579687158139277394800571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386458105426184929867047 6579687158139277394800571)
        ·
          refine ⟨9869530737208916092200857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6579687158139277394800571 9869530737208916092200857)
          ·
            refine ⟨7402148052906687069150643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9869530737208916092200857 7402148052906687069150643)
            ·
              refine ⟨11103222079360030603725965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402148052906687069150643 11103222079360030603725965)
              ·
                refine ⟨4163708279760011476397237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11103222079360030603725965 4163708279760011476397237)
                ·
                  refine ⟨390347651227501075912241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4163708279760011476397237 390347651227501075912241)
                  ·
                    rfl

theorem cell23_6841794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_6841794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841794 prefixEnd_6841794 := by exact prefixLift 6841794
  have htrace : WordTrace (prefixWord ++ tailWord_6841794) baseStart_6841794 baseEnd_6841794 := by
    simpa [prefixWord, tailWord_6841794, baseEnd_6841794] using wordTrace_append hprefix tailTrace_6841794
  have hstable : (prefixWord ++ tailWord_6841794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841794).length < 2 ^ (prefixWord ++ tailWord_6841794).sum := by decide
  have hdescent : baseEnd_6841794 < baseStart_6841794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841796 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_6841796 : Nat := 118140960795 + 6841796 * 2 ^ 59
def prefixEnd_6841796 : Nat := 4983230072969 + 3 ^ 40 * 6841796 * 2
def baseEnd_6841796 : Nat := 3513129888008818675385159

theorem tailTrace_6841796 : CollatzResearch.WordTrace tailWord_6841796 prefixEnd_6841796 3513129888008818675385159 := by
  unfold tailWord_6841796
  simp only [CollatzResearch.WordTrace]
  refine ⟨124770400360674526287004621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166360533814232701716006161 124770400360674526287004621)
  ·
    refine ⟨46788900135252947357626733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124770400360674526287004621 46788900135252947357626733)
    ·
      refine ⟨17545837550719855259110025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46788900135252947357626733 17545837550719855259110025)
      ·
        refine ⟨13159378163039891444332519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17545837550719855259110025 13159378163039891444332519)
        ·
          refine ⟨19739067244559837166498779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159378163039891444332519 19739067244559837166498779)
          ·
            refine ⟨29608600866839755749748169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19739067244559837166498779 29608600866839755749748169)
            ·
              refine ⟨22206450650129816812311127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29608600866839755749748169 22206450650129816812311127)
              ·
                refine ⟨33309675975194725218466691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22206450650129816812311127 33309675975194725218466691)
                ·
                  refine ⟨49964513962792087827700037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33309675975194725218466691 49964513962792087827700037)
                  ·
                    refine ⟨9368346368023516467693757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49964513962792087827700037 9368346368023516467693757)
                    ·
                      refine ⟨3513129888008818675385159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368346368023516467693757 3513129888008818675385159)
                      ·
                        rfl

theorem cell23_6841796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_6841796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841796 prefixEnd_6841796 := by exact prefixLift 6841796
  have htrace : WordTrace (prefixWord ++ tailWord_6841796) baseStart_6841796 baseEnd_6841796 := by
    simpa [prefixWord, tailWord_6841796, baseEnd_6841796] using wordTrace_append hprefix tailTrace_6841796
  have hstable : (prefixWord ++ tailWord_6841796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841796).length < 2 ^ (prefixWord ++ tailWord_6841796).sum := by decide
  have hdescent : baseEnd_6841796 < baseStart_6841796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841846 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_6841846 : Nat := 118140960795 + 6841846 * 2 ^ 59
def prefixEnd_6841846 : Nat := 4983230072969 + 3 ^ 40 * 6841846 * 2
def baseEnd_6841846 : Nat := 1171051854013847826586643

theorem tailTrace_6841846 : CollatzResearch.WordTrace tailWord_6841846 prefixEnd_6841846 1171051854013847826586643 := by
  unfold tailWord_6841846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596414023197994444583087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166361749580778607408886261 15596414023197994444583087)
  ·
    refine ⟨23394621034796991666874631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15596414023197994444583087 23394621034796991666874631)
    ·
      refine ⟨35091931552195487500311947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23394621034796991666874631 35091931552195487500311947)
      ·
        refine ⟨52637897328293231250467921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35091931552195487500311947 52637897328293231250467921)
        ·
          refine ⟨39478422996219923437850941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52637897328293231250467921 39478422996219923437850941)
          ·
            refine ⟨14804408623582471289194103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39478422996219923437850941 14804408623582471289194103)
            ·
              refine ⟨22206612935373706933791155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14804408623582471289194103 22206612935373706933791155)
              ·
                refine ⟨33309919403060560400686733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22206612935373706933791155 33309919403060560400686733)
                ·
                  refine ⟨12491219776147710150257525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33309919403060560400686733 12491219776147710150257525)
                  ·
                    refine ⟨1171051854013847826586643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12491219776147710150257525 1171051854013847826586643)
                    ·
                      rfl

theorem cell23_6841846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_6841846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841846 prefixEnd_6841846 := by exact prefixLift 6841846
  have htrace : WordTrace (prefixWord ++ tailWord_6841846) baseStart_6841846 baseEnd_6841846 := by
    simpa [prefixWord, tailWord_6841846, baseEnd_6841846] using wordTrace_append hprefix tailTrace_6841846
  have hstable : (prefixWord ++ tailWord_6841846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841846).length < 2 ^ (prefixWord ++ tailWord_6841846).sum := by decide
  have hdescent : baseEnd_6841846 < baseStart_6841846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841853 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 2, 3, 2]
def baseStart_6841853 : Nat := 118140960795 + 6841853 * 2 ^ 59
def prefixEnd_6841853 : Nat := 4983230072969 + 3 ^ 40 * 6841853 * 2
def baseEnd_6841853 : Nat := 3513159156406124952372397

theorem tailTrace_6841853 : CollatzResearch.WordTrace tailWord_6841853 prefixEnd_6841853 3513159156406124952372397 := by
  unfold tailWord_6841853
  simp only [CollatzResearch.WordTrace]
  refine ⟨249542879682142551308834213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166361919788095034205889475 249542879682142551308834213)
  ·
    refine ⟨46789289940401728370406415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249542879682142551308834213 46789289940401728370406415)
    ·
      refine ⟨70183934910602592555609623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46789289940401728370406415 70183934910602592555609623)
      ·
        refine ⟨105275902365903888833414435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70183934910602592555609623 105275902365903888833414435)
        ·
          refine ⟨157913853548855833250121653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105275902365903888833414435 157913853548855833250121653)
          ·
            refine ⟨14804423770205234367198905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157913853548855833250121653 14804423770205234367198905)
            ·
              refine ⟨11103317827653925775399179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14804423770205234367198905 11103317827653925775399179)
              ·
                refine ⟨16654976741480888663098769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11103317827653925775399179 16654976741480888663098769)
                ·
                  refine ⟨12491232556110666497324077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16654976741480888663098769 12491232556110666497324077)
                  ·
                    refine ⟨4684212208541499936496529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12491232556110666497324077 4684212208541499936496529)
                    ·
                      refine ⟨3513159156406124952372397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4684212208541499936496529 3513159156406124952372397)
                      ·
                        rfl

theorem cell23_6841853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_6841853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841853 prefixEnd_6841853 := by exact prefixLift 6841853
  have htrace : WordTrace (prefixWord ++ tailWord_6841853) baseStart_6841853 baseEnd_6841853 := by
    simpa [prefixWord, tailWord_6841853, baseEnd_6841853] using wordTrace_append hprefix tailTrace_6841853
  have hstable : (prefixWord ++ tailWord_6841853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841853).length < 2 ^ (prefixWord ++ tailWord_6841853).sum := by decide
  have hdescent : baseEnd_6841853 < baseStart_6841853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841859 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 4, 4]
def baseStart_6841859 : Nat := 118140960795 + 6841859 * 2 ^ 59
def prefixEnd_6841859 : Nat := 4983230072969 + 3 ^ 40 * 6841859 * 2
def baseEnd_6841859 : Nat := 1171054079096683976299123

theorem tailTrace_6841859 : CollatzResearch.WordTrace tailWord_6841859 prefixEnd_6841859 1171054079096683976299123 := by
  unfold tailWord_6841859
  simp only [CollatzResearch.WordTrace]
  refine ⟨249543098520120814333552631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166362065680080542889035087 249543098520120814333552631)
  ·
    refine ⟨374314647780181221500328947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249543098520120814333552631 374314647780181221500328947)
    ·
      refine ⟨561471971670271832250493421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374314647780181221500328947 561471971670271832250493421)
      ·
        refine ⟨210551989376351937093935033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561471971670271832250493421 210551989376351937093935033)
        ·
          refine ⟨157913992032263952820451275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210551989376351937093935033 157913992032263952820451275)
          ·
            refine ⟨236870988048395929230676913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157913992032263952820451275 236870988048395929230676913)
            ·
              refine ⟨177653241036296946923007685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236870988048395929230676913 177653241036296946923007685)
              ·
                refine ⟨33309982694305677548063941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177653241036296946923007685 33309982694305677548063941)
                ·
                  refine ⟨6245621755182314540261989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33309982694305677548063941 6245621755182314540261989)
                  ·
                    refine ⟨1171054079096683976299123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6245621755182314540261989 1171054079096683976299123)
                    ·
                      rfl

theorem cell23_6841859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4, 4].length) (baseStart_6841859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841859 prefixEnd_6841859 := by exact prefixLift 6841859
  have htrace : WordTrace (prefixWord ++ tailWord_6841859) baseStart_6841859 baseEnd_6841859 := by
    simpa [prefixWord, tailWord_6841859, baseEnd_6841859] using wordTrace_append hprefix tailTrace_6841859
  have hstable : (prefixWord ++ tailWord_6841859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841859).length < 2 ^ (prefixWord ++ tailWord_6841859).sum := by decide
  have hdescent : baseEnd_6841859 < baseStart_6841859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841863 : List Nat := [1, 1, 4, 3, 2, 2, 3, 1, 1, 5]
def baseStart_6841863 : Nat := 118140960795 + 6841863 * 2 ^ 59
def prefixEnd_6841863 : Nat := 4983230072969 + 3 ^ 40 * 6841863 * 2
def baseEnd_6841863 : Nat := 1171054763737556637749117

theorem tailTrace_6841863 : CollatzResearch.WordTrace tailWord_6841863 prefixEnd_6841863 1171054763737556637749117 := by
  unfold tailWord_6841863
  simp only [CollatzResearch.WordTrace]
  refine ⟨249543244412106323016698243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166362162941404215344465495 249543244412106323016698243)
  ·
    refine ⟨374314866618159484525047365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249543244412106323016698243 374314866618159484525047365)
    ·
      refine ⟨70184037490904903348446381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374314866618159484525047365 70184037490904903348446381)
      ·
        refine ⟨26319014059089338755667393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70184037490904903348446381 26319014059089338755667393)
        ·
          refine ⟨19739260544317004066750545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26319014059089338755667393 19739260544317004066750545)
          ·
            refine ⟨14804445408237753050062909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19739260544317004066750545 14804445408237753050062909)
            ·
              refine ⟨5551667028089157393773591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14804445408237753050062909 5551667028089157393773591)
              ·
                refine ⟨8327500542133736090660387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551667028089157393773591 8327500542133736090660387)
                ·
                  refine ⟨12491250813200604135990581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327500542133736090660387 12491250813200604135990581)
                  ·
                    refine ⟨1171054763737556637749117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12491250813200604135990581 1171054763737556637749117)
                    ·
                      rfl

theorem cell23_6841863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_6841863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841863 prefixEnd_6841863 := by exact prefixLift 6841863
  have htrace : WordTrace (prefixWord ++ tailWord_6841863) baseStart_6841863 baseEnd_6841863 := by
    simpa [prefixWord, tailWord_6841863, baseEnd_6841863] using wordTrace_append hprefix tailTrace_6841863
  have hstable : (prefixWord ++ tailWord_6841863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841863).length < 2 ^ (prefixWord ++ tailWord_6841863).sum := by decide
  have hdescent : baseEnd_6841863 < baseStart_6841863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841877 : List Nat := [1, 3, 2, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_6841877 : Nat := 118140960795 + 6841877 * 2 ^ 59
def prefixEnd_6841877 : Nat := 4983230072969 + 3 ^ 40 * 6841877 * 2
def baseEnd_6841877 : Nat := 3513171479941832858472287

theorem tailTrace_6841877 : CollatzResearch.WordTrace tailWord_6841877 prefixEnd_6841877 3513171479941832858472287 := by
  unfold tailWord_6841877
  simp only [CollatzResearch.WordTrace]
  refine ⟨249543755034055603407707885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166362503356037068938471923 249543755034055603407707885)
  ·
    refine ⟨93578908137770851277890457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249543755034055603407707885 93578908137770851277890457)
    ·
      refine ⟨70184181103328138458417843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93578908137770851277890457 70184181103328138458417843)
      ·
        refine ⟨105276271654992207687626765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70184181103328138458417843 105276271654992207687626765)
        ·
          refine ⟨39478601870622077882860037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105276271654992207687626765 39478601870622077882860037)
          ·
            refine ⟨7402237850741639603036257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39478601870622077882860037 7402237850741639603036257)
            ·
              refine ⟨5551678388056229702277193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7402237850741639603036257 5551678388056229702277193)
              ·
                refine ⟨4163758791042172276707895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5551678388056229702277193 4163758791042172276707895)
                ·
                  refine ⟨6245638186563258415061843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163758791042172276707895 6245638186563258415061843)
                  ·
                    refine ⟨9368457279844887622592765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6245638186563258415061843 9368457279844887622592765)
                    ·
                      refine ⟨3513171479941832858472287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368457279844887622592765 3513171479941832858472287)
                      ·
                        rfl

theorem cell23_6841877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_6841877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841877 prefixEnd_6841877 := by exact prefixLift 6841877
  have htrace : WordTrace (prefixWord ++ tailWord_6841877) baseStart_6841877 baseEnd_6841877 := by
    simpa [prefixWord, tailWord_6841877, baseEnd_6841877] using wordTrace_append hprefix tailTrace_6841877
  have hstable : (prefixWord ++ tailWord_6841877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841877).length < 2 ^ (prefixWord ++ tailWord_6841877).sum := by decide
  have hdescent : baseEnd_6841877 < baseStart_6841877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841889 : List Nat := [1, 2, 3, 2, 2, 2, 3, 8]
def baseStart_6841889 : Nat := 118140960795 + 6841889 * 2 ^ 59
def prefixEnd_6841889 : Nat := 4983230072969 + 3 ^ 40 * 6841889 * 2
def baseEnd_6841889 : Nat := 130117690433692104130453

theorem tailTrace_6841889 : CollatzResearch.WordTrace tailWord_6841889 prefixEnd_6841889 130117690433692104130453 := by
  unfold tailWord_6841889
  simp only [CollatzResearch.WordTrace]
  refine ⟨249544192710012129457144721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166362795140008086304763147 249544192710012129457144721)
  ·
    refine ⟨187158144532509097092858541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249544192710012129457144721 187158144532509097092858541)
    ·
      refine ⟨70184304199690911409821953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187158144532509097092858541 70184304199690911409821953)
      ·
        refine ⟨52638228149768183557366465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70184304199690911409821953 52638228149768183557366465)
        ·
          refine ⟨39478671112326137668024849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52638228149768183557366465 39478671112326137668024849)
          ·
            refine ⟨29609003334244603251018637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39478671112326137668024849 29609003334244603251018637)
            ·
              refine ⟨11103376250341726219131989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29609003334244603251018637 11103376250341726219131989)
              ·
                refine ⟨130117690433692104130453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11103376250341726219131989 130117690433692104130453)
                ·
                  rfl

theorem cell23_6841889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 8].length) (baseStart_6841889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841889 prefixEnd_6841889 := by exact prefixLift 6841889
  have htrace : WordTrace (prefixWord ++ tailWord_6841889) baseStart_6841889 baseEnd_6841889 := by
    simpa [prefixWord, tailWord_6841889, baseEnd_6841889] using wordTrace_append hprefix tailTrace_6841889
  have hstable : (prefixWord ++ tailWord_6841889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841889).length < 2 ^ (prefixWord ++ tailWord_6841889).sum := by decide
  have hdescent : baseEnd_6841889 < baseStart_6841889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841917 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 1, 1, 4]
def baseStart_6841917 : Nat := 118140960795 + 6841917 * 2 ^ 59
def prefixEnd_6841917 : Nat := 4983230072969 + 3 ^ 40 * 6841917 * 2
def baseEnd_6841917 : Nat := 3513192019168012701972103

theorem tailTrace_6841917 : CollatzResearch.WordTrace tailWord_6841917 prefixEnd_6841917 3513192019168012701972103 := by
  unfold tailWord_6841917
  simp only [CollatzResearch.WordTrace]
  refine ⟨249545213953910690239164005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166363475969273793492776003 249545213953910690239164005)
  ·
    refine ⟨46789727616358254419843251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249545213953910690239164005 46789727616358254419843251)
    ·
      refine ⟨70184591424537381629764877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46789727616358254419843251 70184591424537381629764877)
      ·
        refine ⟨26319221784201518111161829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70184591424537381629764877 26319221784201518111161829)
        ·
          refine ⟨4934854084537784645842843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26319221784201518111161829 4934854084537784645842843)
          ·
            refine ⟨7402281126806676968764265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934854084537784645842843 7402281126806676968764265)
            ·
              refine ⟨5551710845105007726573199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7402281126806676968764265 5551710845105007726573199)
              ·
                refine ⟨8327566267657511589859799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551710845105007726573199 8327566267657511589859799)
                ·
                  refine ⟨12491349401486267384789699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327566267657511589859799 12491349401486267384789699)
                  ·
                    refine ⟨18737024102229401077184549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12491349401486267384789699 18737024102229401077184549)
                    ·
                      refine ⟨3513192019168012701972103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18737024102229401077184549 3513192019168012701972103)
                      ·
                        rfl

theorem cell23_6841917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_6841917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841917 prefixEnd_6841917 := by exact prefixLift 6841917
  have htrace : WordTrace (prefixWord ++ tailWord_6841917) baseStart_6841917 baseEnd_6841917 := by
    simpa [prefixWord, tailWord_6841917, baseEnd_6841917] using wordTrace_append hprefix tailTrace_6841917
  have hstable : (prefixWord ++ tailWord_6841917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841917).length < 2 ^ (prefixWord ++ tailWord_6841917).sum := by decide
  have hdescent : baseEnd_6841917 < baseStart_6841917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841960 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6841960 : Nat := 118140960795 + 6841960 * 2 ^ 59
def prefixEnd_6841960 : Nat := 4983230072969 + 3 ^ 40 * 6841960 * 2
def baseEnd_6841960 : Nat := 3513214098836156033734405

theorem tailTrace_6841960 : CollatzResearch.WordTrace tailWord_6841960 prefixEnd_6841960 3513214098836156033734405 := by
  unfold tailWord_6841960
  simp only [CollatzResearch.WordTrace]
  refine ⟨124773391146377454291489667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166364521528503272388652889 124773391146377454291489667)
  ·
    refine ⟨187160086719566181437234501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124773391146377454291489667 187160086719566181437234501)
    ·
      refine ⟨35092516259918659019481469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187160086719566181437234501 35092516259918659019481469)
      ·
        refine ⟨13159693597469497132305551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35092516259918659019481469 13159693597469497132305551)
        ·
          refine ⟨19739540396204245698458327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159693597469497132305551 19739540396204245698458327)
          ·
            refine ⟨29609310594306368547687491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19739540396204245698458327 29609310594306368547687491)
            ·
              refine ⟨44413965891459552821531237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29609310594306368547687491 44413965891459552821531237)
              ·
                refine ⟨8327618604648666154037107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44413965891459552821531237 8327618604648666154037107)
                ·
                  refine ⟨12491427906972999231055661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327618604648666154037107 12491427906972999231055661)
                  ·
                    refine ⟨4684285465114874711645873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12491427906972999231055661 4684285465114874711645873)
                    ·
                      refine ⟨3513214098836156033734405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4684285465114874711645873 3513214098836156033734405)
                      ·
                        rfl

theorem cell23_6841960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6841960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841960 prefixEnd_6841960 := by exact prefixLift 6841960
  have htrace : WordTrace (prefixWord ++ tailWord_6841960) baseStart_6841960 baseEnd_6841960 := by
    simpa [prefixWord, tailWord_6841960, baseEnd_6841960] using wordTrace_append hprefix tailTrace_6841960
  have hstable : (prefixWord ++ tailWord_6841960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841960).length < 2 ^ (prefixWord ++ tailWord_6841960).sum := by decide
  have hdescent : baseEnd_6841960 < baseStart_6841960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841969 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_6841969 : Nat := 118140960795 + 6841969 * 2 ^ 59
def prefixEnd_6841969 : Nat := 4983230072969 + 3 ^ 40 * 6841969 * 2
def baseEnd_6841969 : Nat := 3513218720162046498521863

theorem tailTrace_6841969 : CollatzResearch.WordTrace tailWord_6841969 prefixEnd_6841969 3513218720162046498521863 := by
  unfold tailWord_6841969
  simp only [CollatzResearch.WordTrace]
  refine ⟨249547110549722303120056961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166364740366481535413371307 249547110549722303120056961)
  ·
    refine ⟨187160332912291727340042721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249547110549722303120056961 187160332912291727340042721)
    ·
      refine ⟨140370249684218795505032041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187160332912291727340042721 140370249684218795505032041)
      ·
        refine ⟨105277687263164096628774031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140370249684218795505032041 105277687263164096628774031)
        ·
          refine ⟨157916530894746144943161047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105277687263164096628774031 157916530894746144943161047)
          ·
            refine ⟨236874796342119217414741571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157916530894746144943161047 236874796342119217414741571)
            ·
              refine ⟨355312194513178826122112357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236874796342119217414741571 355312194513178826122112357)
              ·
                refine ⟨66621036471221029897896067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355312194513178826122112357 66621036471221029897896067)
                ·
                  refine ⟨99931554706831544846844101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66621036471221029897896067 99931554706831544846844101)
                  ·
                    refine ⟨18737166507530914658783269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99931554706831544846844101 18737166507530914658783269)
                    ·
                      refine ⟨3513218720162046498521863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18737166507530914658783269 3513218720162046498521863)
                      ·
                        rfl

theorem cell23_6841969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_6841969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841969 prefixEnd_6841969 := by exact prefixLift 6841969
  have htrace : WordTrace (prefixWord ++ tailWord_6841969) baseStart_6841969 baseEnd_6841969 := by
    simpa [prefixWord, tailWord_6841969, baseEnd_6841969] using wordTrace_append hprefix tailTrace_6841969
  have hstable : (prefixWord ++ tailWord_6841969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841969).length < 2 ^ (prefixWord ++ tailWord_6841969).sum := by decide
  have hdescent : baseEnd_6841969 < baseStart_6841969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6841989 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_6841989 : Nat := 118140960795 + 6841989 * 2 ^ 59
def prefixEnd_6841989 : Nat := 4983230072969 + 3 ^ 40 * 6841989 * 2
def baseEnd_6841989 : Nat := 3513228989775136420271771

theorem tailTrace_6841989 : CollatzResearch.WordTrace tailWord_6841989 prefixEnd_6841989 3513228989775136420271771 := by
  unfold tailWord_6841989
  simp only [CollatzResearch.WordTrace]
  refine ⟨249547840009649846535785021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166365226673099897690523347 249547840009649846535785021)
  ·
    refine ⟨93580440003618692450919383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249547840009649846535785021 93580440003618692450919383)
    ·
      refine ⟨140370660005428038676379075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93580440003618692450919383 140370660005428038676379075)
      ·
        refine ⟨210555990008142058014568613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140370660005428038676379075 210555990008142058014568613)
        ·
          refine ⟨39479248126526635877731615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210555990008142058014568613 39479248126526635877731615)
          ·
            refine ⟨59218872189789953816597423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39479248126526635877731615 59218872189789953816597423)
            ·
              refine ⟨88828308284684930724896135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59218872189789953816597423 88828308284684930724896135)
              ·
                refine ⟨133242462427027396087344203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88828308284684930724896135 133242462427027396087344203)
                ·
                  refine ⟨199863693640541094131016305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133242462427027396087344203 199863693640541094131016305)
                  ·
                    refine ⟨149897770230405820598262229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199863693640541094131016305 149897770230405820598262229)
                    ·
                      refine ⟨3513228989775136420271771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149897770230405820598262229 3513228989775136420271771)
                      ·
                        rfl

theorem cell23_6841989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_6841989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6841989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6841989 prefixEnd_6841989 := by exact prefixLift 6841989
  have htrace : WordTrace (prefixWord ++ tailWord_6841989) baseStart_6841989 baseEnd_6841989 := by
    simpa [prefixWord, tailWord_6841989, baseEnd_6841989] using wordTrace_append hprefix tailTrace_6841989
  have hstable : (prefixWord ++ tailWord_6841989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6841989).length < 2 ^ (prefixWord ++ tailWord_6841989).sum := by decide
  have hdescent : baseEnd_6841989 < baseStart_6841989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6841989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842007 : List Nat := [1, 1, 3, 3, 2, 2, 4, 1, 2, 2, 2]
def baseStart_6842007 : Nat := 118140960795 + 6842007 * 2 ^ 59
def prefixEnd_6842007 : Nat := 4983230072969 + 3 ^ 40 * 6842007 * 2
def baseEnd_6842007 : Nat := 3513238232426917349846689

theorem tailTrace_6842007 : CollatzResearch.WordTrace tailWord_6842007 prefixEnd_6842007 3513238232426917349846689 := by
  unfold tailWord_6842007
  simp only [CollatzResearch.WordTrace]
  refine ⟨249548496523584635609940275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166365664349056423739960183 249548496523584635609940275)
  ·
    refine ⟨374322744785376953414910413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249548496523584635609940275 374322744785376953414910413)
    ·
      refine ⟨140371029294516357530591405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374322744785376953414910413 140371029294516357530591405)
      ·
        refine ⟨52639135985443634073971777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140371029294516357530591405 52639135985443634073971777)
        ·
          refine ⟨39479351989082725555478833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52639135985443634073971777 39479351989082725555478833)
          ·
            refine ⟨29609513991812044166609125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39479351989082725555478833 29609513991812044166609125)
            ·
              refine ⟨5551783873464758281239211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29609513991812044166609125 5551783873464758281239211)
              ·
                refine ⟨8327675810197137421858817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551783873464758281239211 8327675810197137421858817)
                ·
                  refine ⟨6245756857647853066394113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8327675810197137421858817 6245756857647853066394113)
                  ·
                    refine ⟨4684317643235889799795585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6245756857647853066394113 4684317643235889799795585)
                    ·
                      refine ⟨3513238232426917349846689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4684317643235889799795585 3513238232426917349846689)
                      ·
                        rfl

theorem cell23_6842007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_6842007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842007 prefixEnd_6842007 := by exact prefixLift 6842007
  have htrace : WordTrace (prefixWord ++ tailWord_6842007) baseStart_6842007 baseEnd_6842007 := by
    simpa [prefixWord, tailWord_6842007, baseEnd_6842007] using wordTrace_append hprefix tailTrace_6842007
  have hstable : (prefixWord ++ tailWord_6842007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842007).length < 2 ^ (prefixWord ++ tailWord_6842007).sum := by decide
  have hdescent : baseEnd_6842007 < baseStart_6842007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842009 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 1, 7]
def baseStart_6842009 : Nat := 118140960795 + 6842009 * 2 ^ 59
def prefixEnd_6842009 : Nat := 4983230072969 + 3 ^ 40 * 6842009 * 2
def baseEnd_6842009 : Nat := 1171079753129408780673893

theorem tailTrace_6842009 : CollatzResearch.WordTrace tailWord_6842009 prefixEnd_6842009 1171079753129408780673893 := by
  unfold tailWord_6842009
  simp only [CollatzResearch.WordTrace]
  refine ⟨249548569469577389951513081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166365712979718259967675387 249548569469577389951513081)
  ·
    refine ⟨187161427102183042463634811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249548569469577389951513081 187161427102183042463634811)
    ·
      refine ⟨280742140653274563695452217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187161427102183042463634811 280742140653274563695452217)
      ·
        refine ⟨210556605489955922771589163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280742140653274563695452217 210556605489955922771589163)
        ·
          refine ⟨315834908234933884157383745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210556605489955922771589163 315834908234933884157383745)
          ·
            refine ⟨236876181176200413118037809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315834908234933884157383745 236876181176200413118037809)
            ·
              refine ⟨177657135882150309838528357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236876181176200413118037809 177657135882150309838528357)
              ·
                refine ⟨33310712977903183094724067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177657135882150309838528357 33310712977903183094724067)
                ·
                  refine ⟨49966069466854774642086101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33310712977903183094724067 49966069466854774642086101)
                  ·
                    refine ⟨1171079753129408780673893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49966069466854774642086101 1171079753129408780673893)
                    ·
                      rfl

theorem cell23_6842009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_6842009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842009 prefixEnd_6842009 := by exact prefixLift 6842009
  have htrace : WordTrace (prefixWord ++ tailWord_6842009) baseStart_6842009 baseEnd_6842009 := by
    simpa [prefixWord, tailWord_6842009, baseEnd_6842009] using wordTrace_append hprefix tailTrace_6842009
  have hstable : (prefixWord ++ tailWord_6842009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842009).length < 2 ^ (prefixWord ++ tailWord_6842009).sum := by decide
  have hdescent : baseEnd_6842009 < baseStart_6842009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842019 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7]
def baseStart_6842019 : Nat := 118140960795 + 6842019 * 2 ^ 59
def prefixEnd_6842019 : Nat := 4983230072969 + 3 ^ 40 * 6842019 * 2
def baseEnd_6842019 : Nat := 3513244394194771302896633

theorem tailTrace_6842019 : CollatzResearch.WordTrace tailWord_6842019 prefixEnd_6842019 3513244394194771302896633 := by
  unfold tailWord_6842019
  simp only [CollatzResearch.WordTrace]
  refine ⟨249548934199541161659377111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166365956133027441106251407 249548934199541161659377111)
  ·
    refine ⟨374323401299311742489065667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249548934199541161659377111 374323401299311742489065667)
    ·
      refine ⟨561485101948967613733598501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374323401299311742489065667 561485101948967613733598501)
      ·
        refine ⟨105278456615431427575049719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 561485101948967613733598501 105278456615431427575049719)
        ·
          refine ⟨157917684923147141362574579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105278456615431427575049719 157917684923147141362574579)
          ·
            refine ⟨236876527384720712043861869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157917684923147141362574579 236876527384720712043861869)
            ·
              refine ⟨88828697769270267016448201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236876527384720712043861869 88828697769270267016448201)
              ·
                refine ⟨66621523326952700262336151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88828697769270267016448201 66621523326952700262336151)
                ·
                  refine ⟨99932284990429050393504227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66621523326952700262336151 99932284990429050393504227)
                  ·
                    refine ⟨149898427485643575590256341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99932284990429050393504227 149898427485643575590256341)
                    ·
                      refine ⟨3513244394194771302896633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149898427485643575590256341 3513244394194771302896633)
                      ·
                        rfl

theorem cell23_6842019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_6842019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842019 prefixEnd_6842019 := by exact prefixLift 6842019
  have htrace : WordTrace (prefixWord ++ tailWord_6842019) baseStart_6842019 baseEnd_6842019 := by
    simpa [prefixWord, tailWord_6842019, baseEnd_6842019] using wordTrace_append hprefix tailTrace_6842019
  have hstable : (prefixWord ++ tailWord_6842019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842019).length < 2 ^ (prefixWord ++ tailWord_6842019).sum := by decide
  have hdescent : baseEnd_6842019 < baseStart_6842019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842024 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6842024 : Nat := 118140960795 + 6842024 * 2 ^ 59
def prefixEnd_6842024 : Nat := 4983230072969 + 3 ^ 40 * 6842024 * 2
def baseEnd_6842024 : Nat := 3513246961598043783334111

theorem tailTrace_6842024 : CollatzResearch.WordTrace tailWord_6842024 prefixEnd_6842024 3513246961598043783334111 := by
  unfold tailWord_6842024
  simp only [CollatzResearch.WordTrace]
  refine ⟨124774558282261523756654563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166366077709682031675539417 124774558282261523756654563)
  ·
    refine ⟨187161837423392285634981845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124774558282261523756654563 187161837423392285634981845)
    ·
      refine ⟨4386605564610756694569887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 187161837423392285634981845 4386605564610756694569887)
      ·
        refine ⟨6579908346916135041854831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386605564610756694569887 6579908346916135041854831)
        ·
          refine ⟨9869862520374202562782247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6579908346916135041854831 9869862520374202562782247)
          ·
            refine ⟨14804793780561303844173371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9869862520374202562782247 14804793780561303844173371)
            ·
              refine ⟨22207190670841955766260057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14804793780561303844173371 22207190670841955766260057)
              ·
                refine ⟨16655393003131466824695043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22207190670841955766260057 16655393003131466824695043)
                ·
                  refine ⟨24983089504697200237042565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16655393003131466824695043 24983089504697200237042565)
                  ·
                    refine ⟨4684329282130725044445481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24983089504697200237042565 4684329282130725044445481)
                    ·
                      refine ⟨3513246961598043783334111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4684329282130725044445481 3513246961598043783334111)
                      ·
                        rfl

theorem cell23_6842024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6842024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842024 prefixEnd_6842024 := by exact prefixLift 6842024
  have htrace : WordTrace (prefixWord ++ tailWord_6842024) baseStart_6842024 baseEnd_6842024 := by
    simpa [prefixWord, tailWord_6842024, baseEnd_6842024] using wordTrace_append hprefix tailTrace_6842024
  have hstable : (prefixWord ++ tailWord_6842024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842024).length < 2 ^ (prefixWord ++ tailWord_6842024).sum := by decide
  have hdescent : baseEnd_6842024 < baseStart_6842024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842073 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 3, 4]
def baseStart_6842073 : Nat := 118140960795 + 6842073 * 2 ^ 59
def prefixEnd_6842073 : Nat := 4983230072969 + 3 ^ 40 * 6842073 * 2
def baseEnd_6842073 : Nat := 1171090707383371363873795

theorem tailTrace_6842073 : CollatzResearch.WordTrace tailWord_6842073 prefixEnd_6842073 1171090707383371363873795 := by
  unfold tailWord_6842073
  simp only [CollatzResearch.WordTrace]
  refine ⟨249550903741345528881842873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166367269160897019254561915 249550903741345528881842873)
  ·
    refine ⟨187163177806009146661382155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249550903741345528881842873 187163177806009146661382155)
    ·
      refine ⟨280744766709013719992073233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187163177806009146661382155 280744766709013719992073233)
      ·
        refine ⟨210558575031760289994054925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280744766709013719992073233 210558575031760289994054925)
        ·
          refine ⟨78959465636910108747770597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210558575031760289994054925 78959465636910108747770597)
          ·
            refine ⟨14804899806920645390206987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78959465636910108747770597 14804899806920645390206987)
            ·
              refine ⟨22207349710380968085310481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14804899806920645390206987 22207349710380968085310481)
              ·
                refine ⟨16655512282785726063982861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22207349710380968085310481 16655512282785726063982861)
                ·
                  refine ⟨6245817106044647273993573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16655512282785726063982861 6245817106044647273993573)
                  ·
                    refine ⟨1171090707383371363873795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6245817106044647273993573 1171090707383371363873795)
                    ·
                      rfl

theorem cell23_6842073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 3, 4].length) (baseStart_6842073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842073 prefixEnd_6842073 := by exact prefixLift 6842073
  have htrace : WordTrace (prefixWord ++ tailWord_6842073) baseStart_6842073 baseEnd_6842073 := by
    simpa [prefixWord, tailWord_6842073, baseEnd_6842073] using wordTrace_append hprefix tailTrace_6842073
  have hstable : (prefixWord ++ tailWord_6842073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842073).length < 2 ^ (prefixWord ++ tailWord_6842073).sum := by decide
  have hdescent : baseEnd_6842073 < baseStart_6842073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842077 : List Nat := [1, 4, 3, 3, 1, 2, 1, 1, 2, 5]
def baseStart_6842077 : Nat := 118140960795 + 6842077 * 2 ^ 59
def prefixEnd_6842077 : Nat := 4983230072969 + 3 ^ 40 * 6842077 * 2
def baseEnd_6842077 : Nat := 1171091392024244025323789

theorem tailTrace_6842077 : CollatzResearch.WordTrace tailWord_6842077 prefixEnd_6842077 1171091392024244025323789 := by
  unfold tailWord_6842077
  simp only [CollatzResearch.WordTrace]
  refine ⟨249551049633331037564988485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166367366422220691709992323 249551049633331037564988485)
  ·
    refine ⟨46790821806249569543435341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249551049633331037564988485 46790821806249569543435341)
    ·
      refine ⟨17546558177343588578788253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46790821806249569543435341 17546558177343588578788253)
      ·
        refine ⟨6579959316503845717045595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17546558177343588578788253 6579959316503845717045595)
        ·
          refine ⟨9869938974755768575568393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6579959316503845717045595 9869938974755768575568393)
          ·
            refine ⟨7402454231066826431676295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9869938974755768575568393 7402454231066826431676295)
            ·
              refine ⟨11103681346600239647514443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402454231066826431676295 11103681346600239647514443)
              ·
                refine ⟨16655522019900359471271665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11103681346600239647514443 16655522019900359471271665)
                ·
                  refine ⟨12491641514925269603453749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16655522019900359471271665 12491641514925269603453749)
                  ·
                    refine ⟨1171091392024244025323789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12491641514925269603453749 1171091392024244025323789)
                    ·
                      rfl

theorem cell23_6842077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_6842077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842077 prefixEnd_6842077 := by exact prefixLift 6842077
  have htrace : WordTrace (prefixWord ++ tailWord_6842077) baseStart_6842077 baseEnd_6842077 := by
    simpa [prefixWord, tailWord_6842077, baseEnd_6842077] using wordTrace_append hprefix tailTrace_6842077
  have hstable : (prefixWord ++ tailWord_6842077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842077).length < 2 ^ (prefixWord ++ tailWord_6842077).sum := by decide
  have hdescent : baseEnd_6842077 < baseStart_6842077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842090 : List Nat := [3, 1, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_6842090 : Nat := 118140960795 + 6842090 * 2 ^ 59
def prefixEnd_6842090 : Nat := 4983230072969 + 3 ^ 40 * 6842090 * 2
def baseEnd_6842090 : Nat := 1171093617107080175036269

theorem tailTrace_6842090 : CollatzResearch.WordTrace tailWord_6842090 prefixEnd_6842090 1171093617107080175036269 := by
  unfold tailWord_6842090
  simp only [CollatzResearch.WordTrace]
  refine ⟨62387880945570985196302931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166367682521522627190141149 62387880945570985196302931)
  ·
    refine ⟨93581821418356477794454397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62387880945570985196302931 93581821418356477794454397)
    ·
      refine ⟨35093183031883679172920399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93581821418356477794454397 35093183031883679172920399)
      ·
        refine ⟨52639774547825518759380599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35093183031883679172920399 52639774547825518759380599)
        ·
          refine ⟨78959661821738278139070899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52639774547825518759380599 78959661821738278139070899)
          ·
            refine ⟨118439492732607417208606349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78959661821738278139070899 118439492732607417208606349)
            ·
              refine ⟨44414809774727781453227381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118439492732607417208606349 44414809774727781453227381)
              ·
                refine ⟨4163888416380729511240067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44414809774727781453227381 4163888416380729511240067)
                ·
                  refine ⟨6245832624571094266860101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163888416380729511240067 6245832624571094266860101)
                  ·
                    refine ⟨1171093617107080175036269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6245832624571094266860101 1171093617107080175036269)
                    ·
                      rfl

theorem cell23_6842090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_6842090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842090 prefixEnd_6842090 := by exact prefixLift 6842090
  have htrace : WordTrace (prefixWord ++ tailWord_6842090) baseStart_6842090 baseEnd_6842090 := by
    simpa [prefixWord, tailWord_6842090, baseEnd_6842090] using wordTrace_append hprefix tailTrace_6842090
  have hstable : (prefixWord ++ tailWord_6842090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842090).length < 2 ^ (prefixWord ++ tailWord_6842090).sum := by decide
  have hdescent : baseEnd_6842090 < baseStart_6842090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842123 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 1, 5, 2]
def baseStart_6842123 : Nat := 118140960795 + 6842123 * 2 ^ 59
def prefixEnd_6842123 : Nat := 4983230072969 + 3 ^ 40 * 6842123 * 2
def baseEnd_6842123 : Nat := 3513297796182838895996155

theorem tailTrace_6842123 : CollatzResearch.WordTrace tailWord_6842123 prefixEnd_6842123 3513297796182838895996155 := by
  unfold tailWord_6842123
  simp only [CollatzResearch.WordTrace]
  refine ⟨249552727391164387421163023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166368484927442924947442015 249552727391164387421163023)
  ·
    refine ⟨374329091086746581131744535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249552727391164387421163023 374329091086746581131744535)
    ·
      refine ⟨561493636630119871697616803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374329091086746581131744535 561493636630119871697616803)
      ·
        refine ⟨842240454945179807546425205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561493636630119871697616803 842240454945179807546425205)
        ·
          refine ⟨78960042651110606957477363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 842240454945179807546425205 78960042651110606957477363)
          ·
            refine ⟨118440063976665910436216045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78960042651110606957477363 118440063976665910436216045)
            ·
              refine ⟨44415023991249716413581017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118440063976665910436216045 44415023991249716413581017)
              ·
                refine ⟨33311267993437287310185763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44415023991249716413581017 33311267993437287310185763)
                ·
                  refine ⟨49966901990155930965278645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33311267993437287310185763 49966901990155930965278645)
                  ·
                    refine ⟨4684397061577118527994873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49966901990155930965278645 4684397061577118527994873)
                    ·
                      refine ⟨3513297796182838895996155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4684397061577118527994873 3513297796182838895996155)
                      ·
                        rfl

theorem cell23_6842123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5, 2].length) (baseStart_6842123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842123 prefixEnd_6842123 := by exact prefixLift 6842123
  have htrace : WordTrace (prefixWord ++ tailWord_6842123) baseStart_6842123 baseEnd_6842123 := by
    simpa [prefixWord, tailWord_6842123, baseEnd_6842123] using wordTrace_append hprefix tailTrace_6842123
  have hstable : (prefixWord ++ tailWord_6842123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842123).length < 2 ^ (prefixWord ++ tailWord_6842123).sum := by decide
  have hdescent : baseEnd_6842123 < baseStart_6842123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842126 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_6842126 : Nat := 118140960795 + 6842126 * 2 ^ 59
def prefixEnd_6842126 : Nat := 4983230072969 + 3 ^ 40 * 6842126 * 2
def baseEnd_6842126 : Nat := 3513299336624802384258641

theorem tailTrace_6842126 : CollatzResearch.WordTrace tailWord_6842126 prefixEnd_6842126 3513299336624802384258641 := by
  unfold tailWord_6842126
  simp only [CollatzResearch.WordTrace]
  refine ⟨31194104601269189866690279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166368557873435679289014821 31194104601269189866690279)
  ·
    refine ⟨46791156901903784800035419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31194104601269189866690279 46791156901903784800035419)
    ·
      refine ⟨70186735352855677200053129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46791156901903784800035419 70186735352855677200053129)
      ·
        refine ⟨52640051514641757900039847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70186735352855677200053129 52640051514641757900039847)
        ·
          refine ⟨78960077271962636850059771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52640051514641757900039847 78960077271962636850059771)
          ·
            refine ⟨118440115907943955275089657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78960077271962636850059771 118440115907943955275089657)
            ·
              refine ⟨88830086930957966456317243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118440115907943955275089657 88830086930957966456317243)
              ·
                refine ⟨133245130396436949684475865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88830086930957966456317243 133245130396436949684475865)
                ·
                  refine ⟨99933847797327712263356899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133245130396436949684475865 99933847797327712263356899)
                  ·
                    refine ⟨149900771695991568395035349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99933847797327712263356899 149900771695991568395035349)
                    ·
                      refine ⟨3513299336624802384258641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149900771695991568395035349 3513299336624802384258641)
                      ·
                        rfl

theorem cell23_6842126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_6842126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842126 prefixEnd_6842126 := by exact prefixLift 6842126
  have htrace : WordTrace (prefixWord ++ tailWord_6842126) baseStart_6842126 baseEnd_6842126 := by
    simpa [prefixWord, tailWord_6842126, baseEnd_6842126] using wordTrace_append hprefix tailTrace_6842126
  have hstable : (prefixWord ++ tailWord_6842126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842126).length < 2 ^ (prefixWord ++ tailWord_6842126).sum := by decide
  have hdescent : baseEnd_6842126 < baseStart_6842126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842133 : List Nat := [1, 3, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_6842133 : Nat := 118140960795 + 6842133 * 2 ^ 59
def prefixEnd_6842133 : Nat := 4983230072969 + 3 ^ 40 * 6842133 * 2
def baseEnd_6842133 : Nat := 1171100976996461285623703

theorem tailTrace_6842133 : CollatzResearch.WordTrace tailWord_6842133 prefixEnd_6842133 1171100976996461285623703 := by
  unfold tailWord_6842133
  simp only [CollatzResearch.WordTrace]
  refine ⟨249553092121128159129027053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166368728080752106086018035 249553092121128159129027053)
  ·
    refine ⟨93582409545423059673385145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249553092121128159129027053 93582409545423059673385145)
    ·
      refine ⟨70186807159067294755038859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93582409545423059673385145 70186807159067294755038859)
      ·
        refine ⟨105280210738600942132558289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70186807159067294755038859 105280210738600942132558289)
        ·
          refine ⟨78960158053950706599418717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105280210738600942132558289 78960158053950706599418717)
          ·
            refine ⟨29610059270231514974782019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78960158053950706599418717 29610059270231514974782019)
            ·
              refine ⟨44415088905347272462173029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29610059270231514974782019 44415088905347272462173029)
              ·
                refine ⟨8327829169752613586657443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44415088905347272462173029 8327829169752613586657443)
                ·
                  refine ⟨12491743754628920379986165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327829169752613586657443 12491743754628920379986165)
                  ·
                    refine ⟨1171100976996461285623703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12491743754628920379986165 1171100976996461285623703)
                    ·
                      rfl

theorem cell23_6842133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_6842133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842133 prefixEnd_6842133 := by exact prefixLift 6842133
  have htrace : WordTrace (prefixWord ++ tailWord_6842133) baseStart_6842133 baseEnd_6842133 := by
    simpa [prefixWord, tailWord_6842133, baseEnd_6842133] using wordTrace_append hprefix tailTrace_6842133
  have hstable : (prefixWord ++ tailWord_6842133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842133).length < 2 ^ (prefixWord ++ tailWord_6842133).sum := by decide
  have hdescent : baseEnd_6842133 < baseStart_6842133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842140 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_6842140 : Nat := 118140960795 + 6842140 * 2 ^ 59
def prefixEnd_6842140 : Nat := 4983230072969 + 3 ^ 40 * 6842140 * 2
def baseEnd_6842140 : Nat := 3513306525353965329483577

theorem tailTrace_6842140 : CollatzResearch.WordTrace tailWord_6842140 prefixEnd_6842140 3513306525353965329483577 := by
  unfold tailWord_6842140
  simp only [CollatzResearch.WordTrace]
  refine ⟨124776673716051399662265937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166368898288068532883021249 124776673716051399662265937)
  ·
    refine ⟨93582505287038549746699453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124776673716051399662265937 93582505287038549746699453)
    ·
      refine ⟨35093439482639456155012295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93582505287038549746699453 35093439482639456155012295)
      ·
        refine ⟨52640159223959184232518443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35093439482639456155012295 52640159223959184232518443)
        ·
          refine ⟨78960238835938776348777665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52640159223959184232518443 78960238835938776348777665)
          ·
            refine ⟨59220179126954082261583249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78960238835938776348777665 59220179126954082261583249)
            ·
              refine ⟨44415134345215561696187437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59220179126954082261583249 44415134345215561696187437)
              ·
                refine ⟨16655675379455835636070289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44415134345215561696187437 16655675379455835636070289)
                ·
                  refine ⟨12491756534591876727052717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16655675379455835636070289 12491756534591876727052717)
                  ·
                    refine ⟨4684408700471953772644769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12491756534591876727052717 4684408700471953772644769)
                    ·
                      refine ⟨3513306525353965329483577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4684408700471953772644769 3513306525353965329483577)
                      ·
                        rfl

theorem cell23_6842140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_6842140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842140 prefixEnd_6842140 := by exact prefixLift 6842140
  have htrace : WordTrace (prefixWord ++ tailWord_6842140) baseStart_6842140 baseEnd_6842140 := by
    simpa [prefixWord, tailWord_6842140, baseEnd_6842140] using wordTrace_append hprefix tailTrace_6842140
  have hstable : (prefixWord ++ tailWord_6842140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842140).length < 2 ^ (prefixWord ++ tailWord_6842140).sum := by decide
  have hdescent : baseEnd_6842140 < baseStart_6842140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842147 : List Nat := [1, 1, 1, 4, 2, 1, 5, 3, 1, 1, 3]
def baseStart_6842147 : Nat := 118140960795 + 6842147 * 2 ^ 59
def prefixEnd_6842147 : Nat := 4983230072969 + 3 ^ 40 * 6842147 * 2
def baseEnd_6842147 : Nat := 3513310119718546802096045

theorem tailTrace_6842147 : CollatzResearch.WordTrace tailWord_6842147 prefixEnd_6842147 3513310119718546802096045 := by
  unfold tailWord_6842147
  simp only [CollatzResearch.WordTrace]
  refine ⟨249553602743077439520036695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166369068495384959680024463 249553602743077439520036695)
  ·
    refine ⟨374330404114616159280055043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249553602743077439520036695 374330404114616159280055043)
    ·
      refine ⟨561495606171924238920082565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374330404114616159280055043 561495606171924238920082565)
      ·
        refine ⟨105280426157235794797515481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 561495606171924238920082565 105280426157235794797515481)
        ·
          refine ⟨78960319617926846098136611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105280426157235794797515481 78960319617926846098136611)
          ·
            refine ⟨118440479426890269147204917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78960319617926846098136611 118440479426890269147204917)
            ·
              refine ⟨11103794946270962732550461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118440479426890269147204917 11103794946270962732550461)
              ·
                refine ⟨4163923104851611024706423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11103794946270962732550461 4163923104851611024706423)
                ·
                  refine ⟨6245884657277416537059635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163923104851611024706423 6245884657277416537059635)
                  ·
                    refine ⟨9368826985916124805589453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6245884657277416537059635 9368826985916124805589453)
                    ·
                      refine ⟨3513310119718546802096045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368826985916124805589453 3513310119718546802096045)
                      ·
                        rfl

theorem cell23_6842147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_6842147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842147 prefixEnd_6842147 := by exact prefixLift 6842147
  have htrace : WordTrace (prefixWord ++ tailWord_6842147) baseStart_6842147 baseEnd_6842147 := by
    simpa [prefixWord, tailWord_6842147, baseEnd_6842147] using wordTrace_append hprefix tailTrace_6842147
  have hstable : (prefixWord ++ tailWord_6842147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842147).length < 2 ^ (prefixWord ++ tailWord_6842147).sum := by decide
  have hdescent : baseEnd_6842147 < baseStart_6842147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842164 : List Nat := [2, 5, 1, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_6842164 : Nat := 118140960795 + 6842164 * 2 ^ 59
def prefixEnd_6842164 : Nat := 4983230072969 + 3 ^ 40 * 6842164 * 2
def baseEnd_6842164 : Nat := 3513318848889673235583467

theorem tailTrace_6842164 : CollatzResearch.WordTrace tailWord_6842164 prefixEnd_6842164 3513318848889673235583467 := by
  unfold tailWord_6842164
  simp only [CollatzResearch.WordTrace]
  refine ⟨124777111392007925711702773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166369481856010567615603697 124777111392007925711702773)
  ·
    refine ⟨11697854193000743035472135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124777111392007925711702773 11697854193000743035472135)
    ·
      refine ⟨17546781289501114553208203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11697854193000743035472135 17546781289501114553208203)
      ·
        refine ⟨26320171934251671829812305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17546781289501114553208203 26320171934251671829812305)
        ·
          refine ⟨19740128950688753872359229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26320171934251671829812305 19740128950688753872359229)
          ·
            refine ⟨7402548356508282702134711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19740128950688753872359229 7402548356508282702134711)
            ·
              refine ⟨11103822534762424053202067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402548356508282702134711 11103822534762424053202067)
              ·
                refine ⟨16655733802143636079803101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11103822534762424053202067 16655733802143636079803101)
                ·
                  refine ⟨6245900175803863529926163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16655733802143636079803101 6245900175803863529926163)
                  ·
                    refine ⟨9368850263705795294889245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6245900175803863529926163 9368850263705795294889245)
                    ·
                      refine ⟨3513318848889673235583467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368850263705795294889245 3513318848889673235583467)
                      ·
                        rfl

theorem cell23_6842164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_6842164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842164 prefixEnd_6842164 := by exact prefixLift 6842164
  have htrace : WordTrace (prefixWord ++ tailWord_6842164) baseStart_6842164 baseEnd_6842164 := by
    simpa [prefixWord, tailWord_6842164, baseEnd_6842164] using wordTrace_append hprefix tailTrace_6842164
  have hstable : (prefixWord ++ tailWord_6842164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842164).length < 2 ^ (prefixWord ++ tailWord_6842164).sum := by decide
  have hdescent : baseEnd_6842164 < baseStart_6842164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842204 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_6842204 : Nat := 118140960795 + 6842204 * 2 ^ 59
def prefixEnd_6842204 : Nat := 4983230072969 + 3 ^ 40 * 6842204 * 2
def baseEnd_6842204 : Nat := 3513339388115853079083283

theorem tailTrace_6842204 : CollatzResearch.WordTrace tailWord_6842204 prefixEnd_6842204 3513339388115853079083283 := by
  unfold tailWord_6842204
  simp only [CollatzResearch.WordTrace]
  refine ⟨124777840851935469127430833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166370454469247292169907777 124777840851935469127430833)
  ·
    refine ⟨93583380638951601845573125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124777840851935469127430833 93583380638951601845573125)
    ·
      refine ⟨17546883869803425346044961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93583380638951601845573125 17546883869803425346044961)
      ·
        refine ⟨13160162902352569009533721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17546883869803425346044961 13160162902352569009533721)
        ·
          refine ⟨9870122176764426757150291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13160162902352569009533721 9870122176764426757150291)
          ·
            refine ⟨14805183265146640135725437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870122176764426757150291 14805183265146640135725437)
            ·
              refine ⟨5551943724429990050897039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14805183265146640135725437 5551943724429990050897039)
              ·
                refine ⟨8327915586644985076345559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551943724429990050897039 8327915586644985076345559)
                ·
                  refine ⟨12491873379967477614518339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327915586644985076345559 12491873379967477614518339)
                  ·
                    refine ⟨18737810069951216421777509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12491873379967477614518339 18737810069951216421777509)
                    ·
                      refine ⟨3513339388115853079083283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18737810069951216421777509 3513339388115853079083283)
                      ·
                        rfl

theorem cell23_6842204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_6842204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842204 prefixEnd_6842204 := by exact prefixLift 6842204
  have htrace : WordTrace (prefixWord ++ tailWord_6842204) baseStart_6842204 baseEnd_6842204 := by
    simpa [prefixWord, tailWord_6842204, baseEnd_6842204] using wordTrace_append hprefix tailTrace_6842204
  have hstable : (prefixWord ++ tailWord_6842204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842204).length < 2 ^ (prefixWord ++ tailWord_6842204).sum := by decide
  have hdescent : baseEnd_6842204 < baseStart_6842204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842207 : List Nat := [1, 1, 2, 3, 1, 5, 3, 1, 1, 2, 3]
def baseStart_6842207 : Nat := 118140960795 + 6842207 * 2 ^ 59
def prefixEnd_6842207 : Nat := 4983230072969 + 3 ^ 40 * 6842207 * 2
def baseEnd_6842207 : Nat := 3513340928557816567345769

theorem tailTrace_6842207 : CollatzResearch.WordTrace tailWord_6842207 prefixEnd_6842207 3513340928557816567345769 := by
  unfold tailWord_6842207
  simp only [CollatzResearch.WordTrace]
  refine ⟨249555791122860069767220875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166370527415240046511480583 249555791122860069767220875)
  ·
    refine ⟨374333686684290104650831313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249555791122860069767220875 374333686684290104650831313)
    ·
      refine ⟨280750265013217578488123485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374333686684290104650831313 280750265013217578488123485)
      ·
        refine ⟨105281349379956591933046307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280750265013217578488123485 105281349379956591933046307)
        ·
          refine ⟨157922024069934887899569461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105281349379956591933046307 157922024069934887899569461)
          ·
            refine ⟨14805189756556395740584637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157922024069934887899569461 14805189756556395740584637)
            ·
              refine ⟨5551946158708648402719239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14805189756556395740584637 5551946158708648402719239)
              ·
                refine ⟨8327919238062972604078859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551946158708648402719239 8327919238062972604078859)
                ·
                  refine ⟨12491878857094458906118289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8327919238062972604078859 12491878857094458906118289)
                  ·
                    refine ⟨9368909142820844179588717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12491878857094458906118289 9368909142820844179588717)
                    ·
                      refine ⟨3513340928557816567345769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368909142820844179588717 3513340928557816567345769)
                      ·
                        rfl

theorem cell23_6842207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_6842207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842207 prefixEnd_6842207 := by exact prefixLift 6842207
  have htrace : WordTrace (prefixWord ++ tailWord_6842207) baseStart_6842207 baseEnd_6842207 := by
    simpa [prefixWord, tailWord_6842207, baseEnd_6842207] using wordTrace_append hprefix tailTrace_6842207
  have hstable : (prefixWord ++ tailWord_6842207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842207).length < 2 ^ (prefixWord ++ tailWord_6842207).sum := by decide
  have hdescent : baseEnd_6842207 < baseStart_6842207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842221 : List Nat := [1, 5, 1, 1, 1, 1, 6, 2, 1, 2, 2]
def baseStart_6842221 : Nat := 118140960795 + 6842221 * 2 ^ 59
def prefixEnd_6842221 : Nat := 4983230072969 + 3 ^ 40 * 6842221 * 2
def baseEnd_6842221 : Nat := 3513348117286979512570705

theorem tailTrace_6842221 : CollatzResearch.WordTrace tailWord_6842221 prefixEnd_6842221 3513348117286979512570705 := by
  unfold tailWord_6842221
  simp only [CollatzResearch.WordTrace]
  refine ⟨249556301744809350158230517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166370867829872900105487011 249556301744809350158230517)
  ·
    refine ⟨23395903288575876577334111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249556301744809350158230517 23395903288575876577334111)
    ·
      refine ⟨35093854932863814866001167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23395903288575876577334111 35093854932863814866001167)
      ·
        refine ⟨52640782399295722299001751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35093854932863814866001167 52640782399295722299001751)
        ·
          refine ⟨78961173598943583448502627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52640782399295722299001751 78961173598943583448502627)
          ·
            refine ⟨118441760398415375172753941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78961173598943583448502627 118441760398415375172753941)
            ·
              refine ⟨5551957518675720711222841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118441760398415375172753941 5551957518675720711222841)
              ·
                refine ⟨4163968139006790533417131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5551957518675720711222841 4163968139006790533417131)
                ·
                  refine ⟨6245952208510185800125697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163968139006790533417131 6245952208510185800125697)
                  ·
                    refine ⟨4684464156382639350094273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6245952208510185800125697 4684464156382639350094273)
                    ·
                      refine ⟨3513348117286979512570705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4684464156382639350094273 3513348117286979512570705)
                      ·
                        rfl

theorem cell23_6842221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_6842221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842221 prefixEnd_6842221 := by exact prefixLift 6842221
  have htrace : WordTrace (prefixWord ++ tailWord_6842221) baseStart_6842221 baseEnd_6842221 := by
    simpa [prefixWord, tailWord_6842221, baseEnd_6842221] using wordTrace_append hprefix tailTrace_6842221
  have hstable : (prefixWord ++ tailWord_6842221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842221).length < 2 ^ (prefixWord ++ tailWord_6842221).sum := by decide
  have hdescent : baseEnd_6842221 < baseStart_6842221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842271 : List Nat := [1, 1, 2, 5, 4, 1, 1, 2, 2, 1, 3]
def baseStart_6842271 : Nat := 118140960795 + 6842271 * 2 ^ 59
def prefixEnd_6842271 : Nat := 4983230072969 + 3 ^ 40 * 6842271 * 2
def baseEnd_6842271 : Nat := 3513373791319704316945475

theorem tailTrace_6842271 : CollatzResearch.WordTrace tailWord_6842271 prefixEnd_6842271 3513373791319704316945475 := by
  unfold tailWord_6842271
  simp only [CollatzResearch.WordTrace]
  refine ⟨249558125394628208697550667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166372083596418805798367111 249558125394628208697550667)
  ·
    refine ⟨374337188091942313046326001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249558125394628208697550667 374337188091942313046326001)
    ·
      refine ⟨280752891068956734784744501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374337188091942313046326001 280752891068956734784744501)
      ·
        refine ⟨26320583537714693886069797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280752891068956734784744501 26320583537714693886069797)
        ·
          refine ⟨4935109413321505103638087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26320583537714693886069797 4935109413321505103638087)
          ·
            refine ⟨7402664119982257655457131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935109413321505103638087 7402664119982257655457131)
            ·
              refine ⟨11103996179973386483185697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402664119982257655457131 11103996179973386483185697)
              ·
                refine ⟨8327997134980039862389273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11103996179973386483185697 8327997134980039862389273)
                ·
                  refine ⟨6245997851235029896791955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8327997134980039862389273 6245997851235029896791955)
                  ·
                    refine ⟨9368996776852544845187933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6245997851235029896791955 9368996776852544845187933)
                    ·
                      refine ⟨3513373791319704316945475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9368996776852544845187933 3513373791319704316945475)
                      ·
                        rfl

theorem cell23_6842271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_6842271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842271 prefixEnd_6842271 := by exact prefixLift 6842271
  have htrace : WordTrace (prefixWord ++ tailWord_6842271) baseStart_6842271 baseEnd_6842271 := by
    simpa [prefixWord, tailWord_6842271, baseEnd_6842271] using wordTrace_append hprefix tailTrace_6842271
  have hstable : (prefixWord ++ tailWord_6842271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842271).length < 2 ^ (prefixWord ++ tailWord_6842271).sum := by decide
  have hdescent : baseEnd_6842271 < baseStart_6842271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842360 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 3, 4]
def baseStart_6842360 : Nat := 118140960795 + 6842360 * 2 ^ 59
def prefixEnd_6842360 : Nat := 4983230072969 + 3 ^ 40 * 6842360 * 2
def baseEnd_6842360 : Nat := 1171139830365984822910855

theorem tailTrace_6842360 : CollatzResearch.WordTrace tailWord_6842360 prefixEnd_6842360 1171139830365984822910855 := by
  unfold tailWord_6842360
  simp only [CollatzResearch.WordTrace]
  refine ⟨124780685745652888448770267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166374247660870517931693689 124780685745652888448770267)
  ·
    refine ⟨187171028618479332673155401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124780685745652888448770267 187171028618479332673155401)
    ·
      refine ⟨140378271463859499504866551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187171028618479332673155401 140378271463859499504866551)
      ·
        refine ⟨210567407195789249257299827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140378271463859499504866551 210567407195789249257299827)
        ·
          refine ⟨315851110793683873885949741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210567407195789249257299827 315851110793683873885949741)
          ·
            refine ⟨118444166547631452707231153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315851110793683873885949741 118444166547631452707231153)
            ·
              refine ⟨88833124910723589530423365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118444166547631452707231153 88833124910723589530423365)
              ·
                refine ⟨16656210920760673036954381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88833124910723589530423365 16656210920760673036954381)
                ·
                  refine ⟨6246079095285252388857893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16656210920760673036954381 6246079095285252388857893)
                  ·
                    refine ⟨1171139830365984822910855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246079095285252388857893 1171139830365984822910855)
                    ·
                      rfl

theorem cell23_6842360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_6842360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842360 prefixEnd_6842360 := by exact prefixLift 6842360
  have htrace : WordTrace (prefixWord ++ tailWord_6842360) baseStart_6842360 baseEnd_6842360 := by
    simpa [prefixWord, tailWord_6842360, baseEnd_6842360] using wordTrace_append hprefix tailTrace_6842360
  have hstable : (prefixWord ++ tailWord_6842360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842360).length < 2 ^ (prefixWord ++ tailWord_6842360).sum := by decide
  have hdescent : baseEnd_6842360 < baseStart_6842360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842363 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4]
def baseStart_6842363 : Nat := 118140960795 + 6842363 * 2 ^ 59
def prefixEnd_6842363 : Nat := 4983230072969 + 3 ^ 40 * 6842363 * 2
def baseEnd_6842363 : Nat := 3513421031539917956995051

theorem tailTrace_6842363 : CollatzResearch.WordTrace tailWord_6842363 prefixEnd_6842363 3513421031539917956995051 := by
  unfold tailWord_6842363
  simp only [CollatzResearch.WordTrace]
  refine ⟨249561480910294908409899743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166374320606863272273266495 249561480910294908409899743)
  ·
    refine ⟨374342221365442362614849615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249561480910294908409899743 374342221365442362614849615)
    ·
      refine ⟨561513332048163543922274423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374342221365442362614849615 561513332048163543922274423)
      ·
        refine ⟨842269998072245315883411635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561513332048163543922274423 842269998072245315883411635)
        ·
          refine ⟨1263404997108367973825117453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842269998072245315883411635 1263404997108367973825117453)
          ·
            refine ⟨473776873915637990184419045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263404997108367973825117453 473776873915637990184419045)
            ·
              refine ⟨88833163859182123159578571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 473776873915637990184419045 88833163859182123159578571)
              ·
                refine ⟨133249745788773184739367857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88833163859182123159578571 133249745788773184739367857)
                ·
                  refine ⟨99937309341579888554525893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133249745788773184739367857 99937309341579888554525893)
                  ·
                    refine ⟨18738245501546229103973605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99937309341579888554525893 18738245501546229103973605)
                    ·
                      refine ⟨3513421031539917956995051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18738245501546229103973605 3513421031539917956995051)
                      ·
                        rfl

theorem cell23_6842363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_6842363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842363 prefixEnd_6842363 := by exact prefixLift 6842363
  have htrace : WordTrace (prefixWord ++ tailWord_6842363) baseStart_6842363 baseEnd_6842363 := by
    simpa [prefixWord, tailWord_6842363, baseEnd_6842363] using wordTrace_append hprefix tailTrace_6842363
  have hstable : (prefixWord ++ tailWord_6842363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842363).length < 2 ^ (prefixWord ++ tailWord_6842363).sum := by decide
  have hdescent : baseEnd_6842363 < baseStart_6842363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842393 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_6842393 : Nat := 118140960795 + 6842393 * 2 ^ 59
def prefixEnd_6842393 : Nat := 4983230072969 + 3 ^ 40 * 6842393 * 2
def baseEnd_6842393 : Nat := 3513436435959552839619913

theorem tailTrace_6842393 : CollatzResearch.WordTrace tailWord_6842393 prefixEnd_6842393 3513436435959552839619913 := by
  unfold tailWord_6842393
  simp only [CollatzResearch.WordTrace]
  refine ⟨249562575100186223533491833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166375050066790815688994555 249562575100186223533491833)
  ·
    refine ⟨187171931325139667650118875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249562575100186223533491833 187171931325139667650118875)
    ·
      refine ⟨280757896987709501475178313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187171931325139667650118875 280757896987709501475178313)
      ·
        refine ⟨210568422740782126106383735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280757896987709501475178313 210568422740782126106383735)
        ·
          refine ⟨315852634111173189159575603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210568422740782126106383735 315852634111173189159575603)
          ·
            refine ⟨473778951166759783739363405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315852634111173189159575603 473778951166759783739363405)
            ·
              refine ⟨177667106687534918902261277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473778951166759783739363405 177667106687534918902261277)
              ·
                refine ⟨66625165007825594588347979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177667106687534918902261277 66625165007825594588347979)
                ·
                  refine ⟨99937747511738391882521969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66625165007825594588347979 99937747511738391882521969)
                  ·
                    refine ⟨74953310633803793911891477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99937747511738391882521969 74953310633803793911891477)
                    ·
                      refine ⟨3513436435959552839619913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74953310633803793911891477 3513436435959552839619913)
                      ·
                        rfl

theorem cell23_6842393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_6842393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842393 prefixEnd_6842393 := by exact prefixLift 6842393
  have htrace : WordTrace (prefixWord ++ tailWord_6842393) baseStart_6842393 baseEnd_6842393 := by
    simpa [prefixWord, tailWord_6842393, baseEnd_6842393] using wordTrace_append hprefix tailTrace_6842393
  have hstable : (prefixWord ++ tailWord_6842393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842393).length < 2 ^ (prefixWord ++ tailWord_6842393).sum := by decide
  have hdescent : baseEnd_6842393 < baseStart_6842393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842394 : List Nat := [3, 1, 1, 3, 1, 4, 1, 4, 1, 4]
def baseStart_6842394 : Nat := 118140960795 + 6842394 * 2 ^ 59
def prefixEnd_6842394 : Nat := 4983230072969 + 3 ^ 40 * 6842394 * 2
def baseEnd_6842394 : Nat := 1171145649813402445235803

theorem tailTrace_6842394 : CollatzResearch.WordTrace tailWord_6842394 prefixEnd_6842394 1171145649813402445235803 := by
  unfold tailWord_6842394
  simp only [CollatzResearch.WordTrace]
  refine ⟨62390652893295650176069559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166375074382121733802852157 62390652893295650176069559)
  ·
    refine ⟨93585979339943475264104339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62390652893295650176069559 93585979339943475264104339)
    ·
      refine ⟨140378969009915212896156509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93585979339943475264104339 140378969009915212896156509)
      ·
        refine ⟨52642113378718204836058691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140378969009915212896156509 52642113378718204836058691)
        ·
          refine ⟨78963170068077307254088037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52642113378718204836058691 78963170068077307254088037)
          ·
            refine ⟨14805594387764495110141507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78963170068077307254088037 14805594387764495110141507)
            ·
              refine ⟨22208391581646742665212261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14805594387764495110141507 22208391581646742665212261)
              ·
                refine ⟨4164073421558764249727299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22208391581646742665212261 4164073421558764249727299)
                ·
                  refine ⟨6246110132338146374590949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164073421558764249727299 6246110132338146374590949)
                  ·
                    refine ⟨1171145649813402445235803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246110132338146374590949 1171145649813402445235803)
                    ·
                      rfl

theorem cell23_6842394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 1, 4].length) (baseStart_6842394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842394 prefixEnd_6842394 := by exact prefixLift 6842394
  have htrace : WordTrace (prefixWord ++ tailWord_6842394) baseStart_6842394 baseEnd_6842394 := by
    simpa [prefixWord, tailWord_6842394, baseEnd_6842394] using wordTrace_append hprefix tailTrace_6842394
  have hstable : (prefixWord ++ tailWord_6842394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842394).length < 2 ^ (prefixWord ++ tailWord_6842394).sum := by decide
  have hdescent : baseEnd_6842394 < baseStart_6842394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842417 : List Nat := [1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 3]
def baseStart_6842417 : Nat := 118140960795 + 6842417 * 2 ^ 59
def prefixEnd_6842417 : Nat := 4983230072969 + 3 ^ 40 * 6842417 * 2
def baseEnd_6842417 : Nat := 3513448759495260745719803

theorem tailTrace_6842417 : CollatzResearch.WordTrace tailWord_6842417 prefixEnd_6842417 3513448759495260745719803 := by
  unfold tailWord_6842417
  simp only [CollatzResearch.WordTrace]
  refine ⟨249563450452099275632365505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166375633634732850421577003 249563450452099275632365505)
  ·
    refine ⟨187172587839074456724274129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249563450452099275632365505 187172587839074456724274129)
    ·
      refine ⟨140379440879305842543205597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187172587839074456724274129 140379440879305842543205597)
      ·
        refine ⟨52642290329739690953702099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140379440879305842543205597 52642290329739690953702099)
        ·
          refine ⟨78963435494609536430553149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52642290329739690953702099 78963435494609536430553149)
          ·
            refine ⟨29611288310478576161457431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78963435494609536430553149 29611288310478576161457431)
            ·
              refine ⟨44416932465717864242186147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29611288310478576161457431 44416932465717864242186147)
              ·
                refine ⟨66625398698576796363279221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44416932465717864242186147 66625398698576796363279221)
                ·
                  refine ⟨6246131127991574659057427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66625398698576796363279221 6246131127991574659057427)
                  ·
                    refine ⟨9369196691987361988586141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6246131127991574659057427 9369196691987361988586141)
                    ·
                      refine ⟨3513448759495260745719803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9369196691987361988586141 3513448759495260745719803)
                      ·
                        rfl

theorem cell23_6842417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_6842417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842417 prefixEnd_6842417 := by exact prefixLift 6842417
  have htrace : WordTrace (prefixWord ++ tailWord_6842417) baseStart_6842417 baseEnd_6842417 := by
    simpa [prefixWord, tailWord_6842417, baseEnd_6842417] using wordTrace_append hprefix tailTrace_6842417
  have hstable : (prefixWord ++ tailWord_6842417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842417).length < 2 ^ (prefixWord ++ tailWord_6842417).sum := by decide
  have hdescent : baseEnd_6842417 < baseStart_6842417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842440 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_6842440 : Nat := 118140960795 + 6842440 * 2 ^ 59
def prefixEnd_6842440 : Nat := 4983230072969 + 3 ^ 40 * 6842440 * 2
def baseEnd_6842440 : Nat := 3513460569550314155732197

theorem tailTrace_6842440 : CollatzResearch.WordTrace tailWord_6842440 prefixEnd_6842440 3513460569550314155732197 := by
  unfold tailWord_6842440
  simp only [CollatzResearch.WordTrace]
  refine ⟨124782144665507975280226387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166376192887343967040301849 124782144665507975280226387)
  ·
    refine ⟨187173216998261962920339581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124782144665507975280226387 187173216998261962920339581)
    ·
      refine ⟨70189956374348236095127343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187173216998261962920339581 70189956374348236095127343)
      ·
        refine ⟨105284934561522354142691015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70189956374348236095127343 105284934561522354142691015)
        ·
          refine ⟨157927401842283531214036523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105284934561522354142691015 157927401842283531214036523)
          ·
            refine ⟨236891102763425296821054785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157927401842283531214036523 236891102763425296821054785)
            ·
              refine ⟨177668327072568972615791089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236891102763425296821054785 177668327072568972615791089)
              ·
                refine ⟨133251245304426729461843317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177668327072568972615791089 133251245304426729461843317)
                ·
                  refine ⟨12492304247290005887047811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133251245304426729461843317 12492304247290005887047811)
                  ·
                    refine ⟨18738456370935008830571717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12492304247290005887047811 18738456370935008830571717)
                    ·
                      refine ⟨3513460569550314155732197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18738456370935008830571717 3513460569550314155732197)
                      ·
                        rfl

theorem cell23_6842440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_6842440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842440 prefixEnd_6842440 := by exact prefixLift 6842440
  have htrace : WordTrace (prefixWord ++ tailWord_6842440) baseStart_6842440 baseEnd_6842440 := by
    simpa [prefixWord, tailWord_6842440, baseEnd_6842440] using wordTrace_append hprefix tailTrace_6842440
  have hstable : (prefixWord ++ tailWord_6842440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842440).length < 2 ^ (prefixWord ++ tailWord_6842440).sum := by decide
  have hdescent : baseEnd_6842440 < baseStart_6842440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842467 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 2, 4]
def baseStart_6842467 : Nat := 118140960795 + 6842467 * 2 ^ 59
def prefixEnd_6842467 : Nat := 4983230072969 + 3 ^ 40 * 6842467 * 2
def baseEnd_6842467 : Nat := 1171158144509328516698191

theorem tailTrace_6842467 : CollatzResearch.WordTrace tailWord_6842467 prefixEnd_6842467 1171158144509328516698191 := by
  unfold tailWord_6842467
  simp only [CollatzResearch.WordTrace]
  refine ⟨249565274101918134171685655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166376849401278756114457103 249565274101918134171685655)
  ·
    refine ⟨374347911152877201257528483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249565274101918134171685655 374347911152877201257528483)
    ·
      refine ⟨561521866729315801886292725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374347911152877201257528483 561521866729315801886292725)
      ·
        refine ⟨52642675005873356426839943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 561521866729315801886292725 52642675005873356426839943)
        ·
          refine ⟨78964012508810034640259915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52642675005873356426839943 78964012508810034640259915)
          ·
            refine ⟨118446018763215051960389873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78964012508810034640259915 118446018763215051960389873)
            ·
              refine ⟨88834514072411288970292405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118446018763215051960389873 88834514072411288970292405)
              ·
                refine ⟨8328235694288558340964913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88834514072411288970292405 8328235694288558340964913)
                ·
                  refine ⟨6246176770716418755723685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8328235694288558340964913 6246176770716418755723685)
                  ·
                    refine ⟨1171158144509328516698191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246176770716418755723685 1171158144509328516698191)
                    ·
                      rfl

theorem cell23_6842467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 2, 4].length) (baseStart_6842467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842467 prefixEnd_6842467 := by exact prefixLift 6842467
  have htrace : WordTrace (prefixWord ++ tailWord_6842467) baseStart_6842467 baseEnd_6842467 := by
    simpa [prefixWord, tailWord_6842467, baseEnd_6842467] using wordTrace_append hprefix tailTrace_6842467
  have hstable : (prefixWord ++ tailWord_6842467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842467).length < 2 ^ (prefixWord ++ tailWord_6842467).sum := by decide
  have hdescent : baseEnd_6842467 < baseStart_6842467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842480 : List Nat := [2, 1, 1, 1, 5, 3, 1, 9]
def baseStart_6842480 : Nat := 118140960795 + 6842480 * 2 ^ 59
def prefixEnd_6842480 : Nat := 4983230072969 + 3 ^ 40 * 6842480 * 2
def baseEnd_6842480 : Nat := 130128929954684962934519

theorem tailTrace_6842480 : CollatzResearch.WordTrace tailWord_6842480 prefixEnd_6842480 130128929954684962934519 := by
  unfold tailWord_6842480
  simp only [CollatzResearch.WordTrace]
  refine ⟨124782874125435518695954447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166377165500580691594605929 124782874125435518695954447)
  ·
    refine ⟨187174311188153278043931671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124782874125435518695954447 187174311188153278043931671)
    ·
      refine ⟨280761466782229917065897507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187174311188153278043931671 280761466782229917065897507)
      ·
        refine ⟨421142200173344875598846261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280761466782229917065897507 421142200173344875598846261)
        ·
          refine ⟨39482081266251082087391837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421142200173344875598846261 39482081266251082087391837)
          ·
            refine ⟨14805780474844155782771939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39482081266251082087391837 14805780474844155782771939)
            ·
              refine ⟨22208670712266233674157909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14805780474844155782771939 22208670712266233674157909)
              ·
                refine ⟨130128929954684962934519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22208670712266233674157909 130128929954684962934519)
                ·
                  rfl

theorem cell23_6842480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 9].length) (baseStart_6842480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842480 prefixEnd_6842480 := by exact prefixLift 6842480
  have htrace : WordTrace (prefixWord ++ tailWord_6842480) baseStart_6842480 baseEnd_6842480 := by
    simpa [prefixWord, tailWord_6842480, baseEnd_6842480] using wordTrace_append hprefix tailTrace_6842480
  have hstable : (prefixWord ++ tailWord_6842480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842480).length < 2 ^ (prefixWord ++ tailWord_6842480).sum := by decide
  have hdescent : baseEnd_6842480 < baseStart_6842480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842497 : List Nat := [1, 2, 4, 2, 3, 2, 9]
def baseStart_6842497 : Nat := 118140960795 + 6842497 * 2 ^ 59
def prefixEnd_6842497 : Nat := 4983230072969 + 3 ^ 40 * 6842497 * 2
def baseEnd_6842497 : Nat := 43376417752439758428635

theorem tailTrace_6842497 : CollatzResearch.WordTrace tailWord_6842497 prefixEnd_6842497 43376417752439758428635 := by
  unfold tailWord_6842497
  simp only [CollatzResearch.WordTrace]
  refine ⟨249566368291809449295277745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166377578861206299530185163 249566368291809449295277745)
  ·
    refine ⟨187174776218857086971458309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249566368291809449295277745 187174776218857086971458309)
    ·
      refine ⟨35095270541035703807148433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187174776218857086971458309 35095270541035703807148433)
      ·
        refine ⟨26321452905776777855361325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35095270541035703807148433 26321452905776777855361325)
        ·
          refine ⟨9870544839666291695760497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26321452905776777855361325 9870544839666291695760497)
          ·
            refine ⟨7402908629749718771820373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9870544839666291695760497 7402908629749718771820373)
            ·
              refine ⟨43376417752439758428635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7402908629749718771820373 43376417752439758428635)
              ·
                rfl

theorem cell23_6842497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 9].length) (baseStart_6842497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842497 prefixEnd_6842497 := by exact prefixLift 6842497
  have htrace : WordTrace (prefixWord ++ tailWord_6842497) baseStart_6842497 baseEnd_6842497 := by
    simpa [prefixWord, tailWord_6842497, baseEnd_6842497] using wordTrace_append hprefix tailTrace_6842497
  have hstable : (prefixWord ++ tailWord_6842497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842497).length < 2 ^ (prefixWord ++ tailWord_6842497).sum := by decide
  have hdescent : baseEnd_6842497 < baseStart_6842497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842558 : List Nat := [4, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_6842558 : Nat := 118140960795 + 6842558 * 2 ^ 59
def prefixEnd_6842558 : Nat := 4983230072969 + 3 ^ 40 * 6842558 * 2
def baseEnd_6842558 : Nat := 3513521160267544694056655

theorem tailTrace_6842558 : CollatzResearch.WordTrace tailWord_6842558 prefixEnd_6842558 3513521160267544694056655 := by
  unfold tailWord_6842558
  simp only [CollatzResearch.WordTrace]
  refine ⟨31196074143073557089156041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166379062096392304475498885 31196074143073557089156041)
  ·
    refine ⟨23397055607305167816867031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31196074143073557089156041 23397055607305167816867031)
    ·
      refine ⟨35095583410957751725300547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23397055607305167816867031 35095583410957751725300547)
      ·
        refine ⟨52643375116436627587950821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35095583410957751725300547 52643375116436627587950821)
        ·
          refine ⟨9870632834331867672740779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52643375116436627587950821 9870632834331867672740779)
          ·
            refine ⟨14805949251497801509111169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870632834331867672740779 14805949251497801509111169)
            ·
              refine ⟨11104461938623351131833377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14805949251497801509111169 11104461938623351131833377)
              ·
                refine ⟨8328346453967513348875033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11104461938623351131833377 8328346453967513348875033)
                ·
                  refine ⟨6246259840475635011656275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8328346453967513348875033 6246259840475635011656275)
                  ·
                    refine ⟨9369389760713452517484413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6246259840475635011656275 9369389760713452517484413)
                    ·
                      refine ⟨3513521160267544694056655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9369389760713452517484413 3513521160267544694056655)
                      ·
                        rfl

theorem cell23_6842558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_6842558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842558 prefixEnd_6842558 := by exact prefixLift 6842558
  have htrace : WordTrace (prefixWord ++ tailWord_6842558) baseStart_6842558 baseEnd_6842558 := by
    simpa [prefixWord, tailWord_6842558, baseEnd_6842558] using wordTrace_append hprefix tailTrace_6842558
  have hstable : (prefixWord ++ tailWord_6842558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842558).length < 2 ^ (prefixWord ++ tailWord_6842558).sum := by decide
  have hdescent : baseEnd_6842558 < baseStart_6842558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842604 : List Nat := [2, 2, 1, 1, 2, 3, 4, 3, 5]
def baseStart_6842604 : Nat := 118140960795 + 6842604 * 2 ^ 59
def prefixEnd_6842604 : Nat := 4983230072969 + 3 ^ 40 * 6842604 * 2
def baseEnd_6842604 : Nat := 390393864486405723786827

theorem tailTrace_6842604 : CollatzResearch.WordTrace tailWord_6842604 prefixEnd_6842604 390393864486405723786827 := by
  unfold tailWord_6842604
  simp only [CollatzResearch.WordTrace]
  refine ⟨124785135451210903284711433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166380180601614537712948577 124785135451210903284711433)
  ·
    refine ⟨93588851588408177463533575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124785135451210903284711433 93588851588408177463533575)
    ·
      refine ⟨140383277382612266195300363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93588851588408177463533575 140383277382612266195300363)
      ·
        refine ⟨210574916073918399292950545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140383277382612266195300363 210574916073918399292950545)
        ·
          refine ⟨157931187055438799469712909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210574916073918399292950545 157931187055438799469712909)
          ·
            refine ⟨59224195145789549801142341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157931187055438799469712909 59224195145789549801142341)
            ·
              refine ⟨11104536589835540587714189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59224195145789549801142341 11104536589835540587714189)
              ·
                refine ⟨4164201221188327720392821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11104536589835540587714189 4164201221188327720392821)
                ·
                  refine ⟨390393864486405723786827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4164201221188327720392821 390393864486405723786827)
                  ·
                    rfl

theorem cell23_6842604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_6842604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842604 prefixEnd_6842604 := by exact prefixLift 6842604
  have htrace : WordTrace (prefixWord ++ tailWord_6842604) baseStart_6842604 baseEnd_6842604 := by
    simpa [prefixWord, tailWord_6842604, baseEnd_6842604] using wordTrace_append hprefix tailTrace_6842604
  have hstable : (prefixWord ++ tailWord_6842604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842604).length < 2 ^ (prefixWord ++ tailWord_6842604).sum := by decide
  have hdescent : baseEnd_6842604 < baseStart_6842604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842614 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_6842614 : Nat := 118140960795 + 6842614 * 2 ^ 59
def prefixEnd_6842614 : Nat := 4983230072969 + 3 ^ 40 * 6842614 * 2
def baseEnd_6842614 : Nat := 3513549915184196474956397

theorem tailTrace_6842614 : CollatzResearch.WordTrace tailWord_6842614 prefixEnd_6842614 3513549915184196474956397 := by
  unfold tailWord_6842614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15598164727024098642330431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166380423754923718851524597 15598164727024098642330431)
  ·
    refine ⟨23397247090536147963495647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15598164727024098642330431 23397247090536147963495647)
    ·
      refine ⟨35095870635804221945243471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23397247090536147963495647 35095870635804221945243471)
      ·
        refine ⟨52643805953706332917865207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35095870635804221945243471 52643805953706332917865207)
        ·
          refine ⟨78965708930559499376797811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52643805953706332917865207 78965708930559499376797811)
          ·
            refine ⟨118448563395839249065196717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78965708930559499376797811 118448563395839249065196717)
            ·
              refine ⟨44418211273439718399448769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118448563395839249065196717 44418211273439718399448769)
              ·
                refine ⟨33313658455079788799586577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44418211273439718399448769 33313658455079788799586577)
                ·
                  refine ⟨24985243841309841599689933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33313658455079788799586577 24985243841309841599689933)
                  ·
                    refine ⟨9369466440491190599883725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24985243841309841599689933 9369466440491190599883725)
                    ·
                      refine ⟨3513549915184196474956397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9369466440491190599883725 3513549915184196474956397)
                      ·
                        rfl

theorem cell23_6842614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_6842614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842614 prefixEnd_6842614 := by exact prefixLift 6842614
  have htrace : WordTrace (prefixWord ++ tailWord_6842614) baseStart_6842614 baseEnd_6842614 := by
    simpa [prefixWord, tailWord_6842614, baseEnd_6842614] using wordTrace_append hprefix tailTrace_6842614
  have hstable : (prefixWord ++ tailWord_6842614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842614).length < 2 ^ (prefixWord ++ tailWord_6842614).sum := by decide
  have hdescent : baseEnd_6842614 < baseStart_6842614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842677 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 8]
def baseStart_6842677 : Nat := 118140960795 + 6842677 * 2 ^ 59
def prefixEnd_6842677 : Nat := 4983230072969 + 3 ^ 40 * 6842677 * 2
def baseEnd_6842677 : Nat := 390398029385047747607623

theorem tailTrace_6842677 : CollatzResearch.WordTrace tailWord_6842677 prefixEnd_6842677 390398029385047747607623 := by
  unfold tailWord_6842677
  simp only [CollatzResearch.WordTrace]
  refine ⟨249572933431157340036830285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166381955620771560024553523 249572933431157340036830285)
  ·
    refine ⟨93589850036684002513811357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249572933431157340036830285 93589850036684002513811357)
    ·
      refine ⟨35096193763756500942679259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93589850036684002513811357 35096193763756500942679259)
      ·
        refine ⟨52644290645634751414018889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35096193763756500942679259 52644290645634751414018889)
        ·
          refine ⟨39483217984226063560514167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52644290645634751414018889 39483217984226063560514167)
          ·
            refine ⟨59224826976339095340771251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39483217984226063560514167 59224826976339095340771251)
            ·
              refine ⟨88837240464508643011156877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59224826976339095340771251 88837240464508643011156877)
              ·
                refine ⟨33313965174190741129183829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88837240464508643011156877 33313965174190741129183829)
                ·
                  refine ⟨390398029385047747607623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33313965174190741129183829 390398029385047747607623)
                  ·
                    rfl

theorem cell23_6842677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_6842677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842677 prefixEnd_6842677 := by exact prefixLift 6842677
  have htrace : WordTrace (prefixWord ++ tailWord_6842677) baseStart_6842677 baseEnd_6842677 := by
    simpa [prefixWord, tailWord_6842677, baseEnd_6842677] using wordTrace_append hprefix tailTrace_6842677
  have hstable : (prefixWord ++ tailWord_6842677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842677).length < 2 ^ (prefixWord ++ tailWord_6842677).sum := by decide
  have hdescent : baseEnd_6842677 < baseStart_6842677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842681 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 3, 4]
def baseStart_6842681 : Nat := 118140960795 + 6842681 * 2 ^ 59
def prefixEnd_6842681 : Nat := 4983230072969 + 3 ^ 40 * 6842681 * 2
def baseEnd_6842681 : Nat := 1171194772796015904272863

theorem tailTrace_6842681 : CollatzResearch.WordTrace tailWord_6842681 prefixEnd_6842681 1171194772796015904272863 := by
  unfold tailWord_6842681
  simp only [CollatzResearch.WordTrace]
  refine ⟨249573079323142848719975897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166382052882095232479983931 249573079323142848719975897)
  ·
    refine ⟨187179809492357136539981923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249573079323142848719975897 187179809492357136539981923)
    ·
      refine ⟨280769714238535704809972885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187179809492357136539981923 280769714238535704809972885)
      ·
        refine ⟨13161080354931361162967479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280769714238535704809972885 13161080354931361162967479)
        ·
          refine ⟨19741620532397041744451219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13161080354931361162967479 19741620532397041744451219)
          ·
            refine ⟨29612430798595562616676829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19741620532397041744451219 29612430798595562616676829)
            ·
              refine ⟨11104661549473335981253811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29612430798595562616676829 11104661549473335981253811)
              ·
                refine ⟨16656992324210003971880717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11104661549473335981253811 16656992324210003971880717)
                ·
                  refine ⟨6246372121578751489455269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16656992324210003971880717 6246372121578751489455269)
                  ·
                    refine ⟨1171194772796015904272863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246372121578751489455269 1171194772796015904272863)
                    ·
                      rfl

theorem cell23_6842681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 3, 4].length) (baseStart_6842681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842681 prefixEnd_6842681 := by exact prefixLift 6842681
  have htrace : WordTrace (prefixWord ++ tailWord_6842681) baseStart_6842681 baseEnd_6842681 := by
    simpa [prefixWord, tailWord_6842681, baseEnd_6842681] using wordTrace_append hprefix tailTrace_6842681
  have hstable : (prefixWord ++ tailWord_6842681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842681).length < 2 ^ (prefixWord ++ tailWord_6842681).sum := by decide
  have hdescent : baseEnd_6842681 < baseStart_6842681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842732 : List Nat := [2, 2, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_6842732 : Nat := 118140960795 + 6842732 * 2 ^ 59
def prefixEnd_6842732 : Nat := 4983230072969 + 3 ^ 40 * 6842732 * 2
def baseEnd_6842732 : Nat := 1171203501967142337760285

theorem tailTrace_6842732 : CollatzResearch.WordTrace tailWord_6842732 prefixEnd_6842732 1171203501967142337760285 := by
  unfold tailWord_6842732
  simp only [CollatzResearch.WordTrace]
  refine ⟨124787469722979042215041225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166383292963972056286721633 124787469722979042215041225)
  ·
    refine ⟨93590602292234281661280919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124787469722979042215041225 93590602292234281661280919)
    ·
      refine ⟨140385903438351422491921379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93590602292234281661280919 140385903438351422491921379)
      ·
        refine ⟨210578855157527133737882069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140385903438351422491921379 210578855157527133737882069)
        ·
          refine ⟨4935441917754542196981611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 210578855157527133737882069 4935441917754542196981611)
          ·
            refine ⟨7403162876631813295472417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935441917754542196981611 7403162876631813295472417)
            ·
              refine ⟨5552372157473859971604313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7403162876631813295472417 5552372157473859971604313)
              ·
                refine ⟨4164279118105394978703235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5552372157473859971604313 4164279118105394978703235)
                ·
                  refine ⟨6246418677158092468054853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164279118105394978703235 6246418677158092468054853)
                  ·
                    refine ⟨1171203501967142337760285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246418677158092468054853 1171203501967142337760285)
                    ·
                      rfl

theorem cell23_6842732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_6842732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842732 prefixEnd_6842732 := by exact prefixLift 6842732
  have htrace : WordTrace (prefixWord ++ tailWord_6842732) baseStart_6842732 baseEnd_6842732 := by
    simpa [prefixWord, tailWord_6842732, baseEnd_6842732] using wordTrace_append hprefix tailTrace_6842732
  have hstable : (prefixWord ++ tailWord_6842732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842732).length < 2 ^ (prefixWord ++ tailWord_6842732).sum := by decide
  have hdescent : baseEnd_6842732 < baseStart_6842732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842737 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 5, 6]
def baseStart_6842737 : Nat := 118140960795 + 6842737 * 2 ^ 59
def prefixEnd_6842737 : Nat := 4983230072969 + 3 ^ 40 * 6842737 * 2
def baseEnd_6842737 : Nat := 1171204357768233164572777

theorem tailTrace_6842737 : CollatzResearch.WordTrace tailWord_6842737 prefixEnd_6842737 1171204357768233164572777 := by
  unfold tailWord_6842737
  simp only [CollatzResearch.WordTrace]
  refine ⟨249575121810939970284014465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166383414540626646856009643 249575121810939970284014465)
  ·
    refine ⟨187181341358204977713010849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249575121810939970284014465 187181341358204977713010849)
    ·
      refine ⟨140386006018653733284758137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187181341358204977713010849 140386006018653733284758137)
      ·
        refine ⟨105289504513990299963568603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140386006018653733284758137 105289504513990299963568603)
        ·
          refine ⟨157934256770985449945352905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105289504513990299963568603 157934256770985449945352905)
          ·
            refine ⟨118450692578239087459014679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157934256770985449945352905 118450692578239087459014679)
            ·
              refine ⟨177676038867358631188522019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118450692578239087459014679 177676038867358631188522019)
              ·
                refine ⟨266514058301037946782783029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177676038867358631188522019 266514058301037946782783029)
                ·
                  refine ⟨24985692965722307510885909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266514058301037946782783029 24985692965722307510885909)
                  ·
                    refine ⟨1171204357768233164572777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24985692965722307510885909 1171204357768233164572777)
                    ·
                      rfl

theorem cell23_6842737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_6842737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842737 prefixEnd_6842737 := by exact prefixLift 6842737
  have htrace : WordTrace (prefixWord ++ tailWord_6842737) baseStart_6842737 baseEnd_6842737 := by
    simpa [prefixWord, tailWord_6842737, baseEnd_6842737] using wordTrace_append hprefix tailTrace_6842737
  have hstable : (prefixWord ++ tailWord_6842737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842737).length < 2 ^ (prefixWord ++ tailWord_6842737).sum := by decide
  have hdescent : baseEnd_6842737 < baseStart_6842737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842772 : List Nat := [2, 4, 2, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_6842772 : Nat := 118140960795 + 6842772 * 2 ^ 59
def prefixEnd_6842772 : Nat := 4983230072969 + 3 ^ 40 * 6842772 * 2
def baseEnd_6842772 : Nat := 3513631045127606856780671

theorem tailTrace_6842772 : CollatzResearch.WordTrace tailWord_6842772 prefixEnd_6842772 3513631045127606856780671 := by
  unfold tailWord_6842772
  simp only [CollatzResearch.WordTrace]
  refine ⟨124788199182906585630769285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166384265577208780841025713 124788199182906585630769285)
  ·
    refine ⟨23397787346794984805769241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124788199182906585630769285 23397787346794984805769241)
    ·
      refine ⟨17548340510096238604326931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23397787346794984805769241 17548340510096238604326931)
      ·
        refine ⟨26322510765144357906490397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17548340510096238604326931 26322510765144357906490397)
        ·
          refine ⟨9870941536929134214933899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26322510765144357906490397 9870941536929134214933899)
          ·
            refine ⟨14806412305393701322400849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870941536929134214933899 14806412305393701322400849)
            ·
              refine ⟨11104809229045275991800637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14806412305393701322400849 11104809229045275991800637)
              ·
                refine ⟨4164303460891978496925239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11104809229045275991800637 4164303460891978496925239)
                ·
                  refine ⟨6246455191337967745387859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164303460891978496925239 6246455191337967745387859)
                  ·
                    refine ⟨9369682787006951618081789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6246455191337967745387859 9369682787006951618081789)
                    ·
                      refine ⟨3513631045127606856780671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9369682787006951618081789 3513631045127606856780671)
                      ·
                        rfl

theorem cell23_6842772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_6842772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842772 prefixEnd_6842772 := by exact prefixLift 6842772
  have htrace : WordTrace (prefixWord ++ tailWord_6842772) baseStart_6842772 baseEnd_6842772 := by
    simpa [prefixWord, tailWord_6842772, baseEnd_6842772] using wordTrace_append hprefix tailTrace_6842772
  have hstable : (prefixWord ++ tailWord_6842772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842772).length < 2 ^ (prefixWord ++ tailWord_6842772).sum := by decide
  have hdescent : baseEnd_6842772 < baseStart_6842772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842778 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4]
def baseStart_6842778 : Nat := 118140960795 + 6842778 * 2 ^ 59
def prefixEnd_6842778 : Nat := 4983230072969 + 3 ^ 40 * 6842778 * 2
def baseEnd_6842778 : Nat := 3513634126011533833305643

theorem tailTrace_6842778 : CollatzResearch.WordTrace tailWord_6842778 prefixEnd_6842778 3513634126011533833305643 := by
  unfold tailWord_6842778
  simp only [CollatzResearch.WordTrace]
  refine ⟨62394154300947858571564247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166384411469194289524171325 62394154300947858571564247)
  ·
    refine ⟨93591231451421787857346371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62394154300947858571564247 93591231451421787857346371)
    ·
      refine ⟨140386847177132681786019557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93591231451421787857346371 140386847177132681786019557)
      ·
        refine ⟨26322533845712377834878667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140386847177132681786019557 26322533845712377834878667)
        ·
          refine ⟨39483800768568566752318001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26322533845712377834878667 39483800768568566752318001)
          ·
            refine ⟨29612850576426425064238501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39483800768568566752318001 29612850576426425064238501)
            ·
              refine ⟨5552409483079954699544719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29612850576426425064238501 5552409483079954699544719)
              ·
                refine ⟨8328614224619932049317079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552409483079954699544719 8328614224619932049317079)
                ·
                  refine ⟨12492921336929898073975619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8328614224619932049317079 12492921336929898073975619)
                  ·
                    refine ⟨18739382005394847110963429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12492921336929898073975619 18739382005394847110963429)
                    ·
                      refine ⟨3513634126011533833305643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18739382005394847110963429 3513634126011533833305643)
                      ·
                        rfl

theorem cell23_6842778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_6842778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842778 prefixEnd_6842778 := by exact prefixLift 6842778
  have htrace : WordTrace (prefixWord ++ tailWord_6842778) baseStart_6842778 baseEnd_6842778 := by
    simpa [prefixWord, tailWord_6842778, baseEnd_6842778] using wordTrace_append hprefix tailTrace_6842778
  have hstable : (prefixWord ++ tailWord_6842778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842778).length < 2 ^ (prefixWord ++ tailWord_6842778).sum := by decide
  have hdescent : baseEnd_6842778 < baseStart_6842778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842805 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_6842805 : Nat := 118140960795 + 6842805 * 2 ^ 59
def prefixEnd_6842805 : Nat := 4983230072969 + 3 ^ 40 * 6842805 * 2
def baseEnd_6842805 : Nat := 1171215996663068409222673

theorem tailTrace_6842805 : CollatzResearch.WordTrace tailWord_6842805 prefixEnd_6842805 1171215996663068409222673 := by
  unfold tailWord_6842805
  simp only [CollatzResearch.WordTrace]
  refine ⟨249577601974693617897489869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166385067983129078598326579 249577601974693617897489869)
  ·
    refine ⟨93591600740510106711558701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249577601974693617897489869 93591600740510106711558701)
    ·
      refine ⟨35096850277691290016834513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93591600740510106711558701 35096850277691290016834513)
      ·
        refine ⟨26322637708268467512625885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35096850277691290016834513 26322637708268467512625885)
        ·
          refine ⟨9870989140600675317234707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26322637708268467512625885 9870989140600675317234707)
          ·
            refine ⟨14806483710901012975852061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9870989140600675317234707 14806483710901012975852061)
            ·
              refine ⟨5552431391587879865944523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14806483710901012975852061 5552431391587879865944523)
              ·
                refine ⟨8328647087381819798916785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552431391587879865944523 8328647087381819798916785)
                ·
                  refine ⟨6246485315536364849187589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8328647087381819798916785 6246485315536364849187589)
                  ·
                    refine ⟨1171215996663068409222673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246485315536364849187589 1171215996663068409222673)
                    ·
                      rfl

theorem cell23_6842805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_6842805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842805 prefixEnd_6842805 := by exact prefixLift 6842805
  have htrace : WordTrace (prefixWord ++ tailWord_6842805) baseStart_6842805 baseEnd_6842805 := by
    simpa [prefixWord, tailWord_6842805, baseEnd_6842805] using wordTrace_append hprefix tailTrace_6842805
  have hstable : (prefixWord ++ tailWord_6842805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842805).length < 2 ^ (prefixWord ++ tailWord_6842805).sum := by decide
  have hdescent : baseEnd_6842805 < baseStart_6842805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842814 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_6842814 : Nat := 118140960795 + 6842814 * 2 ^ 59
def prefixEnd_6842814 : Nat := 4983230072969 + 3 ^ 40 * 6842814 * 2
def baseEnd_6842814 : Nat := 1171217537105031897485159

theorem tailTrace_6842814 : CollatzResearch.WordTrace tailWord_6842814 prefixEnd_6842814 1171217537105031897485159 := by
  unfold tailWord_6842814
  simp only [CollatzResearch.WordTrace]
  refine ⟨31197241278957626554320937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166385286821107341623044997 31197241278957626554320937)
  ·
    refine ⟨23397930959218219915740703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31197241278957626554320937 23397930959218219915740703)
    ·
      refine ⟨35096896438827329873611055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23397930959218219915740703 35096896438827329873611055)
      ·
        refine ⟨52645344658240994810416583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35096896438827329873611055 52645344658240994810416583)
        ·
          refine ⟨78968016987361492215624875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52645344658240994810416583 78968016987361492215624875)
          ·
            refine ⟨118452025481042238323437313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78968016987361492215624875 118452025481042238323437313)
            ·
              refine ⟨88839019110781678742577985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118452025481042238323437313 88839019110781678742577985)
              ·
                refine ⟨66629264333086259056933489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88839019110781678742577985 66629264333086259056933489)
                ·
                  refine ⟨49971948249814694292700117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66629264333086259056933489 49971948249814694292700117)
                  ·
                    refine ⟨1171217537105031897485159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49971948249814694292700117 1171217537105031897485159)
                    ·
                      rfl

theorem cell23_6842814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_6842814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842814 prefixEnd_6842814 := by exact prefixLift 6842814
  have htrace : WordTrace (prefixWord ++ tailWord_6842814) baseStart_6842814 baseEnd_6842814 := by
    simpa [prefixWord, tailWord_6842814, baseEnd_6842814] using wordTrace_append hprefix tailTrace_6842814
  have hstable : (prefixWord ++ tailWord_6842814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842814).length < 2 ^ (prefixWord ++ tailWord_6842814).sum := by decide
  have hdescent : baseEnd_6842814 < baseStart_6842814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842824 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_6842824 : Nat := 118140960795 + 6842824 * 2 ^ 59
def prefixEnd_6842824 : Nat := 4983230072969 + 3 ^ 40 * 6842824 * 2
def baseEnd_6842824 : Nat := 3513657746121640653330431

theorem tailTrace_6842824 : CollatzResearch.WordTrace tailWord_6842824 prefixEnd_6842824 3513657746121640653330431 := by
  unfold tailWord_6842824
  simp only [CollatzResearch.WordTrace]
  refine ⟨124789147480812392071215763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166385529974416522761621017 124789147480812392071215763)
  ·
    refine ⟨187183721221218588106823645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124789147480812392071215763 187183721221218588106823645)
    ·
      refine ⟨70193895457956970540058867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187183721221218588106823645 70193895457956970540058867)
      ·
        refine ⟨105290843186935455810088301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70193895457956970540058867 105290843186935455810088301)
        ·
          refine ⟨39484066195100795928783113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105290843186935455810088301 39484066195100795928783113)
          ·
            refine ⟨29613049646325596946587335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39484066195100795928783113 29613049646325596946587335)
            ·
              refine ⟨44419574469488395419881003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29613049646325596946587335 44419574469488395419881003)
              ·
                refine ⟨66629361704232593129821505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44419574469488395419881003 66629361704232593129821505)
                ·
                  refine ⟨49972021278174444847366129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66629361704232593129821505 49972021278174444847366129)
                  ·
                    refine ⟨37479015958630833635524597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49972021278174444847366129 37479015958630833635524597)
                    ·
                      refine ⟨3513657746121640653330431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37479015958630833635524597 3513657746121640653330431)
                      ·
                        rfl

theorem cell23_6842824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_6842824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842824 prefixEnd_6842824 := by exact prefixLift 6842824
  have htrace : WordTrace (prefixWord ++ tailWord_6842824) baseStart_6842824 baseEnd_6842824 := by
    simpa [prefixWord, tailWord_6842824, baseEnd_6842824] using wordTrace_append hprefix tailTrace_6842824
  have hstable : (prefixWord ++ tailWord_6842824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842824).length < 2 ^ (prefixWord ++ tailWord_6842824).sum := by decide
  have hdescent : baseEnd_6842824 < baseStart_6842824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842862 : List Nat := [4, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3]
def baseStart_6842862 : Nat := 118140960795 + 6842862 * 2 ^ 59
def prefixEnd_6842862 : Nat := 4983230072969 + 3 ^ 40 * 6842862 * 2
def baseEnd_6842862 : Nat := 3513677258386511504655257

theorem tailTrace_6842862 : CollatzResearch.WordTrace tailWord_6842862 prefixEnd_6842862 3513677258386511504655257 := by
  unfold tailWord_6842862
  simp only [CollatzResearch.WordTrace]
  refine ⟨31197460116935889579039355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166386453956991411088209893 31197460116935889579039355)
  ·
    refine ⟨46796190175403834368559033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31197460116935889579039355 46796190175403834368559033)
    ·
      refine ⟨35097142631552875776419275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46796190175403834368559033 35097142631552875776419275)
      ·
        refine ⟨52645713947329313664628913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35097142631552875776419275 52645713947329313664628913)
        ·
          refine ⟨39484285460496985248471685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52645713947329313664628913 39484285460496985248471685)
          ·
            refine ⟨7403303523843184734088441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39484285460496985248471685 7403303523843184734088441)
            ·
              refine ⟨5552477642882388550566331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7403303523843184734088441 5552477642882388550566331)
              ·
                refine ⟨8328716464323582825849497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552477642882388550566331 8328716464323582825849497)
                ·
                  refine ⟨6246537348242687119387123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8328716464323582825849497 6246537348242687119387123)
                  ·
                    refine ⟨9369806022364030679080685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6246537348242687119387123 9369806022364030679080685)
                    ·
                      refine ⟨3513677258386511504655257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9369806022364030679080685 3513677258386511504655257)
                      ·
                        rfl

theorem cell23_6842862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_6842862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842862 prefixEnd_6842862 := by exact prefixLift 6842862
  have htrace : WordTrace (prefixWord ++ tailWord_6842862) baseStart_6842862 baseEnd_6842862 := by
    simpa [prefixWord, tailWord_6842862, baseEnd_6842862] using wordTrace_append hprefix tailTrace_6842862
  have hstable : (prefixWord ++ tailWord_6842862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842862).length < 2 ^ (prefixWord ++ tailWord_6842862).sum := by decide
  have hdescent : baseEnd_6842862 < baseStart_6842862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842864 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_6842864 : Nat := 118140960795 + 6842864 * 2 ^ 59
def prefixEnd_6842864 : Nat := 4983230072969 + 3 ^ 40 * 6842864 * 2
def baseEnd_6842864 : Nat := 3513678285347820496830247

theorem tailTrace_6842864 : CollatzResearch.WordTrace tailWord_6842864 prefixEnd_6842864 3513678285347820496830247 := by
  unfold tailWord_6842864
  simp only [CollatzResearch.WordTrace]
  refine ⟨124789876940739935486943823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166386502587653247315925097 124789876940739935486943823)
  ·
    refine ⟨187184815411109903230415735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124789876940739935486943823 187184815411109903230415735)
    ·
      refine ⟨280777223116664854845623603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187184815411109903230415735 280777223116664854845623603)
      ·
        refine ⟨421165834674997282268435405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280777223116664854845623603 421165834674997282268435405)
        ·
          refine ⟨157937188003123980850663277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421165834674997282268435405 157937188003123980850663277)
          ·
            refine ⟨59226445501171492818998729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157937188003123980850663277 59226445501171492818998729)
            ·
              refine ⟨44419834125878619614249047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59226445501171492818998729 44419834125878619614249047)
              ·
                refine ⟨66629751188817929421373571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44419834125878619614249047 66629751188817929421373571)
                ·
                  refine ⟨99944626783226894132060357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66629751188817929421373571 99944626783226894132060357)
                  ·
                    refine ⟨18739617521855042649761317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99944626783226894132060357 18739617521855042649761317)
                    ·
                      refine ⟨3513678285347820496830247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18739617521855042649761317 3513678285347820496830247)
                      ·
                        rfl

theorem cell23_6842864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_6842864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842864 prefixEnd_6842864 := by exact prefixLift 6842864
  have htrace : WordTrace (prefixWord ++ tailWord_6842864) baseStart_6842864 baseEnd_6842864 := by
    simpa [prefixWord, tailWord_6842864, baseEnd_6842864] using wordTrace_append hprefix tailTrace_6842864
  have hstable : (prefixWord ++ tailWord_6842864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842864).length < 2 ^ (prefixWord ++ tailWord_6842864).sum := by decide
  have hdescent : baseEnd_6842864 < baseStart_6842864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842901 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_6842901 : Nat := 118140960795 + 6842901 * 2 ^ 59
def prefixEnd_6842901 : Nat := 4983230072969 + 3 ^ 40 * 6842901 * 2
def baseEnd_6842901 : Nat := 3513697284132036852067577

theorem tailTrace_6842901 : CollatzResearch.WordTrace tailWord_6842901 prefixEnd_6842901 3513697284132036852067577 := by
  unfold tailWord_6842901
  simp only [CollatzResearch.WordTrace]
  refine ⟨249581103382345826292984557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166387402254897217528656371 249581103382345826292984557)
  ·
    refine ⟨93592913768379684859869209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249581103382345826292984557 93592913768379684859869209)
    ·
      refine ⟨70194685326284763644901907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93592913768379684859869209 70194685326284763644901907)
      ·
        refine ⟨105292027989427145467352861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70194685326284763644901907 105292027989427145467352861)
        ·
          refine ⟨39484510496035179550257323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105292027989427145467352861 39484510496035179550257323)
          ·
            refine ⟨59226765744052769325385985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39484510496035179550257323 59226765744052769325385985)
            ·
              refine ⟨44420074308039576994039489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59226765744052769325385985 44420074308039576994039489)
              ·
                refine ⟨33315055731029682745529617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44420074308039576994039489 33315055731029682745529617)
                ·
                  refine ⟨24986291798272262059147213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33315055731029682745529617 24986291798272262059147213)
                  ·
                    refine ⟨9369859424352098272180205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24986291798272262059147213 9369859424352098272180205)
                    ·
                      refine ⟨3513697284132036852067577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9369859424352098272180205 3513697284132036852067577)
                      ·
                        rfl

theorem cell23_6842901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_6842901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842901 prefixEnd_6842901 := by exact prefixLift 6842901
  have htrace : WordTrace (prefixWord ++ tailWord_6842901) baseStart_6842901 baseEnd_6842901 := by
    simpa [prefixWord, tailWord_6842901, baseEnd_6842901] using wordTrace_append hprefix tailTrace_6842901
  have hstable : (prefixWord ++ tailWord_6842901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842901).length < 2 ^ (prefixWord ++ tailWord_6842901).sum := by decide
  have hdescent : baseEnd_6842901 < baseStart_6842901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842908 : List Nat := [2, 2, 3, 1, 2, 3, 1, 4, 5]
def baseStart_6842908 : Nat := 118140960795 + 6842908 * 2 ^ 59
def prefixEnd_6842908 : Nat := 4983230072969 + 3 ^ 40 * 6842908 * 2
def baseEnd_6842908 : Nat := 390411208721846480520005

theorem tailTrace_6842908 : CollatzResearch.WordTrace tailWord_6842908 prefixEnd_6842908 390411208721846480520005 := by
  unfold tailWord_6842908
  simp only [CollatzResearch.WordTrace]
  refine ⟨124790679346660233244244689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166387572462213644325659585 124790679346660233244244689)
  ·
    refine ⟨93593009509995174933183517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124790679346660233244244689 93593009509995174933183517)
    ·
      refine ⟨35097378566248190599943819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93593009509995174933183517 35097378566248190599943819)
      ·
        refine ⟨52646067849372285899915729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35097378566248190599943819 52646067849372285899915729)
        ·
          refine ⟨39484550887029214424936797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52646067849372285899915729 39484550887029214424936797)
          ·
            refine ⟨14806706582635955409351299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39484550887029214424936797 14806706582635955409351299)
            ·
              refine ⟨22210059873953933114026949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14806706582635955409351299 22210059873953933114026949)
              ·
                refine ⟨4164386226366362458880053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22210059873953933114026949 4164386226366362458880053)
                ·
                  refine ⟨390411208721846480520005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4164386226366362458880053 390411208721846480520005)
                  ·
                    rfl

theorem cell23_6842908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_6842908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842908 prefixEnd_6842908 := by exact prefixLift 6842908
  have htrace : WordTrace (prefixWord ++ tailWord_6842908) baseStart_6842908 baseEnd_6842908 := by
    simpa [prefixWord, tailWord_6842908, baseEnd_6842908] using wordTrace_append hprefix tailTrace_6842908
  have hstable : (prefixWord ++ tailWord_6842908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842908).length < 2 ^ (prefixWord ++ tailWord_6842908).sum := by decide
  have hdescent : baseEnd_6842908 < baseStart_6842908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842938 : List Nat := [3, 1, 1, 1, 3, 5, 1, 1, 2, 5]
def baseStart_6842938 : Nat := 118140960795 + 6842938 * 2 ^ 59
def prefixEnd_6842938 : Nat := 4983230072969 + 3 ^ 40 * 6842938 * 2
def baseEnd_6842938 : Nat := 1171238760972084402434969

theorem tailTrace_6842938 : CollatzResearch.WordTrace tailWord_6842938 prefixEnd_6842938 1171238760972084402434969 := by
  unfold tailWord_6842938
  simp only [CollatzResearch.WordTrace]
  refine ⟨62395613220802945403020367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166388301922141187741387645 62395613220802945403020367)
  ·
    refine ⟨93593419831204418104530551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62395613220802945403020367 93593419831204418104530551)
    ·
      refine ⟨140390129746806627156795827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93593419831204418104530551 140390129746806627156795827)
      ·
        refine ⟨210585194620209940735193741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140390129746806627156795827 210585194620209940735193741)
        ·
          refine ⟨78969447982578727775697653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210585194620209940735193741 78969447982578727775697653)
          ·
            refine ⟨7403385748366755728971655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78969447982578727775697653 7403385748366755728971655)
            ·
              refine ⟨11105078622550133593457483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7403385748366755728971655 11105078622550133593457483)
              ·
                refine ⟨16657617933825200390186225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11105078622550133593457483 16657617933825200390186225)
                ·
                  refine ⟨12493213450368900292639669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16657617933825200390186225 12493213450368900292639669)
                  ·
                    refine ⟨1171238760972084402434969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12493213450368900292639669 1171238760972084402434969)
                    ·
                      rfl

theorem cell23_6842938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 1, 2, 5].length) (baseStart_6842938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842938 prefixEnd_6842938 := by exact prefixLift 6842938
  have htrace : WordTrace (prefixWord ++ tailWord_6842938) baseStart_6842938 baseEnd_6842938 := by
    simpa [prefixWord, tailWord_6842938, baseEnd_6842938] using wordTrace_append hprefix tailTrace_6842938
  have hstable : (prefixWord ++ tailWord_6842938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842938).length < 2 ^ (prefixWord ++ tailWord_6842938).sum := by decide
  have hdescent : baseEnd_6842938 < baseStart_6842938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842942 : List Nat := [4, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_6842942 : Nat := 118140960795 + 6842942 * 2 ^ 59
def prefixEnd_6842942 : Nat := 4983230072969 + 3 ^ 40 * 6842942 * 2
def baseEnd_6842942 : Nat := 390413148537652354628321

theorem tailTrace_6842942 : CollatzResearch.WordTrace tailWord_6842942 prefixEnd_6842942 390413148537652354628321 := by
  unfold tailWord_6842942
  simp only [CollatzResearch.WordTrace]
  refine ⟨31197824846899661286903385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166388399183464860196818053 31197824846899661286903385)
  ·
    refine ⟨23398368635174745965177539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31197824846899661286903385 23398368635174745965177539)
    ·
      refine ⟨35097552952762118947766309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23398368635174745965177539 35097552952762118947766309)
      ·
        refine ⟨6580791178642897302706183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35097552952762118947766309 6580791178642897302706183)
        ·
          refine ⟨9871186767964345954059275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6580791178642897302706183 9871186767964345954059275)
          ·
            refine ⟨14806780151946518931088913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9871186767964345954059275 14806780151946518931088913)
            ·
              refine ⟨11105085113959889198316685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14806780151946518931088913 11105085113959889198316685)
              ·
                refine ⟨4164406917734958449368757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11105085113959889198316685 4164406917734958449368757)
                ·
                  refine ⟨390413148537652354628321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4164406917734958449368757 390413148537652354628321)
                  ·
                    rfl

theorem cell23_6842942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_6842942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842942 prefixEnd_6842942 := by exact prefixLift 6842942
  have htrace : WordTrace (prefixWord ++ tailWord_6842942) baseStart_6842942 baseEnd_6842942 := by
    simpa [prefixWord, tailWord_6842942, baseEnd_6842942] using wordTrace_append hprefix tailTrace_6842942
  have hstable : (prefixWord ++ tailWord_6842942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842942).length < 2 ^ (prefixWord ++ tailWord_6842942).sum := by decide
  have hdescent : baseEnd_6842942 < baseStart_6842942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6842958 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2]
def baseStart_6842958 : Nat := 118140960795 + 6842958 * 2 ^ 59
def prefixEnd_6842958 : Nat := 4983230072969 + 3 ^ 40 * 6842958 * 2
def baseEnd_6842958 : Nat := 3513726552529343129054815

theorem tailTrace_6842958 : CollatzResearch.WordTrace tailWord_6842958 prefixEnd_6842958 3513726552529343129054815 := by
  unfold tailWord_6842958
  simp only [CollatzResearch.WordTrace]
  refine ⟨31197897792892415628476191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166388788228759550018539685 31197897792892415628476191)
  ·
    refine ⟨46796846689338623442714287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31197897792892415628476191 46796846689338623442714287)
    ·
      refine ⟨70195270034007935164071431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46796846689338623442714287 70195270034007935164071431)
      ·
        refine ⟨105292905051011902746107147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70195270034007935164071431 105292905051011902746107147)
        ·
          refine ⟨157939357576517854119160721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105292905051011902746107147 157939357576517854119160721)
          ·
            refine ⟨118454518182388390589370541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157939357576517854119160721 118454518182388390589370541)
            ·
              refine ⟨44420444318395646471013953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118454518182388390589370541 44420444318395646471013953)
              ·
                refine ⟨33315333238796734853260465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44420444318395646471013953 33315333238796734853260465)
                ·
                  refine ⟨24986499929097551139945349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33315333238796734853260465 24986499929097551139945349)
                  ·
                    refine ⟨4684968736705790838739753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24986499929097551139945349 4684968736705790838739753)
                    ·
                      refine ⟨3513726552529343129054815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4684968736705790838739753 3513726552529343129054815)
                      ·
                        rfl

theorem cell23_6842958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2].length) (baseStart_6842958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6842958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6842958 prefixEnd_6842958 := by exact prefixLift 6842958
  have htrace : WordTrace (prefixWord ++ tailWord_6842958) baseStart_6842958 baseEnd_6842958 := by
    simpa [prefixWord, tailWord_6842958, baseEnd_6842958] using wordTrace_append hprefix tailTrace_6842958
  have hstable : (prefixWord ++ tailWord_6842958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6842958).length < 2 ^ (prefixWord ++ tailWord_6842958).sum := by decide
  have hdescent : baseEnd_6842958 < baseStart_6842958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6842958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843076 : List Nat := [2, 3, 3, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_6843076 : Nat := 118140960795 + 6843076 * 2 ^ 59
def prefixEnd_6843076 : Nat := 4983230072969 + 3 ^ 40 * 6843076 * 2
def baseEnd_6843076 : Nat := 3513787143246573667379273

theorem tailTrace_6843076 : CollatzResearch.WordTrace tailWord_6843076 prefixEnd_6843076 3513787143246573667379273 := by
  unfold tailWord_6843076
  simp only [CollatzResearch.WordTrace]
  refine ⟨124793743078355915590302541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166391657437807887453736721 124793743078355915590302541)
  ·
    refine ⟨46797653654383468346363453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124793743078355915590302541 46797653654383468346363453)
    ·
      refine ⟨17549120120393800629886295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46797653654383468346363453 17549120120393800629886295)
      ·
        refine ⟨26323680180590700944829443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17549120120393800629886295 26323680180590700944829443)
        ·
          refine ⟨39485520270886051417244165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26323680180590700944829443 39485520270886051417244165)
          ·
            refine ⟨7403535050791134640733281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39485520270886051417244165 7403535050791134640733281)
            ·
              refine ⟨5552651288093350980549961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7403535050791134640733281 5552651288093350980549961)
              ·
                refine ⟨4164488466070013235412471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5552651288093350980549961 4164488466070013235412471)
                ·
                  refine ⟨6246732699105019853118707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164488466070013235412471 6246732699105019853118707)
                  ·
                    refine ⟨9370099048657529779678061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6246732699105019853118707 9370099048657529779678061)
                    ·
                      refine ⟨3513787143246573667379273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9370099048657529779678061 3513787143246573667379273)
                      ·
                        rfl

theorem cell23_6843076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_6843076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843076 prefixEnd_6843076 := by exact prefixLift 6843076
  have htrace : WordTrace (prefixWord ++ tailWord_6843076) baseStart_6843076 baseEnd_6843076 := by
    simpa [prefixWord, tailWord_6843076, baseEnd_6843076] using wordTrace_append hprefix tailTrace_6843076
  have hstable : (prefixWord ++ tailWord_6843076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843076).length < 2 ^ (prefixWord ++ tailWord_6843076).sum := by decide
  have hdescent : baseEnd_6843076 < baseStart_6843076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843132 : List Nat := [2, 2, 2, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_6843132 : Nat := 118140960795 + 6843132 * 2 ^ 59
def prefixEnd_6843132 : Nat := 4983230072969 + 3 ^ 40 * 6843132 * 2
def baseEnd_6843132 : Nat := 3513815898163225448279015

theorem tailTrace_6843132 : CollatzResearch.WordTrace tailWord_6843132 prefixEnd_6843132 3513815898163225448279015 := by
  unfold tailWord_6843132
  simp only [CollatzResearch.WordTrace]
  refine ⟨124794764322254476372321825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166393019096339301829762433 124794764322254476372321825)
  ·
    refine ⟨93596073241690857279241369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124794764322254476372321825 93596073241690857279241369)
    ·
      refine ⟨70197054931268142959431027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93596073241690857279241369 70197054931268142959431027)
      ·
        refine ⟨105295582396902214439146541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70197054931268142959431027 105295582396902214439146541)
        ·
          refine ⟨39485843398838330414679953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105295582396902214439146541 39485843398838330414679953)
          ·
            refine ⟨29614382549128747811009965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39485843398838330414679953 29614382549128747811009965)
            ·
              refine ⟨11105393455923280429128737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29614382549128747811009965 11105393455923280429128737)
              ·
                refine ⟨8329045091942460321846553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11105393455923280429128737 8329045091942460321846553)
                ·
                  refine ⟨6246783818956845241384915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8329045091942460321846553 6246783818956845241384915)
                  ·
                    refine ⟨9370175728435267862077373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6246783818956845241384915 9370175728435267862077373)
                    ·
                      refine ⟨3513815898163225448279015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9370175728435267862077373 3513815898163225448279015)
                      ·
                        rfl

theorem cell23_6843132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_6843132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843132 prefixEnd_6843132 := by exact prefixLift 6843132
  have htrace : WordTrace (prefixWord ++ tailWord_6843132) baseStart_6843132 baseEnd_6843132 := by
    simpa [prefixWord, tailWord_6843132, baseEnd_6843132] using wordTrace_append hprefix tailTrace_6843132
  have hstable : (prefixWord ++ tailWord_6843132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843132).length < 2 ^ (prefixWord ++ tailWord_6843132).sum := by decide
  have hdescent : baseEnd_6843132 < baseStart_6843132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843159 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 1, 3, 2]
def baseStart_6843159 : Nat := 118140960795 + 6843159 * 2 ^ 59
def prefixEnd_6843159 : Nat := 4983230072969 + 3 ^ 40 * 6843159 * 2
def baseEnd_6843159 : Nat := 3513829762140896842641391

theorem tailTrace_6843159 : CollatzResearch.WordTrace tailWord_6843159 prefixEnd_6843159 3513829762140896842641391 := by
  unfold tailWord_6843159
  simp only [CollatzResearch.WordTrace]
  refine ⟨249590513415411136355876531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166393675610274090903917687 249590513415411136355876531)
  ·
    refine ⟨374385770123116704533814797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249590513415411136355876531 374385770123116704533814797)
    ·
      refine ⟨140394663796168764200180549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374385770123116704533814797 140394663796168764200180549)
      ·
        refine ⟨26323999461781643287533853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140394663796168764200180549 26323999461781643287533853)
        ·
          refine ⟨9871499798168116232825195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26323999461781643287533853 9871499798168116232825195)
          ·
            refine ⟨14807249697252174349237793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9871499798168116232825195 14807249697252174349237793)
            ·
              refine ⟨11105437272939130761928345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14807249697252174349237793 11105437272939130761928345)
              ·
                refine ⟨8329077954704348071446259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11105437272939130761928345 8329077954704348071446259)
                ·
                  refine ⟨12493616932056522107169389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329077954704348071446259 12493616932056522107169389)
                  ·
                    refine ⟨4685106349521195790188521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12493616932056522107169389 4685106349521195790188521)
                    ·
                      refine ⟨3513829762140896842641391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685106349521195790188521 3513829762140896842641391)
                      ·
                        rfl

theorem cell23_6843159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_6843159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843159 prefixEnd_6843159 := by exact prefixLift 6843159
  have htrace : WordTrace (prefixWord ++ tailWord_6843159) baseStart_6843159 baseEnd_6843159 := by
    simpa [prefixWord, tailWord_6843159, baseEnd_6843159] using wordTrace_append hprefix tailTrace_6843159
  have hstable : (prefixWord ++ tailWord_6843159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843159).length < 2 ^ (prefixWord ++ tailWord_6843159).sum := by decide
  have hdescent : baseEnd_6843159 < baseStart_6843159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843161 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 9]
def baseStart_6843161 : Nat := 118140960795 + 6843161 * 2 ^ 59
def prefixEnd_6843161 : Nat := 4983230072969 + 3 ^ 40 * 6843161 * 2
def baseEnd_6843161 : Nat := 390425643233578426090709

theorem tailTrace_6843161 : CollatzResearch.WordTrace tailWord_6843161 prefixEnd_6843161 390425643233578426090709 := by
  unfold tailWord_6843161
  simp only [CollatzResearch.WordTrace]
  refine ⟨249590586361403890697449337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166393724240935927131632891 249590586361403890697449337)
  ·
    refine ⟨187192939771052918023087003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249590586361403890697449337 187192939771052918023087003)
    ·
      refine ⟨280789409656579377034630505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187192939771052918023087003 280789409656579377034630505)
      ·
        refine ⟨210592057242434532775972879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280789409656579377034630505 210592057242434532775972879)
        ·
          refine ⟨315888085863651799163959319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210592057242434532775972879 315888085863651799163959319)
          ·
            refine ⟨473832128795477698745938979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315888085863651799163959319 473832128795477698745938979)
            ·
              refine ⟨710748193193216548118908469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473832128795477698745938979 710748193193216548118908469)
              ·
                refine ⟨66632643111864051386147669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 710748193193216548118908469 66632643111864051386147669)
                ·
                  refine ⟨390425643233578426090709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66632643111864051386147669 390425643233578426090709)
                  ·
                    rfl

theorem cell23_6843161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_6843161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843161 prefixEnd_6843161 := by exact prefixLift 6843161
  have htrace : WordTrace (prefixWord ++ tailWord_6843161) baseStart_6843161 baseEnd_6843161 := by
    simpa [prefixWord, tailWord_6843161, baseEnd_6843161] using wordTrace_append hprefix tailTrace_6843161
  have hstable : (prefixWord ++ tailWord_6843161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843161).length < 2 ^ (prefixWord ++ tailWord_6843161).sum := by decide
  have hdescent : baseEnd_6843161 < baseStart_6843161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843208 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 4, 5]
def baseStart_6843208 : Nat := 118140960795 + 6843208 * 2 ^ 59
def prefixEnd_6843208 : Nat := 4983230072969 + 3 ^ 40 * 6843208 * 2
def baseEnd_6843208 : Nat := 1171284974230989050309555

theorem tailTrace_6843208 : CollatzResearch.WordTrace tailWord_6843208 prefixEnd_6843208 1171284974230989050309555 := by
  unfold tailWord_6843208
  simp only [CollatzResearch.WordTrace]
  refine ⟨124796150296116808862205139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166394867061489078482940185 124796150296116808862205139)
  ·
    refine ⟨187194225444175213293307709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124796150296116808862205139 187194225444175213293307709)
    ·
      refine ⟨70197834541565704984990391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187194225444175213293307709 70197834541565704984990391)
      ·
        refine ⟨105296751812348557477485587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70197834541565704984990391 105296751812348557477485587)
        ·
          refine ⟨157945127718522836216228381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105296751812348557477485587 157945127718522836216228381)
          ·
            refine ⟨59229422894446063581085643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157945127718522836216228381 59229422894446063581085643)
            ·
              refine ⟨88844134341669095371628465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59229422894446063581085643 88844134341669095371628465)
              ·
                refine ⟨66633100756251821528721349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88844134341669095371628465 66633100756251821528721349)
                ·
                  refine ⟨12493706391797216536635253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66633100756251821528721349 12493706391797216536635253)
                  ·
                    refine ⟨1171284974230989050309555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12493706391797216536635253 1171284974230989050309555)
                    ·
                      rfl

theorem cell23_6843208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_6843208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843208 prefixEnd_6843208 := by exact prefixLift 6843208
  have htrace : WordTrace (prefixWord ++ tailWord_6843208) baseStart_6843208 baseEnd_6843208 := by
    simpa [prefixWord, tailWord_6843208, baseEnd_6843208] using wordTrace_append hprefix tailTrace_6843208
  have hstable : (prefixWord ++ tailWord_6843208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843208).length < 2 ^ (prefixWord ++ tailWord_6843208).sum := by decide
  have hdescent : baseEnd_6843208 < baseStart_6843208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843218 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_6843218 : Nat := 118140960795 + 6843218 * 2 ^ 59
def prefixEnd_6843218 : Nat := 4983230072969 + 3 ^ 40 * 6843218 * 2
def baseEnd_6843218 : Nat := 3513860057499512111803619

theorem tailTrace_6843218 : CollatzResearch.WordTrace tailWord_6843218 prefixEnd_6843218 3513860057499512111803619 := by
  unfold tailWord_6843218
  simp only [CollatzResearch.WordTrace]
  refine ⟨62398166330549347358068577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166395110214798259621516205 62398166330549347358068577)
  ·
    refine ⟨46798624747912010518551433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62398166330549347358068577 46798624747912010518551433)
    ·
      refine ⟨35098968560934007888913575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46798624747912010518551433 35098968560934007888913575)
      ·
        refine ⟨52648452841401011833370363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35098968560934007888913575 52648452841401011833370363)
        ·
          refine ⟨78972679262101517750055545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52648452841401011833370363 78972679262101517750055545)
          ·
            refine ⟨59229509446576138312541659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78972679262101517750055545 59229509446576138312541659)
            ·
              refine ⟨88844264169864207468812489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59229509446576138312541659 88844264169864207468812489)
              ·
                refine ⟨66633198127398155601609367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88844264169864207468812489 66633198127398155601609367)
                ·
                  refine ⟨99949797191097233402414051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66633198127398155601609367 99949797191097233402414051)
                  ·
                    refine ⟨149924695786645850103621077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99949797191097233402414051 149924695786645850103621077)
                    ·
                      refine ⟨3513860057499512111803619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149924695786645850103621077 3513860057499512111803619)
                      ·
                        rfl

theorem cell23_6843218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_6843218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843218 prefixEnd_6843218 := by exact prefixLift 6843218
  have htrace : WordTrace (prefixWord ++ tailWord_6843218) baseStart_6843218 baseEnd_6843218 := by
    simpa [prefixWord, tailWord_6843218, baseEnd_6843218] using wordTrace_append hprefix tailTrace_6843218
  have hstable : (prefixWord ++ tailWord_6843218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843218).length < 2 ^ (prefixWord ++ tailWord_6843218).sum := by decide
  have hdescent : baseEnd_6843218 < baseStart_6843218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843225 : List Nat := [1, 2, 1, 2, 2, 5, 2, 1, 2, 5]
def baseStart_6843225 : Nat := 118140960795 + 6843225 * 2 ^ 59
def prefixEnd_6843225 : Nat := 4983230072969 + 3 ^ 40 * 6843225 * 2
def baseEnd_6843225 : Nat := 1171287883954697861472029

theorem tailTrace_6843225 : CollatzResearch.WordTrace tailWord_6843225 prefixEnd_6843225 1171287883954697861472029 := by
  unfold tailWord_6843225
  simp only [CollatzResearch.WordTrace]
  refine ⟨249592920633172029627779129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166395280422114686418519419 249592920633172029627779129)
  ·
    refine ⟨187194690474879022220834347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249592920633172029627779129 187194690474879022220834347)
    ·
      refine ⟨280792035712318533331251521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187194690474879022220834347 280792035712318533331251521)
      ·
        refine ⟨210594026784238899998438641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280792035712318533331251521 210594026784238899998438641)
        ·
          refine ⟨157945520088179174998828981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210594026784238899998438641 157945520088179174998828981)
          ·
            refine ⟨14807392508266797656140217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157945520088179174998828981 14807392508266797656140217)
            ·
              refine ⟨11105544381200098242105163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14807392508266797656140217 11105544381200098242105163)
              ·
                refine ⟨16658316571800147363157745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11105544381200098242105163 16658316571800147363157745)
                ·
                  refine ⟨12493737428850110522368309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16658316571800147363157745 12493737428850110522368309)
                  ·
                    refine ⟨1171287883954697861472029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12493737428850110522368309 1171287883954697861472029)
                    ·
                      rfl

theorem cell23_6843225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 5].length) (baseStart_6843225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843225 prefixEnd_6843225 := by exact prefixLift 6843225
  have htrace : WordTrace (prefixWord ++ tailWord_6843225) baseStart_6843225 baseEnd_6843225 := by
    simpa [prefixWord, tailWord_6843225, baseEnd_6843225] using wordTrace_append hprefix tailTrace_6843225
  have hstable : (prefixWord ++ tailWord_6843225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843225).length < 2 ^ (prefixWord ++ tailWord_6843225).sum := by decide
  have hdescent : baseEnd_6843225 < baseStart_6843225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843246 : List Nat := [4, 1, 2, 3, 2, 2, 2, 2, 5]
def baseStart_6843246 : Nat := 118140960795 + 6843246 * 2 ^ 59
def prefixEnd_6843246 : Nat := 4983230072969 + 3 ^ 40 * 6843246 * 2
def baseEnd_6843246 : Nat := 390430492773093111361499

theorem tailTrace_6843246 : CollatzResearch.WordTrace tailWord_6843246 prefixEnd_6843246 390430492773093111361499 := by
  unfold tailWord_6843246
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199210820761993776786699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166395791044063966809529061 31199210820761993776786699)
  ·
    refine ⟨46798816231142990665180049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31199210820761993776786699 46798816231142990665180049)
    ·
      refine ⟨35099112173357242998885037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46798816231142990665180049 35099112173357242998885037)
      ·
        refine ⟨13162167065008966124581889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35099112173357242998885037 13162167065008966124581889)
        ·
          refine ⟨9871625298756724593436417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13162167065008966124581889 9871625298756724593436417)
          ·
            refine ⟨7403718974067543445077313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9871625298756724593436417 7403718974067543445077313)
            ·
              refine ⟨5552789230550657583807985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7403718974067543445077313 5552789230550657583807985)
              ·
                refine ⟨4164591922912993187855989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5552789230550657583807985 4164591922912993187855989)
                ·
                  refine ⟨390430492773093111361499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4164591922912993187855989 390430492773093111361499)
                  ·
                    rfl

theorem cell23_6843246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_6843246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843246 prefixEnd_6843246 := by exact prefixLift 6843246
  have htrace : WordTrace (prefixWord ++ tailWord_6843246) baseStart_6843246 baseEnd_6843246 := by
    simpa [prefixWord, tailWord_6843246, baseEnd_6843246] using wordTrace_append hprefix tailTrace_6843246
  have hstable : (prefixWord ++ tailWord_6843246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843246).length < 2 ^ (prefixWord ++ tailWord_6843246).sum := by decide
  have hdescent : baseEnd_6843246 < baseStart_6843246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843258 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4]
def baseStart_6843258 : Nat := 118140960795 + 6843258 * 2 ^ 59
def prefixEnd_6843258 : Nat := 4983230072969 + 3 ^ 40 * 6843258 * 2
def baseEnd_6843258 : Nat := 3513880596725691955303435

theorem tailTrace_6843258 : CollatzResearch.WordTrace tailWord_6843258 prefixEnd_6843258 3513880596725691955303435 := by
  unfold tailWord_6843258
  simp only [CollatzResearch.WordTrace]
  refine ⟨62398531060513119065932607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166396082828034984175820285 62398531060513119065932607)
  ·
    refine ⟨93597796590769678598898911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62398531060513119065932607 93597796590769678598898911)
    ·
      refine ⟨140396694886154517898348367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93597796590769678598898911 140396694886154517898348367)
      ·
        refine ⟨210595042329231776847522551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140396694886154517898348367 210595042329231776847522551)
        ·
          refine ⟨315892563493847665271283827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210595042329231776847522551 315892563493847665271283827)
          ·
            refine ⟨473838845240771497906925741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315892563493847665271283827 473838845240771497906925741)
            ·
              refine ⟨177689566965289311715097153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473838845240771497906925741 177689566965289311715097153)
              ·
                refine ⟨133267175223966983786322865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177689566965289311715097153 133267175223966983786322865)
                ·
                  refine ⟨99950381417975237839742149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133267175223966983786322865 99950381417975237839742149)
                  ·
                    refine ⟨18740696515870357094951653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99950381417975237839742149 18740696515870357094951653)
                    ·
                      refine ⟨3513880596725691955303435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18740696515870357094951653 3513880596725691955303435)
                      ·
                        rfl

theorem cell23_6843258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_6843258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843258 prefixEnd_6843258 := by exact prefixLift 6843258
  have htrace : WordTrace (prefixWord ++ tailWord_6843258) baseStart_6843258 baseEnd_6843258 := by
    simpa [prefixWord, tailWord_6843258, baseEnd_6843258] using wordTrace_append hprefix tailTrace_6843258
  have hstable : (prefixWord ++ tailWord_6843258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843258).length < 2 ^ (prefixWord ++ tailWord_6843258).sum := by decide
  have hdescent : baseEnd_6843258 < baseStart_6843258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843268 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 10]
def baseStart_6843268 : Nat := 118140960795 + 6843268 * 2 ^ 59
def prefixEnd_6843268 : Nat := 4983230072969 + 3 ^ 40 * 6843268 * 2
def baseEnd_6843268 : Nat := 390431747948026324019821

theorem tailTrace_6843268 : CollatzResearch.WordTrace tailWord_6843268 prefixEnd_6843268 390431747948026324019821 := by
  unfold tailWord_6843268
  simp only [CollatzResearch.WordTrace]
  refine ⟨124797244486008123985797229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166396325981344165314396305 124797244486008123985797229)
  ·
    refine ⟨46798966682253046494673961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124797244486008123985797229 46798966682253046494673961)
    ·
      refine ⟨35099225011689784871005471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46798966682253046494673961 35099225011689784871005471)
      ·
        refine ⟨52648837517534677306508207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35099225011689784871005471 52648837517534677306508207)
        ·
          refine ⟨78973256276302015959762311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52648837517534677306508207 78973256276302015959762311)
          ·
            refine ⟨118459884414453023939643467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78973256276302015959762311 118459884414453023939643467)
            ·
              refine ⟨177689826621679535909465201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118459884414453023939643467 177689826621679535909465201)
              ·
                refine ⟨133267369966259651932098901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177689826621679535909465201 133267369966259651932098901)
                ·
                  refine ⟨390431747948026324019821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133267369966259651932098901 390431747948026324019821)
                  ·
                    rfl

theorem cell23_6843268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_6843268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843268 prefixEnd_6843268 := by exact prefixLift 6843268
  have htrace : WordTrace (prefixWord ++ tailWord_6843268) baseStart_6843268 baseEnd_6843268 := by
    simpa [prefixWord, tailWord_6843268, baseEnd_6843268] using wordTrace_append hprefix tailTrace_6843268
  have hstable : (prefixWord ++ tailWord_6843268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843268).length < 2 ^ (prefixWord ++ tailWord_6843268).sum := by decide
  have hdescent : baseEnd_6843268 < baseStart_6843268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843272 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 3, 4]
def baseStart_6843272 : Nat := 118140960795 + 6843272 * 2 ^ 59
def prefixEnd_6843272 : Nat := 4983230072969 + 3 ^ 40 * 6843272 * 2
def baseEnd_6843272 : Nat := 1171295928484951633509457

theorem tailTrace_6843272 : CollatzResearch.WordTrace tailWord_6843272 prefixEnd_6843272 1171295928484951633509457 := by
  unfold tailWord_6843272
  simp only [CollatzResearch.WordTrace]
  refine ⟨124797317432000878327370035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166396423242667837769826713 124797317432000878327370035)
  ·
    refine ⟨187195976148001317491055053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124797317432000878327370035 187195976148001317491055053)
    ·
      refine ⟨70198491055500494059145645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187195976148001317491055053 70198491055500494059145645)
      ·
        refine ⟨26324434145812685272179617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70198491055500494059145645 26324434145812685272179617)
        ·
          refine ⟨19743325609359513954134713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26324434145812685272179617 19743325609359513954134713)
          ·
            refine ⟨14807494207019635465601035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19743325609359513954134713 14807494207019635465601035)
            ·
              refine ⟨22211241310529453198401553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14807494207019635465601035 22211241310529453198401553)
              ·
                refine ⟨16658430982897089898801165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22211241310529453198401553 16658430982897089898801165)
                ·
                  refine ⟨6246911618586408712050437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16658430982897089898801165 6246911618586408712050437)
                  ·
                    refine ⟨1171295928484951633509457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246911618586408712050437 1171295928484951633509457)
                    ·
                      rfl

theorem cell23_6843272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_6843272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843272 prefixEnd_6843272 := by exact prefixLift 6843272
  have htrace : WordTrace (prefixWord ++ tailWord_6843272) baseStart_6843272 baseEnd_6843272 := by
    simpa [prefixWord, tailWord_6843272, baseEnd_6843272] using wordTrace_append hprefix tailTrace_6843272
  have hstable : (prefixWord ++ tailWord_6843272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843272).length < 2 ^ (prefixWord ++ tailWord_6843272).sum := by decide
  have hdescent : baseEnd_6843272 < baseStart_6843272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843308 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_6843308 : Nat := 118140960795 + 6843308 * 2 ^ 59
def prefixEnd_6843308 : Nat := 4983230072969 + 3 ^ 40 * 6843308 * 2
def baseEnd_6843308 : Nat := 3513906270758416759678205

theorem tailTrace_6843308 : CollatzResearch.WordTrace tailWord_6843308 prefixEnd_6843308 3513906270758416759678205 := by
  unfold tailWord_6843308
  simp only [CollatzResearch.WordTrace]
  refine ⟨124797973945935667401525289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166397298594580889868700385 124797973945935667401525289)
  ·
    refine ⟨93598480459451750551143967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124797973945935667401525289 93598480459451750551143967)
    ·
      refine ⟨140397720689177625826715951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93598480459451750551143967 140397720689177625826715951)
      ·
        refine ⟨210596581033766438740073927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140397720689177625826715951 210596581033766438740073927)
        ·
          refine ⟨315894871550649658110110891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210596581033766438740073927 315894871550649658110110891)
          ·
            refine ⟨473842307325974487165166337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315894871550649658110110891 473842307325974487165166337)
            ·
              refine ⟨355381730494480865373874753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473842307325974487165166337 355381730494480865373874753)
              ·
                refine ⟨266536297870860649030406065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355381730494480865373874753 266536297870860649030406065)
                ·
                  refine ⟨199902223403145486772804549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266536297870860649030406065 199902223403145486772804549)
                  ·
                    refine ⟨37481666888089778769900853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199902223403145486772804549 37481666888089778769900853)
                    ·
                      refine ⟨3513906270758416759678205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37481666888089778769900853 3513906270758416759678205)
                      ·
                        rfl

theorem cell23_6843308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_6843308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843308 prefixEnd_6843308 := by exact prefixLift 6843308
  have htrace : WordTrace (prefixWord ++ tailWord_6843308) baseStart_6843308 baseEnd_6843308 := by
    simpa [prefixWord, tailWord_6843308, baseEnd_6843308] using wordTrace_append hprefix tailTrace_6843308
  have hstable : (prefixWord ++ tailWord_6843308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843308).length < 2 ^ (prefixWord ++ tailWord_6843308).sum := by decide
  have hdescent : baseEnd_6843308 < baseStart_6843308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843335 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_6843335 : Nat := 118140960795 + 6843335 * 2 ^ 59
def prefixEnd_6843335 : Nat := 4983230072969 + 3 ^ 40 * 6843335 * 2
def baseEnd_6843335 : Nat := 3513920134736088154040581

theorem tailTrace_6843335 : CollatzResearch.WordTrace tailWord_6843335 prefixEnd_6843335 3513920134736088154040581 := by
  unfold tailWord_6843335
  simp only [CollatzResearch.WordTrace]
  refine ⟨249596932662773518414283459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166397955108515678942855639 249596932662773518414283459)
  ·
    refine ⟨374395398994160277621425189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249596932662773518414283459 374395398994160277621425189)
    ·
      refine ⟨70199137311405052054017223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374395398994160277621425189 70199137311405052054017223)
      ·
        refine ⟨105298705967107578081025835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70199137311405052054017223 105298705967107578081025835)
        ·
          refine ⟨157948058950661367121538753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105298705967107578081025835 157948058950661367121538753)
          ·
            refine ⟨118461044212996025341154065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157948058950661367121538753 118461044212996025341154065)
            ·
              refine ⟨88845783159747019005865549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118461044212996025341154065 88845783159747019005865549)
              ·
                refine ⟨33317168684905132127199581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88845783159747019005865549 33317168684905132127199581)
                ·
                  refine ⟨12493938256839424547699843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33317168684905132127199581 12493938256839424547699843)
                  ·
                    refine ⟨18740907385259136821549765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12493938256839424547699843 18740907385259136821549765)
                    ·
                      refine ⟨3513920134736088154040581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18740907385259136821549765 3513920134736088154040581)
                      ·
                        rfl

theorem cell23_6843335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_6843335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843335 prefixEnd_6843335 := by exact prefixLift 6843335
  have htrace : WordTrace (prefixWord ++ tailWord_6843335) baseStart_6843335 baseEnd_6843335 := by
    simpa [prefixWord, tailWord_6843335, baseEnd_6843335] using wordTrace_append hprefix tailTrace_6843335
  have hstable : (prefixWord ++ tailWord_6843335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843335).length < 2 ^ (prefixWord ++ tailWord_6843335).sum := by decide
  have hdescent : baseEnd_6843335 < baseStart_6843335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843345 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 6, 4]
def baseStart_6843345 : Nat := 118140960795 + 6843345 * 2 ^ 59
def prefixEnd_6843345 : Nat := 4983230072969 + 3 ^ 40 * 6843345 * 2
def baseEnd_6843345 : Nat := 1171308423180877704971845

theorem tailTrace_6843345 : CollatzResearch.WordTrace tailWord_6843345 prefixEnd_6843345 1171308423180877704971845 := by
  unfold tailWord_6843345
  simp only [CollatzResearch.WordTrace]
  refine ⟨249597297392737290122147489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166398198261824860081431659 249597297392737290122147489)
  ·
    refine ⟨187197973044552967591610617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249597297392737290122147489 187197973044552967591610617)
    ·
      refine ⟨140398479783414725693707963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187197973044552967591610617 140398479783414725693707963)
      ·
        refine ⟨210597719675122088540561945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140398479783414725693707963 210597719675122088540561945)
        ·
          refine ⟨157948289756341566405421459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210597719675122088540561945 157948289756341566405421459)
          ·
            refine ⟨236922434634512349608132189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157948289756341566405421459 236922434634512349608132189)
            ·
              refine ⟨88845912987942131103049571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236922434634512349608132189 88845912987942131103049571)
              ·
                refine ⟨133268869481913196654574357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88845912987942131103049571 133268869481913196654574357)
                ·
                  refine ⟨6246978256964681093183173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133268869481913196654574357 6246978256964681093183173)
                  ·
                    refine ⟨1171308423180877704971845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246978256964681093183173 1171308423180877704971845)
                    ·
                      rfl

theorem cell23_6843345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_6843345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843345 prefixEnd_6843345 := by exact prefixLift 6843345
  have htrace : WordTrace (prefixWord ++ tailWord_6843345) baseStart_6843345 baseEnd_6843345 := by
    simpa [prefixWord, tailWord_6843345, baseEnd_6843345] using wordTrace_append hprefix tailTrace_6843345
  have hstable : (prefixWord ++ tailWord_6843345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843345).length < 2 ^ (prefixWord ++ tailWord_6843345).sum := by decide
  have hdescent : baseEnd_6843345 < baseStart_6843345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843352 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_6843352 : Nat := 118140960795 + 6843352 * 2 ^ 59
def prefixEnd_6843352 : Nat := 4983230072969 + 3 ^ 40 * 6843352 * 2
def baseEnd_6843352 : Nat := 3513928863907214587528003

theorem tailTrace_6843352 : CollatzResearch.WordTrace tailWord_6843352 prefixEnd_6843352 3513928863907214587528003 := by
  unfold tailWord_6843352
  simp only [CollatzResearch.WordTrace]
  refine ⟨124798776351855965158826155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166398368469141286878434873 124798776351855965158826155)
  ·
    refine ⟨187198164527783947738239233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124798776351855965158826155 187198164527783947738239233)
    ·
      refine ⟨140398623395837960803679425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187198164527783947738239233 140398623395837960803679425)
      ·
        refine ⟨105298967546878470602759569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140398623395837960803679425 105298967546878470602759569)
        ·
          refine ⟨78974225660158852952069677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105298967546878470602759569 78974225660158852952069677)
          ·
            refine ⟨29615334622559569857026129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78974225660158852952069677 29615334622559569857026129)
            ·
              refine ⟨22211500966919677392769597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29615334622559569857026129 22211500966919677392769597)
              ·
                refine ⟨8329312862594879022288599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22211500966919677392769597 8329312862594879022288599)
                ·
                  refine ⟨12493969293892318533432899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329312862594879022288599 12493969293892318533432899)
                  ·
                    refine ⟨18740953940838477800149349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12493969293892318533432899 18740953940838477800149349)
                    ·
                      refine ⟨3513928863907214587528003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18740953940838477800149349 3513928863907214587528003)
                      ·
                        rfl

theorem cell23_6843352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_6843352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843352 prefixEnd_6843352 := by exact prefixLift 6843352
  have htrace : WordTrace (prefixWord ++ tailWord_6843352) baseStart_6843352 baseEnd_6843352 := by
    simpa [prefixWord, tailWord_6843352, baseEnd_6843352] using wordTrace_append hprefix tailTrace_6843352
  have hstable : (prefixWord ++ tailWord_6843352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843352).length < 2 ^ (prefixWord ++ tailWord_6843352).sum := by decide
  have hdescent : baseEnd_6843352 < baseStart_6843352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843375 : List Nat := [1, 1, 2, 1, 4, 4, 2, 8]
def baseStart_6843375 : Nat := 118140960795 + 6843375 * 2 ^ 59
def prefixEnd_6843375 : Nat := 4983230072969 + 3 ^ 40 * 6843375 * 2
def baseEnd_6843375 : Nat := 130145950887491407316311

theorem tailTrace_6843375 : CollatzResearch.WordTrace tailWord_6843375 prefixEnd_6843375 130145950887491407316311 := by
  unfold tailWord_6843375
  simp only [CollatzResearch.WordTrace]
  refine ⟨249598391582628605245739579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166398927721752403497159719 249598391582628605245739579)
  ·
    refine ⟨374397587373942907868609369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249598391582628605245739579 374397587373942907868609369)
    ·
      refine ⟨280798190530457180901457027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374397587373942907868609369 280798190530457180901457027)
      ·
        refine ⟨421197285795685771352185541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280798190530457180901457027 421197285795685771352185541)
        ·
          refine ⟨78974491086691082128534789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421197285795685771352185541 78974491086691082128534789)
          ·
            refine ⟨14807717078754577899100273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78974491086691082128534789 14807717078754577899100273)
            ·
              refine ⟨11105787809065933424325205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14807717078754577899100273 11105787809065933424325205)
              ·
                refine ⟨130145950887491407316311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11105787809065933424325205 130145950887491407316311)
                ·
                  rfl

theorem cell23_6843375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 8].length) (baseStart_6843375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843375 prefixEnd_6843375 := by exact prefixLift 6843375
  have htrace : WordTrace (prefixWord ++ tailWord_6843375) baseStart_6843375 baseEnd_6843375 := by
    simpa [prefixWord, tailWord_6843375, baseEnd_6843375] using wordTrace_append hprefix tailTrace_6843375
  have hstable : (prefixWord ++ tailWord_6843375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843375).length < 2 ^ (prefixWord ++ tailWord_6843375).sum := by decide
  have hdescent : baseEnd_6843375 < baseStart_6843375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843382 : List Nat := [5, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6843382 : Nat := 118140960795 + 6843382 * 2 ^ 59
def prefixEnd_6843382 : Nat := 4983230072969 + 3 ^ 40 * 6843382 * 2
def baseEnd_6843382 : Nat := 3513944268326849470152865

theorem tailTrace_6843382 : CollatzResearch.WordTrace tailWord_6843382 prefixEnd_6843382 3513944268326849470152865 := by
  unfold tailWord_6843382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599915430850202840077775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166399097929068830294162933 15599915430850202840077775)
  ·
    refine ⟨23399873146275304260116663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15599915430850202840077775 23399873146275304260116663)
    ·
      refine ⟨35099809719412956390174995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23399873146275304260116663 35099809719412956390174995)
      ·
        refine ⟨52649714579119434585262493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35099809719412956390174995 52649714579119434585262493)
        ·
          refine ⟨19743642967169787969473435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52649714579119434585262493 19743642967169787969473435)
          ·
            refine ⟨29615464450754681954210153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19743642967169787969473435 29615464450754681954210153)
            ·
              refine ⟨22211598338066011465657615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29615464450754681954210153 22211598338066011465657615)
              ·
                refine ⟨33317397507099017198486423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22211598338066011465657615 33317397507099017198486423)
                ·
                  refine ⟨49976096260648525797729635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33317397507099017198486423 49976096260648525797729635)
                  ·
                    refine ⟨74964144390972788696594453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49976096260648525797729635 74964144390972788696594453)
                    ·
                      refine ⟨3513944268326849470152865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74964144390972788696594453 3513944268326849470152865)
                      ·
                        rfl

theorem cell23_6843382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6843382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843382 prefixEnd_6843382 := by exact prefixLift 6843382
  have htrace : WordTrace (prefixWord ++ tailWord_6843382) baseStart_6843382 baseEnd_6843382 := by
    simpa [prefixWord, tailWord_6843382, baseEnd_6843382] using wordTrace_append hprefix tailTrace_6843382
  have hstable : (prefixWord ++ tailWord_6843382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843382).length < 2 ^ (prefixWord ++ tailWord_6843382).sum := by decide
  have hdescent : baseEnd_6843382 < baseStart_6843382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843402 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3]
def baseStart_6843402 : Nat := 118140960795 + 6843402 * 2 ^ 59
def prefixEnd_6843402 : Nat := 4983230072969 + 3 ^ 40 * 6843402 * 2
def baseEnd_6843402 : Nat := 3513954537939939391902773

theorem tailTrace_6843402 : CollatzResearch.WordTrace tailWord_6843402 prefixEnd_6843402 3513954537939939391902773 := by
  unfold tailWord_6843402
  simp only [CollatzResearch.WordTrace]
  refine ⟨62399844088382697214243115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166399584235687192571314973 62399844088382697214243115)
  ·
    refine ⟨93599766132574045821364673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62399844088382697214243115 93599766132574045821364673)
    ·
      refine ⟨70199824599430534366023505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93599766132574045821364673 70199824599430534366023505)
      ·
        refine ⟨52649868449572900774517629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70199824599430534366023505 52649868449572900774517629)
        ·
          refine ⟨19743700668589837790444111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52649868449572900774517629 19743700668589837790444111)
          ·
            refine ⟨29615551002884756685666167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19743700668589837790444111 29615551002884756685666167)
            ·
              refine ⟨44423326504327135028499251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29615551002884756685666167 44423326504327135028499251)
              ·
                refine ⟨66634989756490702542748877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44423326504327135028499251 66634989756490702542748877)
                ·
                  refine ⟨24988121158684013453530829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66634989756490702542748877 24988121158684013453530829)
                  ·
                    refine ⟨9370545434506505045074061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24988121158684013453530829 9370545434506505045074061)
                    ·
                      refine ⟨3513954537939939391902773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9370545434506505045074061 3513954537939939391902773)
                      ·
                        rfl

theorem cell23_6843402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_6843402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843402 prefixEnd_6843402 := by exact prefixLift 6843402
  have htrace : WordTrace (prefixWord ++ tailWord_6843402) baseStart_6843402 baseEnd_6843402 := by
    simpa [prefixWord, tailWord_6843402, baseEnd_6843402] using wordTrace_append hprefix tailTrace_6843402
  have hstable : (prefixWord ++ tailWord_6843402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843402).length < 2 ^ (prefixWord ++ tailWord_6843402).sum := by decide
  have hdescent : baseEnd_6843402 < baseStart_6843402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843406 : List Nat := [4, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3]
def baseStart_6843406 : Nat := 118140960795 + 6843406 * 2 ^ 59
def prefixEnd_6843406 : Nat := 4983230072969 + 3 ^ 40 * 6843406 * 2
def baseEnd_6843406 : Nat := 3513956591862557376252755

theorem tailTrace_6843406 : CollatzResearch.WordTrace tailWord_6843406 prefixEnd_6843406 3513956591862557376252755 := by
  unfold tailWord_6843406
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199940280689537192514759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166399681497010865026745381 31199940280689537192514759)
  ·
    refine ⟨46799910421034305788772139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31199940280689537192514759 46799910421034305788772139)
    ·
      refine ⟨70199865631551458683158209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46799910421034305788772139 70199865631551458683158209)
      ·
        refine ⟨52649899223663594012368657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70199865631551458683158209 52649899223663594012368657)
        ·
          refine ⟨39487424417747695509276493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52649899223663594012368657 39487424417747695509276493)
          ·
            refine ⟨14807784156655385815978685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39487424417747695509276493 14807784156655385815978685)
            ·
              refine ⟨5552919058745769680992007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14807784156655385815978685 5552919058745769680992007)
              ·
                refine ⟨8329378588118654521488011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552919058745769680992007 8329378588118654521488011)
                ·
                  refine ⟨12494067882177981782232017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329378588118654521488011 12494067882177981782232017)
                  ·
                    refine ⟨9370550911633486336674013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12494067882177981782232017 9370550911633486336674013)
                    ·
                      refine ⟨3513956591862557376252755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9370550911633486336674013 3513956591862557376252755)
                      ·
                        rfl

theorem cell23_6843406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3].length) (baseStart_6843406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843406 prefixEnd_6843406 := by exact prefixLift 6843406
  have htrace : WordTrace (prefixWord ++ tailWord_6843406) baseStart_6843406 baseEnd_6843406 := by
    simpa [prefixWord, tailWord_6843406, baseEnd_6843406] using wordTrace_append hprefix tailTrace_6843406
  have hstable : (prefixWord ++ tailWord_6843406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843406).length < 2 ^ (prefixWord ++ tailWord_6843406).sum := by decide
  have hdescent : baseEnd_6843406 < baseStart_6843406 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843435 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 2, 6]
def baseStart_6843435 : Nat := 118140960795 + 6843435 * 2 ^ 59
def prefixEnd_6843435 : Nat := 4983230072969 + 3 ^ 40 * 6843435 * 2
def baseEnd_6843435 : Nat := 1171323827600512587596707

theorem tailTrace_6843435 : CollatzResearch.WordTrace tailWord_6843435 prefixEnd_6843435 1171323827600512587596707 := by
  unfold tailWord_6843435
  simp only [CollatzResearch.WordTrace]
  refine ⟨249600579962411235492923759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166400386641607490328615839 249600579962411235492923759)
  ·
    refine ⟨374400869943616853239385639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249600579962411235492923759 374400869943616853239385639)
    ·
      refine ⟨561601304915425279859078459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374400869943616853239385639 561601304915425279859078459)
      ·
        refine ⟨842401957373137919788617689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561601304915425279859078459 842401957373137919788617689)
        ·
          refine ⟨631801468029853439841463267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 842401957373137919788617689 631801468029853439841463267)
          ·
            refine ⟨947702202044780159762194901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631801468029853439841463267 947702202044780159762194901)
            ·
              refine ⟨22211770360424534994426443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 947702202044780159762194901 22211770360424534994426443)
              ·
                refine ⟨33317655540636802491639665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22211770360424534994426443 33317655540636802491639665)
                ·
                  refine ⟨24988241655477601868729749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33317655540636802491639665 24988241655477601868729749)
                  ·
                    refine ⟨1171323827600512587596707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24988241655477601868729749 1171323827600512587596707)
                    ·
                      rfl

theorem cell23_6843435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 6].length) (baseStart_6843435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843435 prefixEnd_6843435 := by exact prefixLift 6843435
  have htrace : WordTrace (prefixWord ++ tailWord_6843435) baseStart_6843435 baseEnd_6843435 := by
    simpa [prefixWord, tailWord_6843435, baseEnd_6843435] using wordTrace_append hprefix tailTrace_6843435
  have hstable : (prefixWord ++ tailWord_6843435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843435).length < 2 ^ (prefixWord ++ tailWord_6843435).sum := by decide
  have hdescent : baseEnd_6843435 < baseStart_6843435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843446 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_6843446 : Nat := 118140960795 + 6843446 * 2 ^ 59
def prefixEnd_6843446 : Nat := 4983230072969 + 3 ^ 40 * 6843446 * 2
def baseEnd_6843446 : Nat := 3513977131088737219752571

theorem tailTrace_6843446 : CollatzResearch.WordTrace tailWord_6843446 prefixEnd_6843446 3513977131088737219752571 := by
  unfold tailWord_6843446
  simp only [CollatzResearch.WordTrace]
  refine ⟨15600061322835711523223387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166400654110247589581049461 15600061322835711523223387)
  ·
    refine ⟨23400091984253567284835081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15600061322835711523223387 23400091984253567284835081)
    ·
      refine ⟨17550068988190175463626311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23400091984253567284835081 17550068988190175463626311)
      ·
        refine ⟨26325103482285263195439467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17550068988190175463626311 26325103482285263195439467)
        ·
          refine ⟨39487655223427894793159201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26325103482285263195439467 39487655223427894793159201)
          ·
            refine ⟨29615741417570921094869401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39487655223427894793159201 29615741417570921094869401)
            ·
              refine ⟨22211806063178190821152051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29615741417570921094869401 22211806063178190821152051)
              ·
                refine ⟨33317709094767286231728077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22211806063178190821152051 33317709094767286231728077)
                ·
                  refine ⟨12494140910537732336898029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33317709094767286231728077 12494140910537732336898029)
                  ·
                    refine ⟨4685302841451649626336761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12494140910537732336898029 4685302841451649626336761)
                    ·
                      refine ⟨3513977131088737219752571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685302841451649626336761 3513977131088737219752571)
                      ·
                        rfl

theorem cell23_6843446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_6843446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843446 prefixEnd_6843446 := by exact prefixLift 6843446
  have htrace : WordTrace (prefixWord ++ tailWord_6843446) baseStart_6843446 baseEnd_6843446 := by
    simpa [prefixWord, tailWord_6843446, baseEnd_6843446] using wordTrace_append hprefix tailTrace_6843446
  have hstable : (prefixWord ++ tailWord_6843446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843446).length < 2 ^ (prefixWord ++ tailWord_6843446).sum := by decide
  have hdescent : baseEnd_6843446 < baseStart_6843446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843455 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_6843455 : Nat := 118140960795 + 6843455 * 2 ^ 59
def prefixEnd_6843455 : Nat := 4983230072969 + 3 ^ 40 * 6843455 * 2
def baseEnd_6843455 : Nat := 3513981752414627684540029

theorem tailTrace_6843455 : CollatzResearch.WordTrace tailWord_6843455 prefixEnd_6843455 3513981752414627684540029 := by
  unfold tailWord_6843455
  simp only [CollatzResearch.WordTrace]
  refine ⟨249601309422338778908651819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166400872948225852605767879 249601309422338778908651819)
  ·
    refine ⟨374401964133508168362977729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249601309422338778908651819 374401964133508168362977729)
    ·
      refine ⟨280801473100131126272233297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374401964133508168362977729 280801473100131126272233297)
      ·
        refine ⟨210601104825098344704174973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280801473100131126272233297 210601104825098344704174973)
        ·
          refine ⟨78975414309411879264065615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210601104825098344704174973 78975414309411879264065615)
          ·
            refine ⟨118463121464117818896098423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78975414309411879264065615 118463121464117818896098423)
            ·
              refine ⟨177694682196176728344147635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118463121464117818896098423 177694682196176728344147635)
              ·
                refine ⟨266542023294265092516221453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177694682196176728344147635 266542023294265092516221453)
                ·
                  refine ⟨99953258735349409693583045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266542023294265092516221453 99953258735349409693583045)
                  ·
                    refine ⟨18741236012878014317546821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99953258735349409693583045 18741236012878014317546821)
                    ·
                      refine ⟨3513981752414627684540029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18741236012878014317546821 3513981752414627684540029)
                      ·
                        rfl

theorem cell23_6843455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_6843455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843455 prefixEnd_6843455 := by exact prefixLift 6843455
  have htrace : WordTrace (prefixWord ++ tailWord_6843455) baseStart_6843455 baseEnd_6843455 := by
    simpa [prefixWord, tailWord_6843455, baseEnd_6843455] using wordTrace_append hprefix tailTrace_6843455
  have hstable : (prefixWord ++ tailWord_6843455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843455).length < 2 ^ (prefixWord ++ tailWord_6843455).sum := by decide
  have hdescent : baseEnd_6843455 < baseStart_6843455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843459 : List Nat := [1, 1, 1, 3, 1, 2, 4, 2, 4, 2, 2]
def baseStart_6843459 : Nat := 118140960795 + 6843459 * 2 ^ 59
def prefixEnd_6843459 : Nat := 4983230072969 + 3 ^ 40 * 6843459 * 2
def baseEnd_6843459 : Nat := 3513983806337245668890011

theorem tailTrace_6843459 : CollatzResearch.WordTrace tailWord_6843459 prefixEnd_6843459 3513983806337245668890011 := by
  unfold tailWord_6843459
  simp only [CollatzResearch.WordTrace]
  refine ⟨249601455314324287591797431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166400970209549525061198287 249601455314324287591797431)
  ·
    refine ⟨374402182971486431387696147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249601455314324287591797431 374402182971486431387696147)
    ·
      refine ⟨561603274457229647081544221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374402182971486431387696147 561603274457229647081544221)
      ·
        refine ⟨210601227921461117655579083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561603274457229647081544221 210601227921461117655579083)
        ·
          refine ⟨315901841882191676483368625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210601227921461117655579083 315901841882191676483368625)
          ·
            refine ⟨236926381411643757362526469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315901841882191676483368625 236926381411643757362526469)
            ·
              refine ⟨44423696514683204505473713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236926381411643757362526469 44423696514683204505473713)
              ·
                refine ⟨33317772386012403379105285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44423696514683204505473713 33317772386012403379105285)
                ·
                  refine ⟨6247082322377325633582241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33317772386012403379105285 6247082322377325633582241)
                  ·
                    refine ⟨4685311741782994225186681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247082322377325633582241 4685311741782994225186681)
                    ·
                      refine ⟨3513983806337245668890011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685311741782994225186681 3513983806337245668890011)
                      ·
                        rfl

theorem cell23_6843459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_6843459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843459 prefixEnd_6843459 := by exact prefixLift 6843459
  have htrace : WordTrace (prefixWord ++ tailWord_6843459) baseStart_6843459 baseEnd_6843459 := by
    simpa [prefixWord, tailWord_6843459, baseEnd_6843459] using wordTrace_append hprefix tailTrace_6843459
  have hstable : (prefixWord ++ tailWord_6843459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843459).length < 2 ^ (prefixWord ++ tailWord_6843459).sum := by decide
  have hdescent : baseEnd_6843459 < baseStart_6843459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843463 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_6843463 : Nat := 118140960795 + 6843463 * 2 ^ 59
def prefixEnd_6843463 : Nat := 4983230072969 + 3 ^ 40 * 6843463 * 2
def baseEnd_6843463 : Nat := 3513985860259863653239993

theorem tailTrace_6843463 : CollatzResearch.WordTrace tailWord_6843463 prefixEnd_6843463 3513985860259863653239993 := by
  unfold tailWord_6843463
  simp only [CollatzResearch.WordTrace]
  refine ⟨249601601206309796274943043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166401067470873197516628695 249601601206309796274943043)
  ·
    refine ⟨374402401809464694412414565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249601601206309796274943043 374402401809464694412414565)
    ·
      refine ⟨70200450339274630202327731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374402401809464694412414565 70200450339274630202327731)
      ·
        refine ⟨105300675508911945303491597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70200450339274630202327731 105300675508911945303491597)
        ·
          refine ⟨39487753315841979488809349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105300675508911945303491597 39487753315841979488809349)
          ·
            refine ⟨7403953746720371154151753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39487753315841979488809349 7403953746720371154151753)
            ·
              refine ⟨5552965310040278365613815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7403953746720371154151753 5552965310040278365613815)
              ·
                refine ⟨8329447965060417548420723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552965310040278365613815 8329447965060417548420723)
                ·
                  refine ⟨12494171947590626322631085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329447965060417548420723 12494171947590626322631085)
                  ·
                    refine ⟨4685314480346484870986657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12494171947590626322631085 4685314480346484870986657)
                    ·
                      refine ⟨3513985860259863653239993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685314480346484870986657 3513985860259863653239993)
                      ·
                        rfl

theorem cell23_6843463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_6843463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843463 prefixEnd_6843463 := by exact prefixLift 6843463
  have htrace : WordTrace (prefixWord ++ tailWord_6843463) baseStart_6843463 baseEnd_6843463 := by
    simpa [prefixWord, tailWord_6843463, baseEnd_6843463] using wordTrace_append hprefix tailTrace_6843463
  have hstable : (prefixWord ++ tailWord_6843463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843463).length < 2 ^ (prefixWord ++ tailWord_6843463).sum := by decide
  have hdescent : baseEnd_6843463 < baseStart_6843463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843486 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_6843486 : Nat := 118140960795 + 6843486 * 2 ^ 59
def prefixEnd_6843486 : Nat := 4983230072969 + 3 ^ 40 * 6843486 * 2
def baseEnd_6843486 : Nat := 1171332556771639021084129

theorem tailTrace_6843486 : CollatzResearch.WordTrace tailWord_6843486 prefixEnd_6843486 1171332556771639021084129 := by
  unfold tailWord_6843486
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200305010653308900378789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166401626723484314135353541 31200305010653308900378789)
  ·
    refine ⟨5850057189497495418821023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31200305010653308900378789 5850057189497495418821023)
    ·
      refine ⟨8775085784246243128231535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850057189497495418821023 8775085784246243128231535)
      ·
        refine ⟨13162628676369364692347303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775085784246243128231535 13162628676369364692347303)
        ·
          refine ⟨19743943014554047038520955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13162628676369364692347303 19743943014554047038520955)
          ·
            refine ⟨29615914521831070557781433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19743943014554047038520955 29615914521831070557781433)
            ·
              refine ⟨22211935891373302918336075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29615914521831070557781433 22211935891373302918336075)
              ·
                refine ⟨33317903837059954377504113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22211935891373302918336075 33317903837059954377504113)
                ·
                  refine ⟨24988427877794965783128085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33317903837059954377504113 24988427877794965783128085)
                  ·
                    refine ⟨1171332556771639021084129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24988427877794965783128085 1171332556771639021084129)
                    ·
                      rfl

theorem cell23_6843486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_6843486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843486 prefixEnd_6843486 := by exact prefixLift 6843486
  have htrace : WordTrace (prefixWord ++ tailWord_6843486) baseStart_6843486 baseEnd_6843486 := by
    simpa [prefixWord, tailWord_6843486, baseEnd_6843486] using wordTrace_append hprefix tailTrace_6843486
  have hstable : (prefixWord ++ tailWord_6843486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843486).length < 2 ^ (prefixWord ++ tailWord_6843486).sum := by decide
  have hdescent : baseEnd_6843486 < baseStart_6843486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843493 : List Nat := [1, 3, 1, 3, 2, 1, 5, 1, 2, 2, 2]
def baseStart_6843493 : Nat := 118140960795 + 6843493 * 2 ^ 59
def prefixEnd_6843493 : Nat := 4983230072969 + 3 ^ 40 * 6843493 * 2
def baseEnd_6843493 : Nat := 3514001264679498535864855

theorem tailTrace_6843493 : CollatzResearch.WordTrace tailWord_6843493 prefixEnd_6843493 3514001264679498535864855 := by
  unfold tailWord_6843493
  simp only [CollatzResearch.WordTrace]
  refine ⟨249602695396201111398535133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166401796930800740932356755 249602695396201111398535133)
  ·
    refine ⟨93601010773575416774450675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249602695396201111398535133 93601010773575416774450675)
    ·
      refine ⟨140401516160363125161676013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93601010773575416774450675 140401516160363125161676013)
      ·
        refine ⟨52650568560136171935628505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140401516160363125161676013 52650568560136171935628505)
        ·
          refine ⟨39487926420102128951721379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52650568560136171935628505 39487926420102128951721379)
          ·
            refine ⟨59231889630153193427582069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39487926420102128951721379 59231889630153193427582069)
            ·
              refine ⟨5552989652826861883835819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59231889630153193427582069 5552989652826861883835819)
              ·
                refine ⟨8329484479240292825753729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552989652826861883835819 8329484479240292825753729)
                ·
                  refine ⟨6247113359430219619315297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8329484479240292825753729 6247113359430219619315297)
                  ·
                    refine ⟨4685335019572664714486473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247113359430219619315297 4685335019572664714486473)
                    ·
                      refine ⟨3514001264679498535864855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685335019572664714486473 3514001264679498535864855)
                      ·
                        rfl

theorem cell23_6843493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_6843493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843493 prefixEnd_6843493 := by exact prefixLift 6843493
  have htrace : WordTrace (prefixWord ++ tailWord_6843493) baseStart_6843493 baseEnd_6843493 := by
    simpa [prefixWord, tailWord_6843493, baseEnd_6843493] using wordTrace_append hprefix tailTrace_6843493
  have hstable : (prefixWord ++ tailWord_6843493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843493).length < 2 ^ (prefixWord ++ tailWord_6843493).sum := by decide
  have hdescent : baseEnd_6843493 < baseStart_6843493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843505 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_6843505 : Nat := 118140960795 + 6843505 * 2 ^ 59
def prefixEnd_6843505 : Nat := 4983230072969 + 3 ^ 40 * 6843505 * 2
def baseEnd_6843505 : Nat := 3514007426447352488914799

theorem tailTrace_6843505 : CollatzResearch.WordTrace tailWord_6843505 prefixEnd_6843505 3514007426447352488914799 := by
  unfold tailWord_6843505
  simp only [CollatzResearch.WordTrace]
  refine ⟨249603133072157637447971969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166402088714771758298647979 249603133072157637447971969)
  ·
    refine ⟨187202349804118228085978977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249603133072157637447971969 187202349804118228085978977)
    ·
      refine ⟨140401762353088671064484233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187202349804118228085978977 140401762353088671064484233)
      ·
        refine ⟨105301321764816503298363175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140401762353088671064484233 105301321764816503298363175)
        ·
          refine ⟨157951982647224754947544763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105301321764816503298363175 157951982647224754947544763)
          ·
            refine ⟨236927973970837132421317145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157951982647224754947544763 236927973970837132421317145)
            ·
              refine ⟨177695980478127849315987859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236927973970837132421317145 177695980478127849315987859)
              ·
                refine ⟨266543970717191773973981789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177695980478127849315987859 266543970717191773973981789)
                ·
                  refine ⟨99953989018946915240243171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266543970717191773973981789 99953989018946915240243171)
                  ·
                    refine ⟨149930983528420372860364757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99953989018946915240243171 149930983528420372860364757)
                    ·
                      refine ⟨3514007426447352488914799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149930983528420372860364757 3514007426447352488914799)
                      ·
                        rfl

theorem cell23_6843505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_6843505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843505 prefixEnd_6843505 := by exact prefixLift 6843505
  have htrace : WordTrace (prefixWord ++ tailWord_6843505) baseStart_6843505 baseEnd_6843505 := by
    simpa [prefixWord, tailWord_6843505, baseEnd_6843505] using wordTrace_append hprefix tailTrace_6843505
  have hstable : (prefixWord ++ tailWord_6843505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843505).length < 2 ^ (prefixWord ++ tailWord_6843505).sum := by decide
  have hdescent : baseEnd_6843505 < baseStart_6843505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843549 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_6843549 : Nat := 118140960795 + 6843549 * 2 ^ 59
def prefixEnd_6843549 : Nat := 4983230072969 + 3 ^ 40 * 6843549 * 2
def baseEnd_6843549 : Nat := 3514030019596150316764597

theorem tailTrace_6843549 : CollatzResearch.WordTrace tailWord_6843549 prefixEnd_6843549 3514030019596150316764597 := by
  unfold tailWord_6843549
  simp only [CollatzResearch.WordTrace]
  refine ⟨249604737883998232962573701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166403158589332155308382467 249604737883998232962573701)
  ·
    refine ⟨46800888353249668680482569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249604737883998232962573701 46800888353249668680482569)
    ·
      refine ⟨35100666264937251510361927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46800888353249668680482569 35100666264937251510361927)
      ·
        refine ⟨52650999397405877265542891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35100666264937251510361927 52650999397405877265542891)
        ·
          refine ⟨78976499096108815898314337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52650999397405877265542891 78976499096108815898314337)
          ·
            refine ⟨59232374322081611923735753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78976499096108815898314337 59232374322081611923735753)
            ·
              refine ⟨44424280741561208942801815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59232374322081611923735753 44424280741561208942801815)
              ·
                refine ⟨66636421112341813414202723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44424280741561208942801815 66636421112341813414202723)
                ·
                  refine ⟨99954631668512720121304085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66636421112341813414202723 99954631668512720121304085)
                  ·
                    refine ⟨4685373359461533755686129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99954631668512720121304085 4685373359461533755686129)
                    ·
                      refine ⟨3514030019596150316764597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685373359461533755686129 3514030019596150316764597)
                      ·
                        rfl

theorem cell23_6843549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_6843549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843549 prefixEnd_6843549 := by exact prefixLift 6843549
  have htrace : WordTrace (prefixWord ++ tailWord_6843549) baseStart_6843549 baseEnd_6843549 := by
    simpa [prefixWord, tailWord_6843549, baseEnd_6843549] using wordTrace_append hprefix tailTrace_6843549
  have hstable : (prefixWord ++ tailWord_6843549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843549).length < 2 ^ (prefixWord ++ tailWord_6843549).sum := by decide
  have hdescent : baseEnd_6843549 < baseStart_6843549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843609 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 1, 5, 2]
def baseStart_6843609 : Nat := 118140960795 + 6843609 * 2 ^ 59
def prefixEnd_6843609 : Nat := 4983230072969 + 3 ^ 40 * 6843609 * 2
def baseEnd_6843609 : Nat := 3514060828435420082014321

theorem tailTrace_6843609 : CollatzResearch.WordTrace tailWord_6843609 prefixEnd_6843609 3514060828435420082014321 := by
  unfold tailWord_6843609
  simp only [CollatzResearch.WordTrace]
  refine ⟨249606926263780863209757881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166404617509187242139838587 249606926263780863209757881)
  ·
    refine ⟨187205194697835647407318411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249606926263780863209757881 187205194697835647407318411)
    ·
      refine ⟨280807792046753471110977617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187205194697835647407318411 280807792046753471110977617)
      ·
        refine ⟨210605844035065103333233213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280807792046753471110977617 210605844035065103333233213)
        ·
          refine ⟨78977191513149413749962455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210605844035065103333233213 78977191513149413749962455)
          ·
            refine ⟨118465787269724120624943683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78977191513149413749962455 118465787269724120624943683)
            ·
              refine ⟨177698680904586180937415525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118465787269724120624943683 177698680904586180937415525)
              ·
                refine ⟨33318502669609908925765411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177698680904586180937415525 33318502669609908925765411)
                ·
                  refine ⟨49977754004414863388648117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33318502669609908925765411 49977754004414863388648117)
                  ·
                    refine ⟨4685414437913893442685761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49977754004414863388648117 4685414437913893442685761)
                    ·
                      refine ⟨3514060828435420082014321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685414437913893442685761 3514060828435420082014321)
                      ·
                        rfl

theorem cell23_6843609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_6843609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843609 prefixEnd_6843609 := by exact prefixLift 6843609
  have htrace : WordTrace (prefixWord ++ tailWord_6843609) baseStart_6843609 baseEnd_6843609 := by
    simpa [prefixWord, tailWord_6843609, baseEnd_6843609] using wordTrace_append hprefix tailTrace_6843609
  have hstable : (prefixWord ++ tailWord_6843609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843609).length < 2 ^ (prefixWord ++ tailWord_6843609).sum := by decide
  have hdescent : baseEnd_6843609 < baseStart_6843609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843616 : List Nat := [2, 1, 1, 3, 1, 5, 1, 2, 3, 1, 3]
def baseStart_6843616 : Nat := 118140960795 + 6843616 * 2 ^ 59
def prefixEnd_6843616 : Nat := 4983230072969 + 3 ^ 40 * 6843616 * 2
def baseEnd_6843616 : Nat := 3514064422800001554626789

theorem tailTrace_6843616 : CollatzResearch.WordTrace tailWord_6843616 prefixEnd_6843616 3514064422800001554626789 := by
  unfold tailWord_6843616
  simp only [CollatzResearch.WordTrace]
  refine ⟨124803590787377751702631351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166404787716503668936841801 124803590787377751702631351)
  ·
    refine ⟨187205386181066627553947027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124803590787377751702631351 187205386181066627553947027)
    ·
      refine ⟨280808079271599941330920541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187205386181066627553947027 280808079271599941330920541)
      ·
        refine ⟨105303029726849977999095203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280808079271599941330920541 105303029726849977999095203)
        ·
          refine ⟨157954544590274966998642805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105303029726849977999095203 157954544590274966998642805)
          ·
            refine ⟨14808238555338278156122763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157954544590274966998642805 14808238555338278156122763)
            ·
              refine ⟨22212357833007417234184145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808238555338278156122763 22212357833007417234184145)
              ·
                refine ⟨16659268374755562925638109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22212357833007417234184145 16659268374755562925638109)
                ·
                  refine ⟨6247225640533336097114291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16659268374755562925638109 6247225640533336097114291)
                  ·
                    refine ⟨9370838460800004145671437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6247225640533336097114291 9370838460800004145671437)
                    ·
                      refine ⟨3514064422800001554626789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9370838460800004145671437 3514064422800001554626789)
                      ·
                        rfl

theorem cell23_6843616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_6843616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843616 prefixEnd_6843616 := by exact prefixLift 6843616
  have htrace : WordTrace (prefixWord ++ tailWord_6843616) baseStart_6843616 baseEnd_6843616 := by
    simpa [prefixWord, tailWord_6843616, baseEnd_6843616] using wordTrace_append hprefix tailTrace_6843616
  have hstable : (prefixWord ++ tailWord_6843616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843616).length < 2 ^ (prefixWord ++ tailWord_6843616).sum := by decide
  have hdescent : baseEnd_6843616 < baseStart_6843616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843626 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2]
def baseStart_6843626 : Nat := 118140960795 + 6843626 * 2 ^ 59
def prefixEnd_6843626 : Nat := 4983230072969 + 3 ^ 40 * 6843626 * 2
def baseEnd_6843626 : Nat := 3514069557606546515501743

theorem tailTrace_6843626 : CollatzResearch.WordTrace tailWord_6843626 prefixEnd_6843626 3514069557606546515501743 := by
  unfold tailWord_6843626
  simp only [CollatzResearch.WordTrace]
  refine ⟨62401886576179818778281683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166405030869812850075417821 62401886576179818778281683)
  ·
    refine ⟨93602829864269728167422525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62401886576179818778281683 93602829864269728167422525)
    ·
      refine ⟨35101061199101148062783447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93602829864269728167422525 35101061199101148062783447)
      ·
        refine ⟨52651591798651722094175171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35101061199101148062783447 52651591798651722094175171)
        ·
          refine ⟨78977387697977583141262757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52651591798651722094175171 78977387697977583141262757)
          ·
            refine ⟨14808260193370796838986767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78977387697977583141262757 14808260193370796838986767)
            ·
              refine ⟨22212390290056195258480151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808260193370796838986767 22212390290056195258480151)
              ·
                refine ⟨33318585435084292887720227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22212390290056195258480151 33318585435084292887720227)
                ·
                  refine ⟨49977878152626439331580341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33318585435084292887720227 49977878152626439331580341)
                  ·
                    refine ⟨4685426076808728687335657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49977878152626439331580341 4685426076808728687335657)
                    ·
                      refine ⟨3514069557606546515501743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685426076808728687335657 3514069557606546515501743)
                      ·
                        rfl

theorem cell23_6843626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_6843626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843626 prefixEnd_6843626 := by exact prefixLift 6843626
  have htrace : WordTrace (prefixWord ++ tailWord_6843626) baseStart_6843626 baseEnd_6843626 := by
    simpa [prefixWord, tailWord_6843626, baseEnd_6843626] using wordTrace_append hprefix tailTrace_6843626
  have hstable : (prefixWord ++ tailWord_6843626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843626).length < 2 ^ (prefixWord ++ tailWord_6843626).sum := by decide
  have hdescent : baseEnd_6843626 < baseStart_6843626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843639 : List Nat := [1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 4]
def baseStart_6843639 : Nat := 118140960795 + 6843639 * 2 ^ 59
def prefixEnd_6843639 : Nat := 4983230072969 + 3 ^ 40 * 6843639 * 2
def baseEnd_6843639 : Nat := 3514076232855054964639183

theorem tailTrace_6843639 : CollatzResearch.WordTrace tailWord_6843639 prefixEnd_6843639 3514076232855054964639183 := by
  unfold tailWord_6843639
  simp only [CollatzResearch.WordTrace]
  refine ⟨249608020453672178333349971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166405346969114785555566647 249608020453672178333349971)
  ·
    refine ⟨374412030680508267500024957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249608020453672178333349971 374412030680508267500024957)
    ·
      refine ⟨140404511505190600312509359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374412030680508267500024957 140404511505190600312509359)
      ·
        refine ⟨210606767257785900468764039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140404511505190600312509359 210606767257785900468764039)
        ·
          refine ⟨315910150886678850703146059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210606767257785900468764039 315910150886678850703146059)
          ·
            refine ⟨473865226330018276054719089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315910150886678850703146059 473865226330018276054719089)
            ·
              refine ⟨355398919747513707041039317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473865226330018276054719089 355398919747513707041039317)
              ·
                refine ⟨8329662181582352508774359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 355398919747513707041039317 8329662181582352508774359)
                ·
                  refine ⟨12494493272373528763161539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329662181582352508774359 12494493272373528763161539)
                  ·
                    refine ⟨18741739908560293144742309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12494493272373528763161539 18741739908560293144742309)
                    ·
                      refine ⟨3514076232855054964639183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18741739908560293144742309 3514076232855054964639183)
                      ·
                        rfl

theorem cell23_6843639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_6843639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843639 prefixEnd_6843639 := by exact prefixLift 6843639
  have htrace : WordTrace (prefixWord ++ tailWord_6843639) baseStart_6843639 baseEnd_6843639 := by
    simpa [prefixWord, tailWord_6843639, baseEnd_6843639] using wordTrace_append hprefix tailTrace_6843639
  have hstable : (prefixWord ++ tailWord_6843639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843639).length < 2 ^ (prefixWord ++ tailWord_6843639).sum := by decide
  have hdescent : baseEnd_6843639 < baseStart_6843639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843650 : List Nat := [3, 4, 1, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_6843650 : Nat := 118140960795 + 6843650 * 2 ^ 59
def prefixEnd_6843650 : Nat := 4983230072969 + 3 ^ 40 * 6843650 * 2
def baseEnd_6843650 : Nat := 3514081881142254421601633

theorem tailTrace_6843650 : CollatzResearch.WordTrace tailWord_6843650 prefixEnd_6843650 3514081881142254421601633 := by
  unfold tailWord_6843650
  simp only [CollatzResearch.WordTrace]
  refine ⟨62402105414158081803000101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166405614437754884808000269 62402105414158081803000101)
  ·
    refine ⟨11700394765154640338062519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62402105414158081803000101 11700394765154640338062519)
    ·
      refine ⟨17550592147731960507093779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11700394765154640338062519 17550592147731960507093779)
      ·
        refine ⟨26325888221597940760640669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17550592147731960507093779 26325888221597940760640669)
        ·
          refine ⟨9872208083099227785240251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26325888221597940760640669 9872208083099227785240251)
          ·
            refine ⟨14808312124648841677860377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872208083099227785240251 14808312124648841677860377)
            ·
              refine ⟨11106234093486631258395283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14808312124648841677860377 11106234093486631258395283)
              ·
                refine ⟨16659351140229946887592925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11106234093486631258395283 16659351140229946887592925)
                ·
                  refine ⟨6247256677586230082847347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16659351140229946887592925 6247256677586230082847347)
                  ·
                    refine ⟨9370885016379345124271021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6247256677586230082847347 9370885016379345124271021)
                    ·
                      refine ⟨3514081881142254421601633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9370885016379345124271021 3514081881142254421601633)
                      ·
                        rfl

theorem cell23_6843650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_6843650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843650 prefixEnd_6843650 := by exact prefixLift 6843650
  have htrace : WordTrace (prefixWord ++ tailWord_6843650) baseStart_6843650 baseEnd_6843650 := by
    simpa [prefixWord, tailWord_6843650, baseEnd_6843650] using wordTrace_append hprefix tailTrace_6843650
  have hstable : (prefixWord ++ tailWord_6843650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843650).length < 2 ^ (prefixWord ++ tailWord_6843650).sum := by decide
  have hdescent : baseEnd_6843650 < baseStart_6843650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843659 : List Nat := [1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5]
def baseStart_6843659 : Nat := 118140960795 + 6843659 * 2 ^ 59
def prefixEnd_6843659 : Nat := 4983230072969 + 3 ^ 40 * 6843659 * 2
def baseEnd_6843659 : Nat := 3514086502468144886389091

theorem tailTrace_6843659 : CollatzResearch.WordTrace tailWord_6843659 prefixEnd_6843659 3514086502468144886389091 := by
  unfold tailWord_6843659
  simp only [CollatzResearch.WordTrace]
  refine ⟨249608749913599721749078031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166405833275733147832718687 249608749913599721749078031)
  ·
    refine ⟨374413124870399582623617047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249608749913599721749078031 374413124870399582623617047)
    ·
      refine ⟨561619687305599373935425571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374413124870399582623617047 561619687305599373935425571)
      ·
        refine ⟨842429530958399060903138357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561619687305599373935425571 842429530958399060903138357)
        ·
          refine ⟨78977768527349911959669221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 842429530958399060903138357 78977768527349911959669221)
          ·
            refine ⟨14808331598878108492437979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78977768527349911959669221 14808331598878108492437979)
            ·
              refine ⟨22212497398317162738656969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808331598878108492437979 22212497398317162738656969)
              ·
                refine ⟨16659373048737872053992727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22212497398317162738656969 16659373048737872053992727)
                ·
                  refine ⟨24989059573106808080989091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16659373048737872053992727 24989059573106808080989091)
                  ·
                    refine ⟨37483589359660212121483637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24989059573106808080989091 37483589359660212121483637)
                    ·
                      refine ⟨3514086502468144886389091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37483589359660212121483637 3514086502468144886389091)
                      ·
                        rfl

theorem cell23_6843659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5].length) (baseStart_6843659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843659 prefixEnd_6843659 := by exact prefixLift 6843659
  have htrace : WordTrace (prefixWord ++ tailWord_6843659) baseStart_6843659 baseEnd_6843659 := by
    simpa [prefixWord, tailWord_6843659, baseEnd_6843659] using wordTrace_append hprefix tailTrace_6843659
  have hstable : (prefixWord ++ tailWord_6843659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843659).length < 2 ^ (prefixWord ++ tailWord_6843659).sum := by decide
  have hdescent : baseEnd_6843659 < baseStart_6843659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843676 : List Nat := [2, 2, 3, 1, 1, 1, 3, 4, 1, 2, 3]
def baseStart_6843676 : Nat := 118140960795 + 6843676 * 2 ^ 59
def prefixEnd_6843676 : Nat := 4983230072969 + 3 ^ 40 * 6843676 * 2
def baseEnd_6843676 : Nat := 3514095231639271319876513

theorem tailTrace_6843676 : CollatzResearch.WordTrace tailWord_6843676 prefixEnd_6843676 3514095231639271319876513 := by
  unfold tailWord_6843676
  simp only [CollatzResearch.WordTrace]
  refine ⟨124804684977269066826223441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166406246636358755768297921 124804684977269066826223441)
  ·
    refine ⟨93603513732951800119667581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124804684977269066826223441 93603513732951800119667581)
    ·
      refine ⟨35101317649856925044875343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93603513732951800119667581 35101317649856925044875343)
      ·
        refine ⟨52651976474785387567313015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35101317649856925044875343 52651976474785387567313015)
        ·
          refine ⟨78977964712178081350969523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52651976474785387567313015 78977964712178081350969523)
          ·
            refine ⟨118466947068267122026454285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78977964712178081350969523 118466947068267122026454285)
            ·
              refine ⟨44425105150600170759920357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118466947068267122026454285 44425105150600170759920357)
              ·
                refine ⟨8329707215737532017485067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44425105150600170759920357 8329707215737532017485067)
                ·
                  refine ⟨12494560823606298026227601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8329707215737532017485067 12494560823606298026227601)
                  ·
                    refine ⟨9370920617704723519670701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12494560823606298026227601 9370920617704723519670701)
                    ·
                      refine ⟨3514095231639271319876513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9370920617704723519670701 3514095231639271319876513)
                      ·
                        rfl

theorem cell23_6843676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_6843676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843676 prefixEnd_6843676 := by exact prefixLift 6843676
  have htrace : WordTrace (prefixWord ++ tailWord_6843676) baseStart_6843676 baseEnd_6843676 := by
    simpa [prefixWord, tailWord_6843676, baseEnd_6843676] using wordTrace_append hprefix tailTrace_6843676
  have hstable : (prefixWord ++ tailWord_6843676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843676).length < 2 ^ (prefixWord ++ tailWord_6843676).sum := by decide
  have hdescent : baseEnd_6843676 < baseStart_6843676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843679 : List Nat := [1, 1, 2, 4, 4, 1, 1, 9]
def baseStart_6843679 : Nat := 118140960795 + 6843679 * 2 ^ 59
def prefixEnd_6843679 : Nat := 4983230072969 + 3 ^ 40 * 6843679 * 2
def baseEnd_6843679 : Nat := 130151732299304992894037

theorem tailTrace_6843679 : CollatzResearch.WordTrace tailWord_6843679 prefixEnd_6843679 130151732299304992894037 := by
  unfold tailWord_6843679
  simp only [CollatzResearch.WordTrace]
  refine ⟨249609479373527265164806091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166406319582351510109870727 249609479373527265164806091)
  ·
    refine ⟨374414219060290897747209137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249609479373527265164806091 374414219060290897747209137)
    ·
      refine ⟨280810664295218173310406853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374414219060290897747209137 280810664295218173310406853)
      ·
        refine ⟨52651999555353407495701285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280810664295218173310406853 52651999555353407495701285)
        ·
          refine ⟨9872249916628763905443991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52651999555353407495701285 9872249916628763905443991)
          ·
            refine ⟨14808374874943145858165987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872249916628763905443991 14808374874943145858165987)
            ·
              refine ⟨22212562312414718787248981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808374874943145858165987 22212562312414718787248981)
              ·
                refine ⟨130151732299304992894037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22212562312414718787248981 130151732299304992894037)
                ·
                  rfl

theorem cell23_6843679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 9].length) (baseStart_6843679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843679 prefixEnd_6843679 := by exact prefixLift 6843679
  have htrace : WordTrace (prefixWord ++ tailWord_6843679) baseStart_6843679 baseEnd_6843679 := by
    simpa [prefixWord, tailWord_6843679, baseEnd_6843679] using wordTrace_append hprefix tailTrace_6843679
  have hstable : (prefixWord ++ tailWord_6843679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843679).length < 2 ^ (prefixWord ++ tailWord_6843679).sum := by decide
  have hdescent : baseEnd_6843679 < baseStart_6843679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843692 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_6843692 : Nat := 118140960795 + 6843692 * 2 ^ 59
def prefixEnd_6843692 : Nat := 4983230072969 + 3 ^ 40 * 6843692 * 2
def baseEnd_6843692 : Nat := 1171367815776581085758813

theorem tailTrace_6843692 : CollatzResearch.WordTrace tailWord_6843692 prefixEnd_6843692 1171367815776581085758813 := by
  unfold tailWord_6843692
  simp only [CollatzResearch.WordTrace]
  refine ⟨124804976761240084192514665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166406635681653445590019553 124804976761240084192514665)
  ·
    refine ⟨93603732570930063144385999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124804976761240084192514665 93603732570930063144385999)
    ·
      refine ⟨140405598856395094716578999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93603732570930063144385999 140405598856395094716578999)
      ·
        refine ⟨210608398284592642074868499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140405598856395094716578999 210608398284592642074868499)
        ·
          refine ⟨315912597426888963112302749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210608398284592642074868499 315912597426888963112302749)
          ·
            refine ⟨118467224035083361167113531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315912597426888963112302749 118467224035083361167113531)
            ·
              refine ⟨177700836052625041750670297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118467224035083361167113531 177700836052625041750670297)
              ·
                refine ⟨133275627039468781313002723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177700836052625041750670297 133275627039468781313002723)
                ·
                  refine ⟨199913440559203171969504085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133275627039468781313002723 199913440559203171969504085)
                  ·
                    refine ⟨1171367815776581085758813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199913440559203171969504085 1171367815776581085758813)
                    ·
                      rfl

theorem cell23_6843692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_6843692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843692 prefixEnd_6843692 := by exact prefixLift 6843692
  have htrace : WordTrace (prefixWord ++ tailWord_6843692) baseStart_6843692 baseEnd_6843692 := by
    simpa [prefixWord, tailWord_6843692, baseEnd_6843692] using wordTrace_append hprefix tailTrace_6843692
  have hstable : (prefixWord ++ tailWord_6843692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843692).length < 2 ^ (prefixWord ++ tailWord_6843692).sum := by decide
  have hdescent : baseEnd_6843692 < baseStart_6843692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843693 : List Nat := [1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_6843693 : Nat := 118140960795 + 6843693 * 2 ^ 59
def prefixEnd_6843693 : Nat := 4983230072969 + 3 ^ 40 * 6843693 * 2
def baseEnd_6843693 : Nat := 3514103960810397753363935

theorem tailTrace_6843693 : CollatzResearch.WordTrace tailWord_6843693 prefixEnd_6843693 3514103960810397753363935 := by
  unfold tailWord_6843693
  simp only [CollatzResearch.WordTrace]
  refine ⟨249609989995476545555815733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166406659996984363703877155 249609989995476545555815733)
  ·
    refine ⟨23400936562075926145857725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249609989995476545555815733 23400936562075926145857725)
    ·
      refine ⟨8775351210778472304696647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23400936562075926145857725 8775351210778472304696647)
      ·
        refine ⟨13163026816167708457044971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775351210778472304696647 13163026816167708457044971)
        ·
          refine ⟨19744540224251562685567457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13163026816167708457044971 19744540224251562685567457)
          ·
            refine ⟨14808405168188672014175593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19744540224251562685567457 14808405168188672014175593)
            ·
              refine ⟨11106303876141504010631695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14808405168188672014175593 11106303876141504010631695)
              ·
                refine ⟨16659455814212256015947543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11106303876141504010631695 16659455814212256015947543)
                ·
                  refine ⟨24989183721318384023921315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16659455814212256015947543 24989183721318384023921315)
                  ·
                    refine ⟨37483775581977576035881973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24989183721318384023921315 37483775581977576035881973)
                    ·
                      refine ⟨3514103960810397753363935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37483775581977576035881973 3514103960810397753363935)
                      ·
                        rfl

theorem cell23_6843693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_6843693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843693 prefixEnd_6843693 := by exact prefixLift 6843693
  have htrace : WordTrace (prefixWord ++ tailWord_6843693) baseStart_6843693 baseEnd_6843693 := by
    simpa [prefixWord, tailWord_6843693, baseEnd_6843693] using wordTrace_append hprefix tailTrace_6843693
  have hstable : (prefixWord ++ tailWord_6843693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843693).length < 2 ^ (prefixWord ++ tailWord_6843693).sum := by decide
  have hdescent : baseEnd_6843693 < baseStart_6843693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843706 : List Nat := [3, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3]
def baseStart_6843706 : Nat := 118140960795 + 6843706 * 2 ^ 59
def prefixEnd_6843706 : Nat := 4983230072969 + 3 ^ 40 * 6843706 * 2
def baseEnd_6843706 : Nat := 3514110636058906202501375

theorem tailTrace_6843706 : CollatzResearch.WordTrace tailWord_6843706 prefixEnd_6843706 3514110636058906202501375 := by
  unfold tailWord_6843706
  simp only [CollatzResearch.WordTrace]
  refine ⟨62402616036107362194009743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166406976096286299184025981 62402616036107362194009743)
  ·
    refine ⟨93603924054161043291014615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62402616036107362194009743 93603924054161043291014615)
    ·
      refine ⟨140405886081241564936521923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93603924054161043291014615 140405886081241564936521923)
      ·
        refine ⟨210608829121862347404782885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140405886081241564936521923 210608829121862347404782885)
        ·
          refine ⟨39489155460349190138396791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210608829121862347404782885 39489155460349190138396791)
          ·
            refine ⟨59233733190523785207595187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39489155460349190138396791 59233733190523785207595187)
            ·
              refine ⟨88850599785785677811392781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59233733190523785207595187 88850599785785677811392781)
              ·
                refine ⟨33318974919669629179272293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88850599785785677811392781 33318974919669629179272293)
                ·
                  refine ⟨6247307797438055471113555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33318974919669629179272293 6247307797438055471113555)
                  ·
                    refine ⟨9370961696157083206670333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6247307797438055471113555 9370961696157083206670333)
                    ·
                      refine ⟨3514110636058906202501375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9370961696157083206670333 3514110636058906202501375)
                      ·
                        rfl

theorem cell23_6843706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 3, 4, 1, 3].length) (baseStart_6843706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843706 prefixEnd_6843706 := by exact prefixLift 6843706
  have htrace : WordTrace (prefixWord ++ tailWord_6843706) baseStart_6843706 baseEnd_6843706 := by
    simpa [prefixWord, tailWord_6843706, baseEnd_6843706] using wordTrace_append hprefix tailTrace_6843706
  have hstable : (prefixWord ++ tailWord_6843706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843706).length < 2 ^ (prefixWord ++ tailWord_6843706).sum := by decide
  have hdescent : baseEnd_6843706 < baseStart_6843706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843733 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_6843733 : Nat := 118140960795 + 6843733 * 2 ^ 59
def prefixEnd_6843733 : Nat := 4983230072969 + 3 ^ 40 * 6843733 * 2
def baseEnd_6843733 : Nat := 3514124500036577596863751

theorem tailTrace_6843733 : CollatzResearch.WordTrace tailWord_6843733 prefixEnd_6843733 3514124500036577596863751 := by
  unfold tailWord_6843733
  simp only [CollatzResearch.WordTrace]
  refine ⟨249611448915331632387271853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166407632610221088258181235 249611448915331632387271853)
  ·
    refine ⟨93604293343249362145226945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249611448915331632387271853 93604293343249362145226945)
    ·
      refine ⟨70203220007437021608920209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93604293343249362145226945 70203220007437021608920209)
      ·
        refine ⟨52652415005577766206690157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70203220007437021608920209 52652415005577766206690157)
        ·
          refine ⟨19744655627091662327508809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52652415005577766206690157 19744655627091662327508809)
          ·
            refine ⟨14808491720318746745631607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19744655627091662327508809 14808491720318746745631607)
            ·
              refine ⟨22212737580478120118447411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808491720318746745631607 22212737580478120118447411)
              ·
                refine ⟨33319106370717180177671117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22212737580478120118447411 33319106370717180177671117)
                ·
                  refine ⟨12494664889018942566626669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33319106370717180177671117 12494664889018942566626669)
                  ·
                    refine ⟨4685499333382103462485001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12494664889018942566626669 4685499333382103462485001)
                    ·
                      refine ⟨3514124500036577596863751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685499333382103462485001 3514124500036577596863751)
                      ·
                        rfl

theorem cell23_6843733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_6843733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843733 prefixEnd_6843733 := by exact prefixLift 6843733
  have htrace : WordTrace (prefixWord ++ tailWord_6843733) baseStart_6843733 baseEnd_6843733 := by
    simpa [prefixWord, tailWord_6843733, baseEnd_6843733] using wordTrace_append hprefix tailTrace_6843733
  have hstable : (prefixWord ++ tailWord_6843733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843733).length < 2 ^ (prefixWord ++ tailWord_6843733).sum := by decide
  have hdescent : baseEnd_6843733 < baseStart_6843733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843749 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 5]
def baseStart_6843749 : Nat := 118140960795 + 6843749 * 2 ^ 59
def prefixEnd_6843749 : Nat := 4983230072969 + 3 ^ 40 * 6843749 * 2
def baseEnd_6843749 : Nat := 3514132715727049534263677

theorem tailTrace_6843749 : CollatzResearch.WordTrace tailWord_6843749 prefixEnd_6843749 3514132715727049534263677 := by
  unfold tailWord_6843749
  simp only [CollatzResearch.WordTrace]
  refine ⟨249612032483273667119854301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166408021655515778079902867 249612032483273667119854301)
  ·
    refine ⟨93604512181227625169945363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249612032483273667119854301 93604512181227625169945363)
    ·
      refine ⟨140406768271841437754918045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93604512181227625169945363 140406768271841437754918045)
      ·
        refine ⟨52652538101940539158094267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140406768271841437754918045 52652538101940539158094267)
        ·
          refine ⟨78978807152910808737141401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52652538101940539158094267 78978807152910808737141401)
          ·
            refine ⟨59234105364683106552856051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78978807152910808737141401 59234105364683106552856051)
            ·
              refine ⟨88851158047024659829284077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59234105364683106552856051 88851158047024659829284077)
              ·
                refine ⟨33319184267634247435981529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88851158047024659829284077 33319184267634247435981529)
                ·
                  refine ⟨24989388200725685576986147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33319184267634247435981529 24989388200725685576986147)
                  ·
                    refine ⟨37484082301088528365479221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24989388200725685576986147 37484082301088528365479221)
                    ·
                      refine ⟨3514132715727049534263677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37484082301088528365479221 3514132715727049534263677)
                      ·
                        rfl

theorem cell23_6843749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_6843749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843749 prefixEnd_6843749 := by exact prefixLift 6843749
  have htrace : WordTrace (prefixWord ++ tailWord_6843749) baseStart_6843749 baseEnd_6843749 := by
    simpa [prefixWord, tailWord_6843749, baseEnd_6843749] using wordTrace_append hprefix tailTrace_6843749
  have hstable : (prefixWord ++ tailWord_6843749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843749).length < 2 ^ (prefixWord ++ tailWord_6843749).sum := by decide
  have hdescent : baseEnd_6843749 < baseStart_6843749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843758 : List Nat := [4, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2]
def baseStart_6843758 : Nat := 118140960795 + 6843758 * 2 ^ 59
def prefixEnd_6843758 : Nat := 4983230072969 + 3 ^ 40 * 6843758 * 2
def baseEnd_6843758 : Nat := 3514137337052939999051137

theorem tailTrace_6843758 : CollatzResearch.WordTrace tailWord_6843758 prefixEnd_6843758 3514137337052939999051137 := by
  unfold tailWord_6843758
  simp only [CollatzResearch.WordTrace]
  refine ⟨31201545092530132707116491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166408240493494041104621285 31201545092530132707116491)
  ·
    refine ⟨46802317638795199060674737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31201545092530132707116491 46802317638795199060674737)
    ·
      refine ⟨35101738229096399295506053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46802317638795199060674737 35101738229096399295506053)
      ·
        refine ⟨6581575917955574867907385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35101738229096399295506053 6581575917955574867907385)
        ·
          refine ⟨4936181938466681150930539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6581575917955574867907385 4936181938466681150930539)
          ·
            refine ⟨7404272907700021726395809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936181938466681150930539 7404272907700021726395809)
            ·
              refine ⟨5553204680775016294796857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7404272907700021726395809 5553204680775016294796857)
              ·
                refine ⟨4164903510581262221097643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553204680775016294796857 4164903510581262221097643)
                ·
                  refine ⟨6247355265871893331646465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164903510581262221097643 6247355265871893331646465)
                  ·
                    refine ⟨4685516449403919998734849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247355265871893331646465 4685516449403919998734849)
                    ·
                      refine ⟨3514137337052939999051137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685516449403919998734849 3514137337052939999051137)
                      ·
                        rfl

theorem cell23_6843758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_6843758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843758 prefixEnd_6843758 := by exact prefixLift 6843758
  have htrace : WordTrace (prefixWord ++ tailWord_6843758) baseStart_6843758 baseEnd_6843758 := by
    simpa [prefixWord, tailWord_6843758, baseEnd_6843758] using wordTrace_append hprefix tailTrace_6843758
  have hstable : (prefixWord ++ tailWord_6843758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843758).length < 2 ^ (prefixWord ++ tailWord_6843758).sum := by decide
  have hdescent : baseEnd_6843758 < baseStart_6843758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843759 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 4]
def baseStart_6843759 : Nat := 118140960795 + 6843759 * 2 ^ 59
def prefixEnd_6843759 : Nat := 4983230072969 + 3 ^ 40 * 6843759 * 2
def baseEnd_6843759 : Nat := 3514137850533594495138631

theorem tailTrace_6843759 : CollatzResearch.WordTrace tailWord_6843759 prefixEnd_6843759 3514137850533594495138631 := by
  unfold tailWord_6843759
  simp only [CollatzResearch.WordTrace]
  refine ⟨249612397213237438827718331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166408264808824959218478887 249612397213237438827718331)
  ·
    refine ⟨374418595819856158241577497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249612397213237438827718331 374418595819856158241577497)
    ·
      refine ⟨280813946864892118681183123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374418595819856158241577497 280813946864892118681183123)
      ·
        refine ⟨421220920297338178021774685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280813946864892118681183123 421220920297338178021774685)
        ·
          refine ⟨157957845111501816758165507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421220920297338178021774685 157957845111501816758165507)
          ·
            refine ⟨236936767667252725137248261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157957845111501816758165507 236936767667252725137248261)
            ·
              refine ⟨44425643937609885963234049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236936767667252725137248261 44425643937609885963234049)
              ·
                refine ⟨33319232953207414472425537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44425643937609885963234049 33319232953207414472425537)
                ·
                  refine ⟨24989424714905560854319153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33319232953207414472425537 24989424714905560854319153)
                  ·
                    refine ⟨18742068536179170640739365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24989424714905560854319153 18742068536179170640739365)
                    ·
                      refine ⟨3514137850533594495138631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18742068536179170640739365 3514137850533594495138631)
                      ·
                        rfl

theorem cell23_6843759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_6843759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843759 prefixEnd_6843759 := by exact prefixLift 6843759
  have htrace : WordTrace (prefixWord ++ tailWord_6843759) baseStart_6843759 baseEnd_6843759 := by
    simpa [prefixWord, tailWord_6843759, baseEnd_6843759] using wordTrace_append hprefix tailTrace_6843759
  have hstable : (prefixWord ++ tailWord_6843759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843759).length < 2 ^ (prefixWord ++ tailWord_6843759).sum := by decide
  have hdescent : baseEnd_6843759 < baseStart_6843759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843780 : List Nat := [2, 3, 2, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_6843780 : Nat := 118140960795 + 6843780 * 2 ^ 59
def prefixEnd_6843780 : Nat := 4983230072969 + 3 ^ 40 * 6843780 * 2
def baseEnd_6843780 : Nat := 3514148633627338912976035

theorem tailTrace_6843780 : CollatzResearch.WordTrace tailWord_6843780 prefixEnd_6843780 3514148633627338912976035 := by
  unfold tailWord_6843780
  simp only [CollatzResearch.WordTrace]
  refine ⟨124806581573080679707116397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166408775430774239609488529 124806581573080679707116397)
  ·
    refine ⟨46802468089905254890168649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124806581573080679707116397 46802468089905254890168649)
    ·
      refine ⟨35101851067428941167626487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46802468089905254890168649 35101851067428941167626487)
      ·
        refine ⟨52652776601143411751439731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35101851067428941167626487 52652776601143411751439731)
        ·
          refine ⟨78979164901715117627159597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52652776601143411751439731 78979164901715117627159597)
          ·
            refine ⟨29617186838143169110184849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78979164901715117627159597 29617186838143169110184849)
            ·
              refine ⟨22212890128607376832638637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29617186838143169110184849 22212890128607376832638637)
              ·
                refine ⟨8329833798227766312239489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22212890128607376832638637 8329833798227766312239489)
                ·
                  refine ⟨6247375348670824734179617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8329833798227766312239489 6247375348670824734179617)
                  ·
                    refine ⟨4685531511503118550634713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247375348670824734179617 4685531511503118550634713)
                    ·
                      refine ⟨3514148633627338912976035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685531511503118550634713 3514148633627338912976035)
                      ·
                        rfl

theorem cell23_6843780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_6843780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843780 prefixEnd_6843780 := by exact prefixLift 6843780
  have htrace : WordTrace (prefixWord ++ tailWord_6843780) baseStart_6843780 baseEnd_6843780 := by
    simpa [prefixWord, tailWord_6843780, baseEnd_6843780] using wordTrace_append hprefix tailTrace_6843780
  have hstable : (prefixWord ++ tailWord_6843780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843780).length < 2 ^ (prefixWord ++ tailWord_6843780).sum := by decide
  have hdescent : baseEnd_6843780 < baseStart_6843780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843849 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_6843849 : Nat := 118140960795 + 6843849 * 2 ^ 59
def prefixEnd_6843849 : Nat := 4983230072969 + 3 ^ 40 * 6843849 * 2
def baseEnd_6843849 : Nat := 3514184063792499143013217

theorem tailTrace_6843849 : CollatzResearch.WordTrace tailWord_6843849 prefixEnd_6843849 3514184063792499143013217 := by
  unfold tailWord_6843849
  simp only [CollatzResearch.WordTrace]
  refine ⟨249615679782911384198494601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166410453188607589465663067 249615679782911384198494601)
  ·
    refine ⟨187211759837183538148870951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249615679782911384198494601 187211759837183538148870951)
    ·
      refine ⟨280817639755775307223306427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187211759837183538148870951 280817639755775307223306427)
      ·
        refine ⟨421226459633662960834959641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280817639755775307223306427 421226459633662960834959641)
        ·
          refine ⟨315919844725247220626219731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421226459633662960834959641 315919844725247220626219731)
          ·
            refine ⟨473879767087870830939329597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315919844725247220626219731 473879767087870830939329597)
            ·
              refine ⟨177704912657951561602248599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473879767087870830939329597 177704912657951561602248599)
              ·
                refine ⟨266557368986927342403372899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177704912657951561602248599 266557368986927342403372899)
                ·
                  refine ⟨399836053480391013605059349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266557368986927342403372899 399836053480391013605059349)
                  ·
                    refine ⟨18742315006893328762737157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 399836053480391013605059349 18742315006893328762737157)
                    ·
                      refine ⟨3514184063792499143013217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18742315006893328762737157 3514184063792499143013217)
                      ·
                        rfl

theorem cell23_6843849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_6843849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843849 prefixEnd_6843849 := by exact prefixLift 6843849
  have htrace : WordTrace (prefixWord ++ tailWord_6843849) baseStart_6843849 baseEnd_6843849 := by
    simpa [prefixWord, tailWord_6843849, baseEnd_6843849] using wordTrace_append hprefix tailTrace_6843849
  have hstable : (prefixWord ++ tailWord_6843849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843849).length < 2 ^ (prefixWord ++ tailWord_6843849).sum := by decide
  have hdescent : baseEnd_6843849 < baseStart_6843849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843873 : List Nat := [1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 3]
def baseStart_6843873 : Nat := 118140960795 + 6843873 * 2 ^ 59
def prefixEnd_6843873 : Nat := 4983230072969 + 3 ^ 40 * 6843873 * 2
def baseEnd_6843873 : Nat := 3514196387328207049113107

theorem tailTrace_6843873 : CollatzResearch.WordTrace tailWord_6843873 prefixEnd_6843873 3514196387328207049113107 := by
  unfold tailWord_6843873
  simp only [CollatzResearch.WordTrace]
  refine ⟨249616555134824436297368273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166411036756549624198245515 249616555134824436297368273)
  ·
    refine ⟨187212416351118327223026205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249616555134824436297368273 187212416351118327223026205)
    ·
      refine ⟨70204656131669372708634827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187212416351118327223026205 70204656131669372708634827)
      ·
        refine ⟨105306984197504059062952241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70204656131669372708634827 105306984197504059062952241)
        ·
          refine ⟨78980238148128044297214181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105306984197504059062952241 78980238148128044297214181)
          ·
            refine ⟨14808794652774008305727659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78980238148128044297214181 14808794652774008305727659)
            ·
              refine ⟨22213191979161012458591489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808794652774008305727659 22213191979161012458591489)
              ·
                refine ⟨16659893984370759343943617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22213191979161012458591489 16659893984370759343943617)
                ·
                  refine ⟨12494920488278069507957713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16659893984370759343943617 12494920488278069507957713)
                  ·
                    refine ⟨9371190366208552130968285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12494920488278069507957713 9371190366208552130968285)
                    ·
                      refine ⟨3514196387328207049113107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9371190366208552130968285 3514196387328207049113107)
                      ·
                        rfl

theorem cell23_6843873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_6843873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843873 prefixEnd_6843873 := by exact prefixLift 6843873
  have htrace : WordTrace (prefixWord ++ tailWord_6843873) baseStart_6843873 baseEnd_6843873 := by
    simpa [prefixWord, tailWord_6843873, baseEnd_6843873] using wordTrace_append hprefix tailTrace_6843873
  have hstable : (prefixWord ++ tailWord_6843873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843873).length < 2 ^ (prefixWord ++ tailWord_6843873).sum := by decide
  have hdescent : baseEnd_6843873 < baseStart_6843873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843899 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7]
def baseStart_6843899 : Nat := 118140960795 + 6843899 * 2 ^ 59
def prefixEnd_6843899 : Nat := 4983230072969 + 3 ^ 40 * 6843899 * 2
def baseEnd_6843899 : Nat := 3514209737825223947387987

theorem tailTrace_6843899 : CollatzResearch.WordTrace tailWord_6843899 prefixEnd_6843899 3514209737825223947387987 := by
  unfold tailWord_6843899
  simp only [CollatzResearch.WordTrace]
  refine ⟨249617503432730242737814751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166411668955153495158543167 249617503432730242737814751)
  ·
    refine ⟨374426255149095364106722127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249617503432730242737814751 374426255149095364106722127)
    ·
      refine ⟨561639382723643046160083191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374426255149095364106722127 561639382723643046160083191)
      ·
        refine ⟨842459074085464569240124787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561639382723643046160083191 842459074085464569240124787)
        ·
          refine ⟨1263688611128196853860187181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842459074085464569240124787 1263688611128196853860187181)
          ·
            refine ⟨473883229173073820197570193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263688611128196853860187181 473883229173073820197570193)
            ·
              refine ⟨355412421879805365148177645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473883229173073820197570193 355412421879805365148177645)
              ·
                refine ⟨133279658204927011930566617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355412421879805365148177645 133279658204927011930566617)
                ·
                  refine ⟨99959743653695258947924963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133279658204927011930566617 99959743653695258947924963)
                  ·
                    refine ⟨149939615480542888421887445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99959743653695258947924963 149939615480542888421887445)
                    ·
                      refine ⟨3514209737825223947387987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149939615480542888421887445 3514209737825223947387987)
                      ·
                        rfl

theorem cell23_6843899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_6843899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843899 prefixEnd_6843899 := by exact prefixLift 6843899
  have htrace : WordTrace (prefixWord ++ tailWord_6843899) baseStart_6843899 baseEnd_6843899 := by
    simpa [prefixWord, tailWord_6843899, baseEnd_6843899] using wordTrace_append hprefix tailTrace_6843899
  have hstable : (prefixWord ++ tailWord_6843899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843899).length < 2 ^ (prefixWord ++ tailWord_6843899).sum := by decide
  have hdescent : baseEnd_6843899 < baseStart_6843899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843919 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 2, 10]
def baseStart_6843919 : Nat := 118140960795 + 6843919 * 2 ^ 59
def prefixEnd_6843919 : Nat := 4983230072969 + 3 ^ 40 * 6843919 * 2
def baseEnd_6843919 : Nat := 1171406669146104623045965

theorem tailTrace_6843919 : CollatzResearch.WordTrace tailWord_6843919 prefixEnd_6843919 1171406669146104623045965 := by
  unfold tailWord_6843919
  simp only [CollatzResearch.WordTrace]
  refine ⟨249618232892657786153542811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166412155261771857435695207 249618232892657786153542811)
  ·
    refine ⟨374427349338986679230314217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249618232892657786153542811 374427349338986679230314217)
    ·
      refine ⟨280820512004240009422735663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374427349338986679230314217 280820512004240009422735663)
      ·
        refine ⟨421230768006360014134103495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280820512004240009422735663 421230768006360014134103495)
        ·
          refine ⟨631846152009540021201155243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 421230768006360014134103495 631846152009540021201155243)
          ·
            refine ⟨947769228014310031801732865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631846152009540021201155243 947769228014310031801732865)
            ·
              refine ⟨710826921010732523851299649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 947769228014310031801732865 710826921010732523851299649)
              ·
                refine ⟨533120190758049392888474737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 710826921010732523851299649 533120190758049392888474737)
                ·
                  refine ⟨399840143068537044666356053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533120190758049392888474737 399840143068537044666356053)
                  ·
                    refine ⟨1171406669146104623045965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 399840143068537044666356053 1171406669146104623045965)
                    ·
                      rfl

theorem cell23_6843919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 10].length) (baseStart_6843919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843919 prefixEnd_6843919 := by exact prefixLift 6843919
  have htrace : WordTrace (prefixWord ++ tailWord_6843919) baseStart_6843919 baseEnd_6843919 := by
    simpa [prefixWord, tailWord_6843919, baseEnd_6843919] using wordTrace_append hprefix tailTrace_6843919
  have hstable : (prefixWord ++ tailWord_6843919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843919).length < 2 ^ (prefixWord ++ tailWord_6843919).sum := by decide
  have hdescent : baseEnd_6843919 < baseStart_6843919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843937 : List Nat := [1, 2, 3, 2, 2, 3, 1, 4, 1, 1, 3]
def baseStart_6843937 : Nat := 118140960795 + 6843937 * 2 ^ 59
def prefixEnd_6843937 : Nat := 4983230072969 + 3 ^ 40 * 6843937 * 2
def baseEnd_6843937 : Nat := 3514229250090094798712813

theorem tailTrace_6843937 : CollatzResearch.WordTrace tailWord_6843937 prefixEnd_6843937 3514229250090094798712813 := by
  unfold tailWord_6843937
  simp only [CollatzResearch.WordTrace]
  refine ⟨249618889406592575227698065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166412592937728383485132043 249618889406592575227698065)
  ·
    refine ⟨187214167054944431420773549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249618889406592575227698065 187214167054944431420773549)
    ·
      refine ⟨70205312645604161782790081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187214167054944431420773549 70205312645604161782790081)
      ·
        refine ⟨52653984484203121337092561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70205312645604161782790081 52653984484203121337092561)
        ·
          refine ⟨39490488363152341002819421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52653984484203121337092561 39490488363152341002819421)
          ·
            refine ⟨14808933136182127876057283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39490488363152341002819421 14808933136182127876057283)
            ·
              refine ⟨22213399704273191814085925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808933136182127876057283 22213399704273191814085925)
              ·
                refine ⟨4165012444551223465141111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22213399704273191814085925 4165012444551223465141111)
                ·
                  refine ⟨6247518666826835197711667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165012444551223465141111 6247518666826835197711667)
                  ·
                    refine ⟨9371278000240252796567501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6247518666826835197711667 9371278000240252796567501)
                    ·
                      refine ⟨3514229250090094798712813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9371278000240252796567501 3514229250090094798712813)
                      ·
                        rfl

theorem cell23_6843937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 4, 1, 1, 3].length) (baseStart_6843937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843937 prefixEnd_6843937 := by exact prefixLift 6843937
  have htrace : WordTrace (prefixWord ++ tailWord_6843937) baseStart_6843937 baseEnd_6843937 := by
    simpa [prefixWord, tailWord_6843937, baseEnd_6843937] using wordTrace_append hprefix tailTrace_6843937
  have hstable : (prefixWord ++ tailWord_6843937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843937).length < 2 ^ (prefixWord ++ tailWord_6843937).sum := by decide
  have hdescent : baseEnd_6843937 < baseStart_6843937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843960 : List Nat := [2, 1, 2, 1, 4, 2, 1, 1, 5, 2, 2]
def baseStart_6843960 : Nat := 118140960795 + 6843960 * 2 ^ 59
def prefixEnd_6843960 : Nat := 4983230072969 + 3 ^ 40 * 6843960 * 2
def baseEnd_6843960 : Nat := 3514241060145148208725207

theorem tailTrace_6843960 : CollatzResearch.WordTrace tailWord_6843960 prefixEnd_6843960 3514241060145148208725207 := by
  unfold tailWord_6843960
  simp only [CollatzResearch.WordTrace]
  refine ⟨124809864142754625077892667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166413152190339500103856889 124809864142754625077892667)
  ·
    refine ⟨187214796214131937616839001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124809864142754625077892667 187214796214131937616839001)
    ·
      refine ⟨140411097160598953212629251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187214796214131937616839001 140411097160598953212629251)
      ·
        refine ⟨210616645740898429818943877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140411097160598953212629251 210616645740898429818943877)
        ·
          refine ⟨39490621076418455591051977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210616645740898429818943877 39490621076418455591051977)
          ·
            refine ⟨29617965807313841693288983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39490621076418455591051977 29617965807313841693288983)
            ·
              refine ⟨44426948710970762539933475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29617965807313841693288983 44426948710970762539933475)
              ·
                refine ⟨66640423066456143809900213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44426948710970762539933475 66640423066456143809900213)
                ·
                  refine ⟨6247539662480263482178145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66640423066456143809900213 6247539662480263482178145)
                  ·
                    refine ⟨4685654746860197611633609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247539662480263482178145 4685654746860197611633609)
                    ·
                      refine ⟨3514241060145148208725207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685654746860197611633609 3514241060145148208725207)
                      ·
                        rfl

theorem cell23_6843960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_6843960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843960 prefixEnd_6843960 := by exact prefixLift 6843960
  have htrace : WordTrace (prefixWord ++ tailWord_6843960) baseStart_6843960 baseEnd_6843960 := by
    simpa [prefixWord, tailWord_6843960, baseEnd_6843960] using wordTrace_append hprefix tailTrace_6843960
  have hstable : (prefixWord ++ tailWord_6843960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843960).length < 2 ^ (prefixWord ++ tailWord_6843960).sum := by decide
  have hdescent : baseEnd_6843960 < baseStart_6843960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843964 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 2, 3, 2]
def baseStart_6843964 : Nat := 118140960795 + 6843964 * 2 ^ 59
def prefixEnd_6843964 : Nat := 4983230072969 + 3 ^ 40 * 6843964 * 2
def baseEnd_6843964 : Nat := 3514243114067766193075189

theorem tailTrace_6843964 : CollatzResearch.WordTrace tailWord_6843964 prefixEnd_6843964 3514243114067766193075189 := by
  unfold tailWord_6843964
  simp only [CollatzResearch.WordTrace]
  refine ⟨124809937088747379419465473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166413249451663172559287297 124809937088747379419465473)
  ·
    refine ⟨93607452816560534564599105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124809937088747379419465473 93607452816560534564599105)
    ·
      refine ⟨70205589612420400923449329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93607452816560534564599105 70205589612420400923449329)
      ·
        refine ⟨52654192209315300692586997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70205589612420400923449329 52654192209315300692586997)
        ·
          refine ⟨4936330519623309439930031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52654192209315300692586997 4936330519623309439930031)
          ·
            refine ⟨7404495779434964159895047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936330519623309439930031 7404495779434964159895047)
            ·
              refine ⟨11106743669152446239842571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404495779434964159895047 11106743669152446239842571)
              ·
                refine ⟨16660115503728669359763857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11106743669152446239842571 16660115503728669359763857)
                ·
                  refine ⟨12495086627796502019822893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16660115503728669359763857 12495086627796502019822893)
                  ·
                    refine ⟨4685657485423688257433585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12495086627796502019822893 4685657485423688257433585)
                    ·
                      refine ⟨3514243114067766193075189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685657485423688257433585 3514243114067766193075189)
                      ·
                        rfl

theorem cell23_6843964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_6843964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843964 prefixEnd_6843964 := by exact prefixLift 6843964
  have htrace : WordTrace (prefixWord ++ tailWord_6843964) baseStart_6843964 baseEnd_6843964 := by
    simpa [prefixWord, tailWord_6843964, baseEnd_6843964] using wordTrace_append hprefix tailTrace_6843964
  have hstable : (prefixWord ++ tailWord_6843964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843964).length < 2 ^ (prefixWord ++ tailWord_6843964).sum := by decide
  have hdescent : baseEnd_6843964 < baseStart_6843964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843980 : List Nat := [2, 2, 1, 3, 1, 4, 1, 3, 1, 2, 3]
def baseStart_6843980 : Nat := 118140960795 + 6843980 * 2 ^ 59
def prefixEnd_6843980 : Nat := 4983230072969 + 3 ^ 40 * 6843980 * 2
def baseEnd_6843980 : Nat := 3514251329758238130475115

theorem tailTrace_6843980 : CollatzResearch.WordTrace tailWord_6843980 prefixEnd_6843980 3514251329758238130475115 := by
  unfold tailWord_6843980
  simp only [CollatzResearch.WordTrace]
  refine ⟨124810228872718396785756697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166413638496957862381008929 124810228872718396785756697)
  ·
    refine ⟨93607671654538797589317523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124810228872718396785756697 93607671654538797589317523)
    ·
      refine ⟨140411507481808196383976285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93607671654538797589317523 140411507481808196383976285)
      ·
        refine ⟨52654315305678073643991107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140411507481808196383976285 52654315305678073643991107)
        ·
          refine ⟨78981472958517110465986661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52654315305678073643991107 78981472958517110465986661)
          ·
            refine ⟨14809026179721958212372499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78981472958517110465986661 14809026179721958212372499)
            ·
              refine ⟨22213539269582937318558749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14809026179721958212372499 22213539269582937318558749)
              ·
                refine ⟨8330077226093601494459531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22213539269582937318558749 8330077226093601494459531)
                ·
                  refine ⟨12495115839140402241689297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330077226093601494459531 12495115839140402241689297)
                  ·
                    refine ⟨9371336879355301681266973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12495115839140402241689297 9371336879355301681266973)
                    ·
                      refine ⟨3514251329758238130475115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9371336879355301681266973 3514251329758238130475115)
                      ·
                        rfl

theorem cell23_6843980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_6843980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843980 prefixEnd_6843980 := by exact prefixLift 6843980
  have htrace : WordTrace (prefixWord ++ tailWord_6843980) baseStart_6843980 baseEnd_6843980 := by
    simpa [prefixWord, tailWord_6843980, baseEnd_6843980] using wordTrace_append hprefix tailTrace_6843980
  have hstable : (prefixWord ++ tailWord_6843980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843980).length < 2 ^ (prefixWord ++ tailWord_6843980).sum := by decide
  have hdescent : baseEnd_6843980 < baseStart_6843980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6843997 : List Nat := [1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6843997 : Nat := 118140960795 + 6843997 * 2 ^ 59
def prefixEnd_6843997 : Nat := 4983230072969 + 3 ^ 40 * 6843997 * 2
def baseEnd_6843997 : Nat := 3514260058929364563962537

theorem tailTrace_6843997 : CollatzResearch.WordTrace tailWord_6843997 prefixEnd_6843997 3514260058929364563962537 := by
  unfold tailWord_6843997
  simp only [CollatzResearch.WordTrace]
  refine ⟨249621077786375205474882245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166414051857583470316588163 249621077786375205474882245)
  ·
    refine ⟨46803952084945351026540421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249621077786375205474882245 46803952084945351026540421)
    ·
      refine ⟨8775741015927253317476329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46803952084945351026540421 8775741015927253317476329)
      ·
        refine ⟨6581805761945439988107247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8775741015927253317476329 6581805761945439988107247)
        ·
          refine ⟨9872708642918159982160871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6581805761945439988107247 9872708642918159982160871)
          ·
            refine ⟨14809062964377239973241307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872708642918159982160871 14809062964377239973241307)
            ·
              refine ⟨22213594446565859959861961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14809062964377239973241307 22213594446565859959861961)
              ·
                refine ⟨16660195834924394969896471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22213594446565859959861961 16660195834924394969896471)
                ·
                  refine ⟨24990293752386592454844707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16660195834924394969896471 24990293752386592454844707)
                  ·
                    refine ⟨37485440628579888682267061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24990293752386592454844707 37485440628579888682267061)
                    ·
                      refine ⟨3514260058929364563962537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37485440628579888682267061 3514260058929364563962537)
                      ·
                        rfl

theorem cell23_6843997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6843997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6843997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6843997 prefixEnd_6843997 := by exact prefixLift 6843997
  have htrace : WordTrace (prefixWord ++ tailWord_6843997) baseStart_6843997 baseEnd_6843997 := by
    simpa [prefixWord, tailWord_6843997, baseEnd_6843997] using wordTrace_append hprefix tailTrace_6843997
  have hstable : (prefixWord ++ tailWord_6843997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6843997).length < 2 ^ (prefixWord ++ tailWord_6843997).sum := by decide
  have hdescent : baseEnd_6843997 < baseStart_6843997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6843997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844010 : List Nat := [3, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3]
def baseStart_6844010 : Nat := 118140960795 + 6844010 * 2 ^ 59
def prefixEnd_6844010 : Nat := 4983230072969 + 3 ^ 40 * 6844010 * 2
def baseEnd_6844010 : Nat := 3514266734177873013099977

theorem tailTrace_6844010 : CollatzResearch.WordTrace tailWord_6844010 prefixEnd_6844010 3514266734177873013099977 := by
  unfold tailWord_6844010
  simp only [CollatzResearch.WordTrace]
  refine ⟨62405387983832027173776371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166414367956885405796736989 62405387983832027173776371)
  ·
    refine ⟨93608081975748040760664557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62405387983832027173776371 93608081975748040760664557)
    ·
      refine ⟨35103030740905515285249209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93608081975748040760664557 35103030740905515285249209)
      ·
        refine ⟨26327273055679136463936907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35103030740905515285249209 26327273055679136463936907)
        ·
          refine ⟨39490909583518704695905361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26327273055679136463936907 39490909583518704695905361)
          ·
            refine ⟨29618182187639028521929021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39490909583518704695905361 29618182187639028521929021)
            ·
              refine ⟨11106818320364635695723383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29618182187639028521929021 11106818320364635695723383)
              ·
                refine ⟨16660227480546953543585075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11106818320364635695723383 16660227480546953543585075)
                ·
                  refine ⟨24990341220820430315377613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16660227480546953543585075 24990341220820430315377613)
                  ·
                    refine ⟨9371377957807661368266605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24990341220820430315377613 9371377957807661368266605)
                    ·
                      refine ⟨3514266734177873013099977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9371377957807661368266605 3514266734177873013099977)
                      ·
                        rfl

theorem cell23_6844010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_6844010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844010 prefixEnd_6844010 := by exact prefixLift 6844010
  have htrace : WordTrace (prefixWord ++ tailWord_6844010) baseStart_6844010 baseEnd_6844010 := by
    simpa [prefixWord, tailWord_6844010, baseEnd_6844010] using wordTrace_append hprefix tailTrace_6844010
  have hstable : (prefixWord ++ tailWord_6844010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844010).length < 2 ^ (prefixWord ++ tailWord_6844010).sum := by decide
  have hdescent : baseEnd_6844010 < baseStart_6844010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844026 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 4, 6]
def baseStart_6844026 : Nat := 118140960795 + 6844026 * 2 ^ 59
def prefixEnd_6844026 : Nat := 4983230072969 + 3 ^ 40 * 6844026 * 2
def baseEnd_6844026 : Nat := 1171424983289448316833301

theorem tailTrace_6844026 : CollatzResearch.WordTrace tailWord_6844026 prefixEnd_6844026 1171424983289448316833301 := by
  unfold tailWord_6844026
  simp only [CollatzResearch.WordTrace]
  refine ⟨62405533875817535856921983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166414757002180095618458621 62405533875817535856921983)
  ·
    refine ⟨93608300813726303785382975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62405533875817535856921983 93608300813726303785382975)
    ·
      refine ⟨140412451220589455678074463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93608300813726303785382975 140412451220589455678074463)
      ·
        refine ⟨210618676830884183517111695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140412451220589455678074463 210618676830884183517111695)
        ·
          refine ⟨315928015246326275275667543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210618676830884183517111695 315928015246326275275667543)
          ·
            refine ⟨473892022869489412913501315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315928015246326275275667543 473892022869489412913501315)
            ·
              refine ⟨710838034304234119370251973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473892022869489412913501315 710838034304234119370251973)
              ·
                refine ⟨133282131432043897381922245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710838034304234119370251973 133282131432043897381922245)
                ·
                  refine ⟨24990399643508230759110421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133282131432043897381922245 24990399643508230759110421)
                  ·
                    refine ⟨1171424983289448316833301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24990399643508230759110421 1171424983289448316833301)
                    ·
                      rfl

theorem cell23_6844026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 4, 6].length) (baseStart_6844026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844026 prefixEnd_6844026 := by exact prefixLift 6844026
  have htrace : WordTrace (prefixWord ++ tailWord_6844026) baseStart_6844026 baseEnd_6844026 := by
    simpa [prefixWord, tailWord_6844026, baseEnd_6844026] using wordTrace_append hprefix tailTrace_6844026
  have hstable : (prefixWord ++ tailWord_6844026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844026).length < 2 ^ (prefixWord ++ tailWord_6844026).sum := by decide
  have hdescent : baseEnd_6844026 < baseStart_6844026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844067 : List Nat := [1, 1, 1, 4, 1, 1, 5, 3, 2, 2, 2]
def baseStart_6844067 : Nat := 118140960795 + 6844067 * 2 ^ 59
def prefixEnd_6844067 : Nat := 4983230072969 + 3 ^ 40 * 6844067 * 2
def baseEnd_6844067 : Nat := 3514296002575179290087215

theorem tailTrace_6844067 : CollatzResearch.WordTrace tailWord_6844067 prefixEnd_6844067 3514296002575179290087215 := by
  unfold tailWord_6844067
  simp only [CollatzResearch.WordTrace]
  refine ⟨249623630896121607429930455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166415753930747738286620303 249623630896121607429930455)
  ·
    refine ⟨374435446344182411144895683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249623630896121607429930455 374435446344182411144895683)
    ·
      refine ⟨561653169516273616717343525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374435446344182411144895683 561653169516273616717343525)
      ·
        refine ⟨105309969284301303134501911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 561653169516273616717343525 105309969284301303134501911)
        ·
          refine ⟨157964953926451954701752867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105309969284301303134501911 157964953926451954701752867)
          ·
            refine ⟨236947430889677932052629301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157964953926451954701752867 236947430889677932052629301)
            ·
              refine ⟨22213821645907306129933997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236947430889677932052629301 22213821645907306129933997)
              ·
                refine ⟨8330183117215239798725249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22213821645907306129933997 8330183117215239798725249)
                ·
                  refine ⟨6247637337911429849043937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8330183117215239798725249 6247637337911429849043937)
                  ·
                    refine ⟨4685728003433572386782953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247637337911429849043937 4685728003433572386782953)
                    ·
                      refine ⟨3514296002575179290087215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685728003433572386782953 3514296002575179290087215)
                      ·
                        rfl

theorem cell23_6844067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_6844067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844067 prefixEnd_6844067 := by exact prefixLift 6844067
  have htrace : WordTrace (prefixWord ++ tailWord_6844067) baseStart_6844067 baseEnd_6844067 := by
    simpa [prefixWord, tailWord_6844067, baseEnd_6844067] using wordTrace_append hprefix tailTrace_6844067
  have hstable : (prefixWord ++ tailWord_6844067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844067).length < 2 ^ (prefixWord ++ tailWord_6844067).sum := by decide
  have hdescent : baseEnd_6844067 < baseStart_6844067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844076 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_6844076 : Nat := 118140960795 + 6844076 * 2 ^ 59
def prefixEnd_6844076 : Nat := 4983230072969 + 3 ^ 40 * 6844076 * 2
def baseEnd_6844076 : Nat := 3514300623901069754874673

theorem tailTrace_6844076 : CollatzResearch.WordTrace tailWord_6844076 prefixEnd_6844076 3514300623901069754874673 := by
  unfold tailWord_6844076
  simp only [CollatzResearch.WordTrace]
  refine ⟨124811979576544500983504041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166415972768726001311338721 124811979576544500983504041)
  ·
    refine ⟨93608984682408375737628031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124811979576544500983504041 93608984682408375737628031)
    ·
      refine ⟨140413477023612563606442047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93608984682408375737628031 140413477023612563606442047)
      ·
        refine ⟨210620215535418845409663071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140413477023612563606442047 210620215535418845409663071)
        ·
          refine ⟨315930323303128268114494607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210620215535418845409663071 315930323303128268114494607)
          ·
            refine ⟨473895484954692402171741911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315930323303128268114494607 473895484954692402171741911)
            ·
              refine ⟨710843227432038603257612867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473895484954692402171741911 710843227432038603257612867)
              ·
                refine ⟨1066264841148057904886419301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710843227432038603257612867 1066264841148057904886419301)
                ·
                  refine ⟨199924657715260857166203619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1066264841148057904886419301 199924657715260857166203619)
                  ·
                    refine ⟨299886986572891285749305429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199924657715260857166203619 299886986572891285749305429)
                    ·
                      refine ⟨3514300623901069754874673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 299886986572891285749305429 3514300623901069754874673)
                      ·
                        rfl

theorem cell23_6844076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_6844076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844076 prefixEnd_6844076 := by exact prefixLift 6844076
  have htrace : WordTrace (prefixWord ++ tailWord_6844076) baseStart_6844076 baseEnd_6844076 := by
    simpa [prefixWord, tailWord_6844076, baseEnd_6844076] using wordTrace_append hprefix tailTrace_6844076
  have hstable : (prefixWord ++ tailWord_6844076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844076).length < 2 ^ (prefixWord ++ tailWord_6844076).sum := by decide
  have hdescent : baseEnd_6844076 < baseStart_6844076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844100 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_6844100 : Nat := 118140960795 + 6844100 * 2 ^ 59
def prefixEnd_6844100 : Nat := 4983230072969 + 3 ^ 40 * 6844100 * 2
def baseEnd_6844100 : Nat := 3514312947436777660974563

theorem tailTrace_6844100 : CollatzResearch.WordTrace tailWord_6844100 prefixEnd_6844100 3514312947436777660974563 := by
  unfold tailWord_6844100
  simp only [CollatzResearch.WordTrace]
  refine ⟨124812417252501027032940877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166416556336668036043921169 124812417252501027032940877)
  ·
    refine ⟨46804656469687885137352829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124812417252501027032940877 46804656469687885137352829)
    ·
      refine ⟨17551746176132956926507311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46804656469687885137352829 17551746176132956926507311)
      ·
        refine ⟨26327619264199435389760967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17551746176132956926507311 26327619264199435389760967)
        ·
          refine ⟨39491428896299153084641451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26327619264199435389760967 39491428896299153084641451)
          ·
            refine ⟨59237143344448729626962177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39491428896299153084641451 59237143344448729626962177)
            ·
              refine ⟨44427857508336547220221633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59237143344448729626962177 44427857508336547220221633)
              ·
                refine ⟨33320893131252410415166225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44427857508336547220221633 33320893131252410415166225)
                ·
                  refine ⟨24990669848439307811374669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33320893131252410415166225 24990669848439307811374669)
                  ·
                    refine ⟨9371501193164740429265501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24990669848439307811374669 9371501193164740429265501)
                    ·
                      refine ⟨3514312947436777660974563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9371501193164740429265501 3514312947436777660974563)
                      ·
                        rfl

theorem cell23_6844100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_6844100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844100 prefixEnd_6844100 := by exact prefixLift 6844100
  have htrace : WordTrace (prefixWord ++ tailWord_6844100) baseStart_6844100 baseEnd_6844100 := by
    simpa [prefixWord, tailWord_6844100, baseEnd_6844100] using wordTrace_append hprefix tailTrace_6844100
  have hstable : (prefixWord ++ tailWord_6844100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844100).length < 2 ^ (prefixWord ++ tailWord_6844100).sum := by decide
  have hdescent : baseEnd_6844100 < baseStart_6844100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844103 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 2, 5]
def baseStart_6844103 : Nat := 118140960795 + 6844103 * 2 ^ 59
def prefixEnd_6844103 : Nat := 4983230072969 + 3 ^ 40 * 6844103 * 2
def baseEnd_6844103 : Nat := 1171438162626247049745683

theorem tailTrace_6844103 : CollatzResearch.WordTrace tailWord_6844103 prefixEnd_6844103 1171438162626247049745683 := by
  unfold tailWord_6844103
  simp only [CollatzResearch.WordTrace]
  refine ⟨249624943923991185578240963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166416629282660790385493975 249624943923991185578240963)
  ·
    refine ⟨374437415885986778367361445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249624943923991185578240963 374437415885986778367361445)
    ·
      refine ⟨70207015478622520943880271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374437415885986778367361445 70207015478622520943880271)
      ·
        refine ⟨105310523217933781415820407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70207015478622520943880271 105310523217933781415820407)
        ·
          refine ⟨157965784826900672123730611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105310523217933781415820407 157965784826900672123730611)
          ·
            refine ⟨236948677240351008185595917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157965784826900672123730611 236948677240351008185595917)
            ·
              refine ⟨88855753965131628069598469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236948677240351008185595917 88855753965131628069598469)
              ·
                refine ⟨16660453868462180263049713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88855753965131628069598469 16660453868462180263049713)
                ·
                  refine ⟨12495340401346635197287285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16660453868462180263049713 12495340401346635197287285)
                  ·
                    refine ⟨1171438162626247049745683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12495340401346635197287285 1171438162626247049745683)
                    ·
                      rfl

theorem cell23_6844103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_6844103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844103 prefixEnd_6844103 := by exact prefixLift 6844103
  have htrace : WordTrace (prefixWord ++ tailWord_6844103) baseStart_6844103 baseEnd_6844103 := by
    simpa [prefixWord, tailWord_6844103, baseEnd_6844103] using wordTrace_append hprefix tailTrace_6844103
  have hstable : (prefixWord ++ tailWord_6844103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844103).length < 2 ^ (prefixWord ++ tailWord_6844103).sum := by decide
  have hdescent : baseEnd_6844103 < baseStart_6844103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844110 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2]
def baseStart_6844110 : Nat := 118140960795 + 6844110 * 2 ^ 59
def prefixEnd_6844110 : Nat := 4983230072969 + 3 ^ 40 * 6844110 * 2
def baseEnd_6844110 : Nat := 3514318082243322621849517

theorem tailTrace_6844110 : CollatzResearch.WordTrace tailWord_6844110 prefixEnd_6844110 3514318082243322621849517 := by
  unfold tailWord_6844110
  simp only [CollatzResearch.WordTrace]
  refine ⟨31203149904370728221718223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166416799489977217182497189 31203149904370728221718223)
  ·
    refine ⟨46804724856556092332577335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31203149904370728221718223 46804724856556092332577335)
    ·
      refine ⟨70207087284834138498866003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46804724856556092332577335 70207087284834138498866003)
      ·
        refine ⟨105310630927251207748299005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70207087284834138498866003 105310630927251207748299005)
        ·
          refine ⟨39491486597719202905612127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105310630927251207748299005 39491486597719202905612127)
          ·
            refine ⟨59237229896578804358418191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39491486597719202905612127 59237229896578804358418191)
            ·
              refine ⟨88855844844868206537627287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59237229896578804358418191 88855844844868206537627287)
              ·
                refine ⟨133283767267302309806440931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88855844844868206537627287 133283767267302309806440931)
                ·
                  refine ⟨199925650900953464709661397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133283767267302309806440931 199925650900953464709661397)
                  ·
                    refine ⟨4685757442991096829132689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 199925650900953464709661397 4685757442991096829132689)
                    ·
                      refine ⟨3514318082243322621849517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685757442991096829132689 3514318082243322621849517)
                      ·
                        rfl

theorem cell23_6844110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 1, 7, 2].length) (baseStart_6844110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844110 prefixEnd_6844110 := by exact prefixLift 6844110
  have htrace : WordTrace (prefixWord ++ tailWord_6844110) baseStart_6844110 baseEnd_6844110 := by
    simpa [prefixWord, tailWord_6844110, baseEnd_6844110] using wordTrace_append hprefix tailTrace_6844110
  have hstable : (prefixWord ++ tailWord_6844110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844110).length < 2 ^ (prefixWord ++ tailWord_6844110).sum := by decide
  have hdescent : baseEnd_6844110 < baseStart_6844110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844113 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 5]
def baseStart_6844113 : Nat := 118140960795 + 6844113 * 2 ^ 59
def prefixEnd_6844113 : Nat := 4983230072969 + 3 ^ 40 * 6844113 * 2
def baseEnd_6844113 : Nat := 3514319622685286110112003

theorem tailTrace_6844113 : CollatzResearch.WordTrace tailWord_6844113 prefixEnd_6844113 3514319622685286110112003 := by
  unfold tailWord_6844113
  simp only [CollatzResearch.WordTrace]
  refine ⟨249625308653954957286104993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166416872435969971524069995 249625308653954957286104993)
  ·
    refine ⟨187218981490466217964578745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249625308653954957286104993 187218981490466217964578745)
    ·
      refine ⟨140414236117849663473434059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187218981490466217964578745 140414236117849663473434059)
      ·
        refine ⟨210621354176774495210151089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140414236117849663473434059 210621354176774495210151089)
        ·
          refine ⟨157966015632580871407613317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210621354176774495210151089 157966015632580871407613317)
          ·
            refine ⟨29618627931108913388927497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157966015632580871407613317 29618627931108913388927497)
            ·
              refine ⟨22213970948331685041695623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29618627931108913388927497 22213970948331685041695623)
              ·
                refine ⟨33320956422497527562543435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22213970948331685041695623 33320956422497527562543435)
                ·
                  refine ⟨49981434633746291343815153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33320956422497527562543435 49981434633746291343815153)
                  ·
                    refine ⟨37486075975309718507861365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49981434633746291343815153 37486075975309718507861365)
                    ·
                      refine ⟨3514319622685286110112003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37486075975309718507861365 3514319622685286110112003)
                      ·
                        rfl

theorem cell23_6844113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_6844113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844113 prefixEnd_6844113 := by exact prefixLift 6844113
  have htrace : WordTrace (prefixWord ++ tailWord_6844113) baseStart_6844113 baseEnd_6844113 := by
    simpa [prefixWord, tailWord_6844113, baseEnd_6844113] using wordTrace_append hprefix tailTrace_6844113
  have hstable : (prefixWord ++ tailWord_6844113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844113).length < 2 ^ (prefixWord ++ tailWord_6844113).sum := by decide
  have hdescent : baseEnd_6844113 < baseStart_6844113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844140 : List Nat := [2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_6844140 : Nat := 118140960795 + 6844140 * 2 ^ 59
def prefixEnd_6844140 : Nat := 4983230072969 + 3 ^ 40 * 6844140 * 2
def baseEnd_6844140 : Nat := 3514333486662957504474379

theorem tailTrace_6844140 : CollatzResearch.WordTrace tailWord_6844140 prefixEnd_6844140 3514333486662957504474379 := by
  unfold tailWord_6844140
  simp only [CollatzResearch.WordTrace]
  refine ⟨124813146712428570448668937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166417528949904760598225249 124813146712428570448668937)
  ·
    refine ⟨93609860034321427836501703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124813146712428570448668937 93609860034321427836501703)
    ·
      refine ⟨140414790051482141754752555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93609860034321427836501703 140414790051482141754752555)
      ·
        refine ⟨210622185077223212632128833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140414790051482141754752555 210622185077223212632128833)
        ·
          refine ⟨157966638807917409474096625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210622185077223212632128833 157966638807917409474096625)
          ·
            refine ⟨118474979105938057105572469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157966638807917409474096625 118474979105938057105572469)
            ·
              refine ⟨11107029291181692853647419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118474979105938057105572469 11107029291181692853647419)
              ·
                refine ⟨16660543936772539280471129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11107029291181692853647419 16660543936772539280471129)
                ·
                  refine ⟨12495407952579404460353347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16660543936772539280471129 12495407952579404460353347)
                  ·
                    refine ⟨18743111928869106690530021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12495407952579404460353347 18743111928869106690530021)
                    ·
                      refine ⟨3514333486662957504474379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18743111928869106690530021 3514333486662957504474379)
                      ·
                        rfl

theorem cell23_6844140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_6844140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844140 prefixEnd_6844140 := by exact prefixLift 6844140
  have htrace : WordTrace (prefixWord ++ tailWord_6844140) baseStart_6844140 baseEnd_6844140 := by
    simpa [prefixWord, tailWord_6844140, baseEnd_6844140] using wordTrace_append hprefix tailTrace_6844140
  have hstable : (prefixWord ++ tailWord_6844140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844140).length < 2 ^ (prefixWord ++ tailWord_6844140).sum := by decide
  have hdescent : baseEnd_6844140 < baseStart_6844140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844244 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_6844244 : Nat := 118140960795 + 6844244 * 2 ^ 59
def prefixEnd_6844244 : Nat := 4983230072969 + 3 ^ 40 * 6844244 * 2
def baseEnd_6844244 : Nat := 1171462296217008365857967

theorem tailTrace_6844244 : CollatzResearch.WordTrace tailWord_6844244 prefixEnd_6844244 1171462296217008365857967 := by
  unfold tailWord_6844244
  simp only [CollatzResearch.WordTrace]
  refine ⟨124815043308240183329561893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166420057744320244439415857 124815043308240183329561893)
  ·
    refine ⟨23402820620295034374292855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124815043308240183329561893 23402820620295034374292855)
    ·
      refine ⟨35104230930442551561439283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23402820620295034374292855 35104230930442551561439283)
      ·
        refine ⟨52656346395663827342158925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35104230930442551561439283 52656346395663827342158925)
        ·
          refine ⟨19746129898373935253309597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52656346395663827342158925 19746129898373935253309597)
          ·
            refine ⟨7404798711890225719991099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19746129898373935253309597 7404798711890225719991099)
            ·
              refine ⟨11107198067835338579986649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404798711890225719991099 11107198067835338579986649)
              ·
                refine ⟨8330398550876503934989987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11107198067835338579986649 8330398550876503934989987)
                ·
                  refine ⟨12495597826314755902484981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330398550876503934989987 12495597826314755902484981)
                  ·
                    refine ⟨1171462296217008365857967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12495597826314755902484981 1171462296217008365857967)
                    ·
                      rfl

theorem cell23_6844244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_6844244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844244 prefixEnd_6844244 := by exact prefixLift 6844244
  have htrace : WordTrace (prefixWord ++ tailWord_6844244) baseStart_6844244 baseEnd_6844244 := by
    simpa [prefixWord, tailWord_6844244, baseEnd_6844244] using wordTrace_append hprefix tailTrace_6844244
  have hstable : (prefixWord ++ tailWord_6844244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844244).length < 2 ^ (prefixWord ++ tailWord_6844244).sum := by decide
  have hdescent : baseEnd_6844244 < baseStart_6844244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844247 : List Nat := [1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_6844247 : Nat := 118140960795 + 6844247 * 2 ^ 59
def prefixEnd_6844247 : Nat := 4983230072969 + 3 ^ 40 * 6844247 * 2
def baseEnd_6844247 : Nat := 3514388429092988585836387

theorem tailTrace_6844247 : CollatzResearch.WordTrace tailWord_6844247 prefixEnd_6844247 3514388429092988585836387 := by
  unfold tailWord_6844247
  simp only [CollatzResearch.WordTrace]
  refine ⟨249630196035469498171482995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166420130690312998780988663 249630196035469498171482995)
  ·
    refine ⟨374445294053204247257224493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249630196035469498171482995 374445294053204247257224493)
    ·
      refine ⟨140416985269951592721459185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374445294053204247257224493 140416985269951592721459185)
      ·
        refine ⟨105312738952463694541094389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140416985269951592721459185 105312738952463694541094389)
        ·
          refine ⟨9873069276793471363227599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105312738952463694541094389 9873069276793471363227599)
          ·
            refine ⟨14809603915190207044841399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9873069276793471363227599 14809603915190207044841399)
            ·
              refine ⟨22214405872785310567262099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14809603915190207044841399 22214405872785310567262099)
              ·
                refine ⟨33321608809177965850893149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22214405872785310567262099 33321608809177965850893149)
                ·
                  refine ⟨12495603303441737194084931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33321608809177965850893149 12495603303441737194084931)
                  ·
                    refine ⟨18743404955162605791127397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12495603303441737194084931 18743404955162605791127397)
                    ·
                      refine ⟨3514388429092988585836387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18743404955162605791127397 3514388429092988585836387)
                      ·
                        rfl

theorem cell23_6844247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_6844247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844247 prefixEnd_6844247 := by exact prefixLift 6844247
  have htrace : WordTrace (prefixWord ++ tailWord_6844247) baseStart_6844247 baseEnd_6844247 := by
    simpa [prefixWord, tailWord_6844247, baseEnd_6844247] using wordTrace_append hprefix tailTrace_6844247
  have hstable : (prefixWord ++ tailWord_6844247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844247).length < 2 ^ (prefixWord ++ tailWord_6844247).sum := by decide
  have hdescent : baseEnd_6844247 < baseStart_6844247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844264 : List Nat := [2, 1, 4, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_6844264 : Nat := 118140960795 + 6844264 * 2 ^ 59
def prefixEnd_6844264 : Nat := 4983230072969 + 3 ^ 40 * 6844264 * 2
def baseEnd_6844264 : Nat := 3514397158264115019323809

theorem tailTrace_6844264 : CollatzResearch.WordTrace tailWord_6844264 prefixEnd_6844264 3514397158264115019323809 := by
  unfold tailWord_6844264
  simp only [CollatzResearch.WordTrace]
  refine ⟨124815408038203955037425923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166420544050938606716567897 124815408038203955037425923)
  ·
    refine ⟨187223112057305932556138885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124815408038203955037425923 187223112057305932556138885)
    ·
      refine ⟨35104333510744862354276041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187223112057305932556138885 35104333510744862354276041)
      ·
        refine ⟨26328250133058646765707031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35104333510744862354276041 26328250133058646765707031)
        ·
          refine ⟨39492375199587970148560547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26328250133058646765707031 39492375199587970148560547)
          ·
            refine ⟨59238562799381955222840821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39492375199587970148560547 59238562799381955222840821)
            ·
              refine ⟨5553615262442058302141327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59238562799381955222840821 5553615262442058302141327)
              ·
                refine ⟨8330422893663087453211991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5553615262442058302141327 8330422893663087453211991)
                ·
                  refine ⟨12495634340494631179817987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330422893663087453211991 12495634340494631179817987)
                  ·
                    refine ⟨18743451510741946769726981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12495634340494631179817987 18743451510741946769726981)
                    ·
                      refine ⟨3514397158264115019323809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18743451510741946769726981 3514397158264115019323809)
                      ·
                        rfl

theorem cell23_6844264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_6844264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844264 prefixEnd_6844264 := by exact prefixLift 6844264
  have htrace : WordTrace (prefixWord ++ tailWord_6844264) baseStart_6844264 baseEnd_6844264 := by
    simpa [prefixWord, tailWord_6844264, baseEnd_6844264] using wordTrace_append hprefix tailTrace_6844264
  have hstable : (prefixWord ++ tailWord_6844264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844264).length < 2 ^ (prefixWord ++ tailWord_6844264).sum := by decide
  have hdescent : baseEnd_6844264 < baseStart_6844264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844270 : List Nat := [4, 1, 2, 3, 1, 12]
def baseStart_6844270 : Nat := 118140960795 + 6844270 * 2 ^ 59
def prefixEnd_6844270 : Nat := 4983230072969 + 3 ^ 40 * 6844270 * 2
def baseEnd_6844270 : Nat := 14462552424477539077567

theorem tailTrace_6844270 : CollatzResearch.WordTrace tailWord_6844270 prefixEnd_6844270 14462552424477539077567 := by
  unfold tailWord_6844270
  simp only [CollatzResearch.WordTrace]
  refine ⟨31203879364298271637446283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166420689942924115399713509 31203879364298271637446283)
  ·
    refine ⟨46805819046447407456169425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31203879364298271637446283 46805819046447407456169425)
    ·
      refine ⟨35104364284835555592127069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46805819046447407456169425 35104364284835555592127069)
      ·
        refine ⟨13164136606813333347047651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35104364284835555592127069 13164136606813333347047651)
        ·
          refine ⟨19746204910220000020571477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13164136606813333347047651 19746204910220000020571477)
          ·
            refine ⟨14462552424477539077567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19746204910220000020571477 14462552424477539077567)
            ·
              rfl

theorem cell23_6844270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 12].length) (baseStart_6844270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844270 prefixEnd_6844270 := by exact prefixLift 6844270
  have htrace : WordTrace (prefixWord ++ tailWord_6844270) baseStart_6844270 baseEnd_6844270 := by
    simpa [prefixWord, tailWord_6844270, baseEnd_6844270] using wordTrace_append hprefix tailTrace_6844270
  have hstable : (prefixWord ++ tailWord_6844270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844270).length < 2 ^ (prefixWord ++ tailWord_6844270).sum := by decide
  have hdescent : baseEnd_6844270 < baseStart_6844270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844281 : List Nat := [1, 2, 1, 3, 2, 2, 3, 4, 1, 2, 2]
def baseStart_6844281 : Nat := 118140960795 + 6844281 * 2 ^ 59
def prefixEnd_6844281 : Nat := 4983230072969 + 3 ^ 40 * 6844281 * 2
def baseEnd_6844281 : Nat := 3514405887435241452811231

theorem tailTrace_6844281 : CollatzResearch.WordTrace tailWord_6844281 prefixEnd_6844281 3514405887435241452811231 := by
  unfold tailWord_6844281
  simp only [CollatzResearch.WordTrace]
  refine ⟨249631436117346321978220697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166420957411564214652147131 249631436117346321978220697)
  ·
    refine ⟨187223577088009741483665523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249631436117346321978220697 187223577088009741483665523)
    ·
      refine ⟨280835365632014612225498285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187223577088009741483665523 280835365632014612225498285)
      ·
        refine ⟨105313262112005479584561857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280835365632014612225498285 105313262112005479584561857)
        ·
          refine ⟨78984946584004109688421393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105313262112005479584561857 78984946584004109688421393)
          ·
            refine ⟨59238709938003082266316045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78984946584004109688421393 59238709938003082266316045)
            ·
              refine ⟨22214516226751155849868517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59238709938003082266316045 22214516226751155849868517)
              ·
                refine ⟨4165221792515841721850347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22214516226751155849868517 4165221792515841721850347)
                ·
                  refine ⟨6247832688773762582775521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165221792515841721850347 6247832688773762582775521)
                  ·
                    refine ⟨4685874516580321937081641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247832688773762582775521 4685874516580321937081641)
                    ·
                      refine ⟨3514405887435241452811231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685874516580321937081641 3514405887435241452811231)
                      ·
                        rfl

theorem cell23_6844281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_6844281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844281 prefixEnd_6844281 := by exact prefixLift 6844281
  have htrace : WordTrace (prefixWord ++ tailWord_6844281) baseStart_6844281 baseEnd_6844281 := by
    simpa [prefixWord, tailWord_6844281, baseEnd_6844281] using wordTrace_append hprefix tailTrace_6844281
  have hstable : (prefixWord ++ tailWord_6844281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844281).length < 2 ^ (prefixWord ++ tailWord_6844281).sum := by decide
  have hdescent : baseEnd_6844281 < baseStart_6844281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844297 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 3]
def baseStart_6844297 : Nat := 118140960795 + 6844297 * 2 ^ 59
def prefixEnd_6844297 : Nat := 4983230072969 + 3 ^ 40 * 6844297 * 2
def baseEnd_6844297 : Nat := 3514414103125713390211157

theorem tailTrace_6844297 : CollatzResearch.WordTrace tailWord_6844297 prefixEnd_6844297 3514414103125713390211157 := by
  unfold tailWord_6844297
  simp only [CollatzResearch.WordTrace]
  refine ⟨249632019685288356710803145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166421346456858904473868763 249632019685288356710803145)
  ·
    refine ⟨187224014763966267533102359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249632019685288356710803145 187224014763966267533102359)
    ·
      refine ⟨280836022145949401299653539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187224014763966267533102359 280836022145949401299653539)
      ·
        refine ⟨421254033218924101949480309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280836022145949401299653539 421254033218924101949480309)
        ·
          refine ⟨39492565614274134557763779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421254033218924101949480309 39492565614274134557763779)
          ·
            refine ⟨59238848421411201836645669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39492565614274134557763779 59238848421411201836645669)
            ·
              refine ⟨11107284079014600344371063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59238848421411201836645669 11107284079014600344371063)
              ·
                refine ⟨16660926118521900516556595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11107284079014600344371063 16660926118521900516556595)
                ·
                  refine ⟨24991389177782850774834893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16660926118521900516556595 24991389177782850774834893)
                  ·
                    refine ⟨9371770941668569040563085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24991389177782850774834893 9371770941668569040563085)
                    ·
                      refine ⟨3514414103125713390211157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9371770941668569040563085 3514414103125713390211157)
                      ·
                        rfl

theorem cell23_6844297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_6844297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844297 prefixEnd_6844297 := by exact prefixLift 6844297
  have htrace : WordTrace (prefixWord ++ tailWord_6844297) baseStart_6844297 baseEnd_6844297 := by
    simpa [prefixWord, tailWord_6844297, baseEnd_6844297] using wordTrace_append hprefix tailTrace_6844297
  have hstable : (prefixWord ++ tailWord_6844297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844297).length < 2 ^ (prefixWord ++ tailWord_6844297).sum := by decide
  have hdescent : baseEnd_6844297 < baseStart_6844297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844318 : List Nat := [4, 3, 1, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_6844318 : Nat := 118140960795 + 6844318 * 2 ^ 59
def prefixEnd_6844318 : Nat := 4983230072969 + 3 ^ 40 * 6844318 * 2
def baseEnd_6844318 : Nat := 3514424886219457808048561

theorem tailTrace_6844318 : CollatzResearch.WordTrace tailWord_6844318 prefixEnd_6844318 3514424886219457808048561 := by
  unfold tailWord_6844318
  simp only [CollatzResearch.WordTrace]
  refine ⟨31204098202276534662164701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166421857078808184864878405 31204098202276534662164701)
  ·
    refine ⟨11701536825853700498311763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31204098202276534662164701 11701536825853700498311763)
    ·
      refine ⟨17552305238780550747467645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11701536825853700498311763 17552305238780550747467645)
      ·
        refine ⟨6582114464542706530300367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17552305238780550747467645 6582114464542706530300367)
        ·
          refine ⟨9873171696814059795450551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6582114464542706530300367 9873171696814059795450551)
          ·
            refine ⟨14809757545221089693175827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9873171696814059795450551 14809757545221089693175827)
            ·
              refine ⟨22214636317831634539763741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14809757545221089693175827 22214636317831634539763741)
              ·
                refine ⟨8330488619186862952411403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22214636317831634539763741 8330488619186862952411403)
                ·
                  refine ⟨12495732928780294428617105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330488619186862952411403 12495732928780294428617105)
                  ·
                    refine ⟨9371799696585220821462829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12495732928780294428617105 9371799696585220821462829)
                    ·
                      refine ⟨3514424886219457808048561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9371799696585220821462829 3514424886219457808048561)
                      ·
                        rfl

theorem cell23_6844318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_6844318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844318 prefixEnd_6844318 := by exact prefixLift 6844318
  have htrace : WordTrace (prefixWord ++ tailWord_6844318) baseStart_6844318 baseEnd_6844318 := by
    simpa [prefixWord, tailWord_6844318, baseEnd_6844318] using wordTrace_append hprefix tailTrace_6844318
  have hstable : (prefixWord ++ tailWord_6844318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844318).length < 2 ^ (prefixWord ++ tailWord_6844318).sum := by decide
  have hdescent : baseEnd_6844318 < baseStart_6844318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844348 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6844348 : Nat := 118140960795 + 6844348 * 2 ^ 59
def prefixEnd_6844348 : Nat := 4983230072969 + 3 ^ 40 * 6844348 * 2
def baseEnd_6844348 : Nat := 3514440290639092690673423

theorem tailTrace_6844348 : CollatzResearch.WordTrace tailWord_6844348 prefixEnd_6844348 3514440290639092690673423 := by
  unfold tailWord_6844348
  simp only [CollatzResearch.WordTrace]
  refine ⟨124816939904051796210454849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166422586538735728280606465 124816939904051796210454849)
  ·
    refine ⟨93612704928038847157841137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124816939904051796210454849 93612704928038847157841137)
    ·
      refine ⟨70209528696029135368380853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93612704928038847157841137 70209528696029135368380853)
      ·
        refine ⟨6582143315252731440785705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70209528696029135368380853 6582143315252731440785705)
        ·
          refine ⟨4936607486439548580589279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6582143315252731440785705 4936607486439548580589279)
          ·
            refine ⟨7404911229659322870883919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936607486439548580589279 7404911229659322870883919)
            ·
              refine ⟨11107366844488984306325879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404911229659322870883919 11107366844488984306325879)
              ·
                refine ⟨16661050266733476459488819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11107366844488984306325879 16661050266733476459488819)
                ·
                  refine ⟨24991575400100214689233229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16661050266733476459488819 24991575400100214689233229)
                  ·
                    refine ⟨9371840775037580508462461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24991575400100214689233229 9371840775037580508462461)
                    ·
                      refine ⟨3514440290639092690673423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9371840775037580508462461 3514440290639092690673423)
                      ·
                        rfl

theorem cell23_6844348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6844348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844348 prefixEnd_6844348 := by exact prefixLift 6844348
  have htrace : WordTrace (prefixWord ++ tailWord_6844348) baseStart_6844348 baseEnd_6844348 := by
    simpa [prefixWord, tailWord_6844348, baseEnd_6844348] using wordTrace_append hprefix tailTrace_6844348
  have hstable : (prefixWord ++ tailWord_6844348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844348).length < 2 ^ (prefixWord ++ tailWord_6844348).sum := by decide
  have hdescent : baseEnd_6844348 < baseStart_6844348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844400 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_6844400 : Nat := 118140960795 + 6844400 * 2 ^ 59
def prefixEnd_6844400 : Nat := 4983230072969 + 3 ^ 40 * 6844400 * 2
def baseEnd_6844400 : Nat := 3514466991633126487223183

theorem tailTrace_6844400 : CollatzResearch.WordTrace tailWord_6844400 prefixEnd_6844400 3514466991633126487223183 := by
  unfold tailWord_6844400
  simp only [CollatzResearch.WordTrace]
  refine ⟨124817888201957602650901327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166423850935943470201201769 124817888201957602650901327)
  ·
    refine ⟨187226832302936403976351991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124817888201957602650901327 187226832302936403976351991)
    ·
      refine ⟨280840248454404605964527987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187226832302936403976351991 280840248454404605964527987)
      ·
        refine ⟨421260372681606908946791981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280840248454404605964527987 421260372681606908946791981)
        ·
          refine ⟨157972639755602590855046993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421260372681606908946791981 157972639755602590855046993)
          ·
            refine ⟨118479479816701943141285245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157972639755602590855046993 118479479816701943141285245)
            ·
              refine ⟨44429804931263228677981967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118479479816701943141285245 44429804931263228677981967)
              ·
                refine ⟨66644707396894843016972951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44429804931263228677981967 66644707396894843016972951)
                ·
                  refine ⟨99967061095342264525459427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66644707396894843016972951 99967061095342264525459427)
                  ·
                    refine ⟨149950591643013396788189141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99967061095342264525459427 149950591643013396788189141)
                    ·
                      refine ⟨3514466991633126487223183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149950591643013396788189141 3514466991633126487223183)
                      ·
                        rfl

theorem cell23_6844400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_6844400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844400 prefixEnd_6844400 := by exact prefixLift 6844400
  have htrace : WordTrace (prefixWord ++ tailWord_6844400) baseStart_6844400 baseEnd_6844400 := by
    simpa [prefixWord, tailWord_6844400, baseEnd_6844400] using wordTrace_append hprefix tailTrace_6844400
  have hstable : (prefixWord ++ tailWord_6844400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844400).length < 2 ^ (prefixWord ++ tailWord_6844400).sum := by decide
  have hdescent : baseEnd_6844400 < baseStart_6844400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844422 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6844422 : Nat := 118140960795 + 6844422 * 2 ^ 59
def prefixEnd_6844422 : Nat := 4983230072969 + 3 ^ 40 * 6844422 * 2
def baseEnd_6844422 : Nat := 3514478288207525401148083

theorem tailTrace_6844422 : CollatzResearch.WordTrace tailWord_6844422 prefixEnd_6844422 3514478288207525401148083 := by
  unfold tailWord_6844422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7801143087807359470596985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166424385873223668706069013 7801143087807359470596985)
  ·
    refine ⟨5850857315855519602947739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7801143087807359470596985 5850857315855519602947739)
    ·
      refine ⟨8776285973783279404421609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850857315855519602947739 8776285973783279404421609)
      ·
        refine ⟨6582214480337459553316207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8776285973783279404421609 6582214480337459553316207)
        ·
          refine ⟨9873321720506189329974311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6582214480337459553316207 9873321720506189329974311)
          ·
            refine ⟨14809982580759283994961467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9873321720506189329974311 14809982580759283994961467)
            ·
              refine ⟨22214973871138925992442201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14809982580759283994961467 22214973871138925992442201)
              ·
                refine ⟨16661230403354194494331651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22214973871138925992442201 16661230403354194494331651)
                ·
                  refine ⟨24991845605031291741497477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16661230403354194494331651 24991845605031291741497477)
                  ·
                    refine ⟨4685971050943367201530777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24991845605031291741497477 4685971050943367201530777)
                    ·
                      refine ⟨3514478288207525401148083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4685971050943367201530777 3514478288207525401148083)
                      ·
                        rfl

theorem cell23_6844422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6844422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844422 prefixEnd_6844422 := by exact prefixLift 6844422
  have htrace : WordTrace (prefixWord ++ tailWord_6844422) baseStart_6844422 baseEnd_6844422 := by
    simpa [prefixWord, tailWord_6844422, baseEnd_6844422] using wordTrace_append hprefix tailTrace_6844422
  have hstable : (prefixWord ++ tailWord_6844422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844422).length < 2 ^ (prefixWord ++ tailWord_6844422).sum := by decide
  have hdescent : baseEnd_6844422 < baseStart_6844422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844444 : List Nat := [2, 2, 3, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_6844444 : Nat := 118140960795 + 6844444 * 2 ^ 59
def prefixEnd_6844444 : Nat := 4983230072969 + 3 ^ 40 * 6844444 * 2
def baseEnd_6844444 : Nat := 3514489584781924315072981

theorem tailTrace_6844444 : CollatzResearch.WordTrace tailWord_6844444 prefixEnd_6844444 3514489584781924315072981 := by
  unfold tailWord_6844444
  simp only [CollatzResearch.WordTrace]
  refine ⟨124818690607877900408202193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166424920810503867210936257 124818690607877900408202193)
  ·
    refine ⟨93614017955908425306151645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124818690607877900408202193 93614017955908425306151645)
    ·
      refine ⟨35105256733465659489806867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93614017955908425306151645 35105256733465659489806867)
      ·
        refine ⟨52657885100198489234710301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35105256733465659489806867 52657885100198489234710301)
        ·
          refine ⟨19746706912574433463016363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52657885100198489234710301 19746706912574433463016363)
          ·
            refine ⟨29620060368861650194524545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19746706912574433463016363 29620060368861650194524545)
            ·
              refine ⟨22215045276646237645893409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29620060368861650194524545 22215045276646237645893409)
              ·
                refine ⟨16661283957484678234420057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22215045276646237645893409 16661283957484678234420057)
                ·
                  refine ⟨12495962968113508675815043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16661283957484678234420057 12495962968113508675815043)
                  ·
                    refine ⟨18743944452170263013722565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12495962968113508675815043 18743944452170263013722565)
                    ·
                      refine ⟨3514489584781924315072981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18743944452170263013722565 3514489584781924315072981)
                      ·
                        rfl

theorem cell23_6844444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_6844444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844444 prefixEnd_6844444 := by exact prefixLift 6844444
  have htrace : WordTrace (prefixWord ++ tailWord_6844444) baseStart_6844444 baseEnd_6844444 := by
    simpa [prefixWord, tailWord_6844444, baseEnd_6844444] using wordTrace_append hprefix tailTrace_6844444
  have hstable : (prefixWord ++ tailWord_6844444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844444).length < 2 ^ (prefixWord ++ tailWord_6844444).sum := by decide
  have hdescent : baseEnd_6844444 < baseStart_6844444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844467 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 6]
def baseStart_6844467 : Nat := 118140960795 + 6844467 * 2 ^ 59
def prefixEnd_6844467 : Nat := 4983230072969 + 3 ^ 40 * 6844467 * 2
def baseEnd_6844467 : Nat := 390500154981886413898375

theorem tailTrace_6844467 : CollatzResearch.WordTrace tailWord_6844467 prefixEnd_6844467 390500154981886413898375 := by
  unfold tailWord_6844467
  simp only [CollatzResearch.WordTrace]
  refine ⟨249638220094672475744491655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166425480063114983829661103 249638220094672475744491655)
  ·
    refine ⟨374457330142008713616737483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249638220094672475744491655 374457330142008713616737483)
    ·
      refine ⟨561685995213013070425106225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374457330142008713616737483 561685995213013070425106225)
      ·
        refine ⟨421264496409759802818829669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561685995213013070425106225 421264496409759802818829669)
        ·
          refine ⟨78987093076829963028530563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421264496409759802818829669 78987093076829963028530563)
          ·
            refine ⟨118480639615244944542795845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78987093076829963028530563 118480639615244944542795845)
            ·
              refine ⟨22215119927858427101774221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118480639615244944542795845 22215119927858427101774221)
              ·
                refine ⟨8330669972946910163165333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22215119927858427101774221 8330669972946910163165333)
                ·
                  refine ⟨390500154981886413898375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8330669972946910163165333 390500154981886413898375)
                  ·
                    rfl

theorem cell23_6844467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 6].length) (baseStart_6844467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844467 prefixEnd_6844467 := by exact prefixLift 6844467
  have htrace : WordTrace (prefixWord ++ tailWord_6844467) baseStart_6844467 baseEnd_6844467 := by
    simpa [prefixWord, tailWord_6844467, baseEnd_6844467] using wordTrace_append hprefix tailTrace_6844467
  have hstable : (prefixWord ++ tailWord_6844467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844467).length < 2 ^ (prefixWord ++ tailWord_6844467).sum := by decide
  have hdescent : baseEnd_6844467 < baseStart_6844467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844478 : List Nat := [4, 2, 1, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_6844478 : Nat := 118140960795 + 6844478 * 2 ^ 59
def prefixEnd_6844478 : Nat := 4983230072969 + 3 ^ 40 * 6844478 * 2
def baseEnd_6844478 : Nat := 3514507043124177182047825

theorem tailTrace_6844478 : CollatzResearch.WordTrace tailWord_6844478 prefixEnd_6844478 3514507043124177182047825 := by
  unfold tailWord_6844478
  simp only [CollatzResearch.WordTrace]
  refine ⟨31204827662204078077892761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166425747531755083082094725 31204827662204078077892761)
  ·
    refine ⟨23403620746653058558419571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31204827662204078077892761 23403620746653058558419571)
    ·
      refine ⟨35105431119979587837629357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23403620746653058558419571 35105431119979587837629357)
      ·
        refine ⟨13164536669992345439111009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35105431119979587837629357 13164536669992345439111009)
        ·
          refine ⟨9873402502494259079333257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13164536669992345439111009 9873402502494259079333257)
          ·
            refine ⟨7405051876870694309499943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9873402502494259079333257 7405051876870694309499943)
            ·
              refine ⟨11107577815306041464249915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7405051876870694309499943 11107577815306041464249915)
              ·
                refine ⟨16661366722959062196374873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11107577815306041464249915 16661366722959062196374873)
                ·
                  refine ⟨12496025042219296647281155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16661366722959062196374873 12496025042219296647281155)
                  ·
                    refine ⟨18744037563328944970921733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12496025042219296647281155 18744037563328944970921733)
                    ·
                      refine ⟨3514507043124177182047825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18744037563328944970921733 3514507043124177182047825)
                      ·
                        rfl

theorem cell23_6844478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_6844478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844478 prefixEnd_6844478 := by exact prefixLift 6844478
  have htrace : WordTrace (prefixWord ++ tailWord_6844478) baseStart_6844478 baseEnd_6844478 := by
    simpa [prefixWord, tailWord_6844478, baseEnd_6844478] using wordTrace_append hprefix tailTrace_6844478
  have hstable : (prefixWord ++ tailWord_6844478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844478).length < 2 ^ (prefixWord ++ tailWord_6844478).sum := by decide
  have hdescent : baseEnd_6844478 < baseStart_6844478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844481 : List Nat := [1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 3]
def baseStart_6844481 : Nat := 118140960795 + 6844481 * 2 ^ 59
def prefixEnd_6844481 : Nat := 4983230072969 + 3 ^ 40 * 6844481 * 2
def baseEnd_6844481 : Nat := 3514508583566140670310311

theorem tailTrace_6844481 : CollatzResearch.WordTrace tailWord_6844481 prefixEnd_6844481 3514508583566140670310311 := by
  unfold tailWord_6844481
  simp only [CollatzResearch.WordTrace]
  refine ⟨249638730716621756135501297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166425820477747837423667531 249638730716621756135501297)
  ·
    refine ⟨187229048037466317101625973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249638730716621756135501297 187229048037466317101625973)
    ·
      refine ⟨17552723253512467228277435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187229048037466317101625973 17552723253512467228277435)
      ·
        refine ⟨26329084880268700842416153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17552723253512467228277435 26329084880268700842416153)
        ·
          refine ⟨19746813660201525631812115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26329084880268700842416153 19746813660201525631812115)
          ·
            refine ⟨29620220490302288447718173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19746813660201525631812115 29620220490302288447718173)
            ·
              refine ⟨11107582683863358167894315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29620220490302288447718173 11107582683863358167894315)
              ·
                refine ⟨16661374025795037251841473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11107582683863358167894315 16661374025795037251841473)
                ·
                  refine ⟨12496030519346277938881105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16661374025795037251841473 12496030519346277938881105)
                  ·
                    refine ⟨9372022889509708454160829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12496030519346277938881105 9372022889509708454160829)
                    ·
                      refine ⟨3514508583566140670310311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9372022889509708454160829 3514508583566140670310311)
                      ·
                        rfl

theorem cell23_6844481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_6844481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844481 prefixEnd_6844481 := by exact prefixLift 6844481
  have htrace : WordTrace (prefixWord ++ tailWord_6844481) baseStart_6844481 baseEnd_6844481 := by
    simpa [prefixWord, tailWord_6844481, baseEnd_6844481] using wordTrace_append hprefix tailTrace_6844481
  have hstable : (prefixWord ++ tailWord_6844481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844481).length < 2 ^ (prefixWord ++ tailWord_6844481).sum := by decide
  have hdescent : baseEnd_6844481 < baseStart_6844481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844551 : List Nat := [1, 1, 4, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_6844551 : Nat := 118140960795 + 6844551 * 2 ^ 59
def prefixEnd_6844551 : Nat := 4983230072969 + 3 ^ 40 * 6844551 * 2
def baseEnd_6844551 : Nat := 3514544527211955396434989

theorem tailTrace_6844551 : CollatzResearch.WordTrace tailWord_6844551 prefixEnd_6844551 3514544527211955396434989 := by
  unfold tailWord_6844551
  simp only [CollatzResearch.WordTrace]
  refine ⟨249641283826368158090549507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166427522550912105393699671 249641283826368158090549507)
  ·
    refine ⟨374461925739552237135824261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249641283826368158090549507 374461925739552237135824261)
    ·
      refine ⟨70211611076166044462967049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374461925739552237135824261 70211611076166044462967049)
      ·
        refine ⟨52658708307124533347225287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70211611076166044462967049 52658708307124533347225287)
        ·
          refine ⟨78988062460686800020837931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52658708307124533347225287 78988062460686800020837931)
          ·
            refine ⟨118482093691030200031256897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78988062460686800020837931 118482093691030200031256897)
            ·
              refine ⟨88861570268272650023442673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118482093691030200031256897 88861570268272650023442673)
              ·
                refine ⟨66646177701204487517582005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88861570268272650023442673 66646177701204487517582005)
                ·
                  refine ⟨6248079159487920704773313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66646177701204487517582005 6248079159487920704773313)
                  ·
                    refine ⟨4686059369615940528579985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6248079159487920704773313 4686059369615940528579985)
                    ·
                      refine ⟨3514544527211955396434989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686059369615940528579985 3514544527211955396434989)
                      ·
                        rfl

theorem cell23_6844551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_6844551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844551 prefixEnd_6844551 := by exact prefixLift 6844551
  have htrace : WordTrace (prefixWord ++ tailWord_6844551) baseStart_6844551 baseEnd_6844551 := by
    simpa [prefixWord, tailWord_6844551, baseEnd_6844551] using wordTrace_append hprefix tailTrace_6844551
  have hstable : (prefixWord ++ tailWord_6844551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844551).length < 2 ^ (prefixWord ++ tailWord_6844551).sum := by decide
  have hdescent : baseEnd_6844551 < baseStart_6844551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844554 : List Nat := [3, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_6844554 : Nat := 118140960795 + 6844554 * 2 ^ 59
def prefixEnd_6844554 : Nat := 4983230072969 + 3 ^ 40 * 6844554 * 2
def baseEnd_6844554 : Nat := 3514546067653918884697475

theorem tailTrace_6844554 : CollatzResearch.WordTrace tailWord_6844554 prefixEnd_6844554 3514546067653918884697475 := by
  unfold tailWord_6844554
  simp only [CollatzResearch.WordTrace]
  refine ⟨62410348311339322400727179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166427595496904859735272477 62410348311339322400727179)
  ·
    refine ⟨93615522467008983601090769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62410348311339322400727179 93615522467008983601090769)
    ·
      refine ⟨70211641850256737700818077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93615522467008983601090769 70211641850256737700818077)
      ·
        refine ⟨26329365693846276637806779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70211641850256737700818077 26329365693846276637806779)
        ·
          refine ⟨39494048540769414956710169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26329365693846276637806779 39494048540769414956710169)
          ·
            refine ⟨29620536405577061217532627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39494048540769414956710169 29620536405577061217532627)
            ·
              refine ⟨44430804608365591826298941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29620536405577061217532627 44430804608365591826298941)
              ·
                refine ⟨16661551728137096934862103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44430804608365591826298941 16661551728137096934862103)
                ·
                  refine ⟨24992327592205645402293155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16661551728137096934862103 24992327592205645402293155)
                  ·
                    refine ⟨37488491388308468103439733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24992327592205645402293155 37488491388308468103439733)
                    ·
                      refine ⟨3514546067653918884697475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37488491388308468103439733 3514546067653918884697475)
                      ·
                        rfl

theorem cell23_6844554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_6844554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844554 prefixEnd_6844554 := by exact prefixLift 6844554
  have htrace : WordTrace (prefixWord ++ tailWord_6844554) baseStart_6844554 baseEnd_6844554 := by
    simpa [prefixWord, tailWord_6844554, baseEnd_6844554] using wordTrace_append hprefix tailTrace_6844554
  have hstable : (prefixWord ++ tailWord_6844554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844554).length < 2 ^ (prefixWord ++ tailWord_6844554).sum := by decide
  have hdescent : baseEnd_6844554 < baseStart_6844554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844578 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_6844578 : Nat := 118140960795 + 6844578 * 2 ^ 59
def prefixEnd_6844578 : Nat := 4983230072969 + 3 ^ 40 * 6844578 * 2
def baseEnd_6844578 : Nat := 1171519463729875596932455

theorem tailTrace_6844578 : CollatzResearch.WordTrace tailWord_6844578 prefixEnd_6844578 1171519463729875596932455 := by
  unfold tailWord_6844578
  simp only [CollatzResearch.WordTrace]
  refine ⟨62410567149317585425445597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166428179064846894467854925 62410567149317585425445597)
  ·
    refine ⟨23403962680994094534542099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62410567149317585425445597 23403962680994094534542099)
    ·
      refine ⟨35105944021491141801813149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23403962680994094534542099 35105944021491141801813149)
      ·
        refine ⟨13164729008059178175679931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35105944021491141801813149 13164729008059178175679931)
        ·
          refine ⟨19747093512088767263519897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13164729008059178175679931 19747093512088767263519897)
          ·
            refine ⟨14810320134066575447639923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19747093512088767263519897 14810320134066575447639923)
            ·
              refine ⟨22215480201099863171459885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14810320134066575447639923 22215480201099863171459885)
              ·
                refine ⟨8330805075412448689297457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22215480201099863171459885 8330805075412448689297457)
                ·
                  refine ⟨6248103806559336516973093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8330805075412448689297457 6248103806559336516973093)
                  ·
                    refine ⟨1171519463729875596932455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6248103806559336516973093 1171519463729875596932455)
                    ·
                      rfl

theorem cell23_6844578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_6844578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844578 prefixEnd_6844578 := by exact prefixLift 6844578
  have htrace : WordTrace (prefixWord ++ tailWord_6844578) baseStart_6844578 baseEnd_6844578 := by
    simpa [prefixWord, tailWord_6844578, baseEnd_6844578] using wordTrace_append hprefix tailTrace_6844578
  have hstable : (prefixWord ++ tailWord_6844578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844578).length < 2 ^ (prefixWord ++ tailWord_6844578).sum := by decide
  have hdescent : baseEnd_6844578 < baseStart_6844578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844618 : List Nat := [3, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_6844618 : Nat := 118140960795 + 6844618 * 2 ^ 59
def prefixEnd_6844618 : Nat := 4983230072969 + 3 ^ 40 * 6844618 * 2
def baseEnd_6844618 : Nat := 3514578930415806634297181

theorem tailTrace_6844618 : CollatzResearch.WordTrace tailWord_6844618 prefixEnd_6844618 3514578930415806634297181 := by
  unfold tailWord_6844618
  simp only [CollatzResearch.WordTrace]
  refine ⟨62410931879281357133309627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166429151678083619022159005 62410931879281357133309627)
  ·
    refine ⟨93616397818922035699964441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62410931879281357133309627 93616397818922035699964441)
    ·
      refine ⟨70212298364191526774973331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93616397818922035699964441 70212298364191526774973331)
      ·
        refine ⟨105318447546287290162459997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70212298364191526774973331 105318447546287290162459997)
        ·
          refine ⟨39494417829857733810922499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105318447546287290162459997 39494417829857733810922499)
          ·
            refine ⟨59241626744786600716383749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39494417829857733810922499 59241626744786600716383749)
            ·
              refine ⟨11107805014647487634321953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59241626744786600716383749 11107805014647487634321953)
              ·
                refine ⟨8330853760985615725741465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11107805014647487634321953 8330853760985615725741465)
                ·
                  refine ⟨6248140320739211794306099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8330853760985615725741465 6248140320739211794306099)
                  ·
                    refine ⟨9372210481108817691459149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6248140320739211794306099 9372210481108817691459149)
                    ·
                      refine ⟨3514578930415806634297181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9372210481108817691459149 3514578930415806634297181)
                      ·
                        rfl

theorem cell23_6844618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_6844618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844618 prefixEnd_6844618 := by exact prefixLift 6844618
  have htrace : WordTrace (prefixWord ++ tailWord_6844618) baseStart_6844618 baseEnd_6844618 := by
    simpa [prefixWord, tailWord_6844618, baseEnd_6844618] using wordTrace_append hprefix tailTrace_6844618
  have hstable : (prefixWord ++ tailWord_6844618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844618).length < 2 ^ (prefixWord ++ tailWord_6844618).sum := by decide
  have hdescent : baseEnd_6844618 < baseStart_6844618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844644 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_6844644 : Nat := 118140960795 + 6844644 * 2 ^ 59
def prefixEnd_6844644 : Nat := 4983230072969 + 3 ^ 40 * 6844644 * 2
def baseEnd_6844644 : Nat := 3514592280912823532572061

theorem tailTrace_6844644 : CollatzResearch.WordTrace tailWord_6844644 prefixEnd_6844644 3514592280912823532572061 := by
  unfold tailWord_6844644
  simp only [CollatzResearch.WordTrace]
  refine ⟨124822337907515617486842493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166429783876687489982456657 124822337907515617486842493)
  ·
    refine ⟨46808376715318356557565935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124822337907515617486842493 46808376715318356557565935)
    ·
      refine ⟨70212565072977534836348903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46808376715318356557565935 70212565072977534836348903)
      ·
        refine ⟨105318847609466302254523355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70212565072977534836348903 105318847609466302254523355)
        ·
          refine ⟨157978271414199453381785033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105318847609466302254523355 157978271414199453381785033)
          ·
            refine ⟨118483703560649590036338775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157978271414199453381785033 118483703560649590036338775)
            ·
              refine ⟨177725555340974385054508163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118483703560649590036338775 177725555340974385054508163)
              ·
                refine ⟨266588333011461577581762245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177725555340974385054508163 266588333011461577581762245)
                ·
                  refine ⟨49985312439649045796580421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 266588333011461577581762245 49985312439649045796580421)
                  ·
                    refine ⟨9372246082434196086858829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49985312439649045796580421 9372246082434196086858829)
                    ·
                      refine ⟨3514592280912823532572061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9372246082434196086858829 3514592280912823532572061)
                      ·
                        rfl

theorem cell23_6844644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_6844644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844644 prefixEnd_6844644 := by exact prefixLift 6844644
  have htrace : WordTrace (prefixWord ++ tailWord_6844644) baseStart_6844644 baseEnd_6844644 := by
    simpa [prefixWord, tailWord_6844644, baseEnd_6844644] using wordTrace_append hprefix tailTrace_6844644
  have hstable : (prefixWord ++ tailWord_6844644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844644).length < 2 ^ (prefixWord ++ tailWord_6844644).sum := by decide
  have hdescent : baseEnd_6844644 < baseStart_6844644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844654 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_6844654 : Nat := 118140960795 + 6844654 * 2 ^ 59
def prefixEnd_6844654 : Nat := 4983230072969 + 3 ^ 40 * 6844654 * 2
def baseEnd_6844654 : Nat := 3514597415719368493447015

theorem tailTrace_6844654 : CollatzResearch.WordTrace tailWord_6844654 prefixEnd_6844654 3514597415719368493447015 := by
  unfold tailWord_6844654
  simp only [CollatzResearch.WordTrace]
  refine ⟨31205630068124375835193627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166430027029996671121032677 31205630068124375835193627)
  ·
    refine ⟨46808445102186563752790441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31205630068124375835193627 46808445102186563752790441)
    ·
      refine ⟨35106333826639922814592831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46808445102186563752790441 35106333826639922814592831)
      ·
        refine ⟨52659500739959884221889247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35106333826639922814592831 52659500739959884221889247)
        ·
          refine ⟨78989251109939826332833871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52659500739959884221889247 78989251109939826332833871)
          ·
            refine ⟨118483876664909739499250807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78989251109939826332833871 118483876664909739499250807)
            ·
              refine ⟨177725814997364609248876211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118483876664909739499250807 177725814997364609248876211)
              ·
                refine ⟨266588722496046913873314317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177725814997364609248876211 266588722496046913873314317)
                ·
                  refine ⟨99970770936017592702492869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266588722496046913873314317 99970770936017592702492869)
                  ·
                    refine ⟨18744519550503298631717413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99970770936017592702492869 18744519550503298631717413)
                    ·
                      refine ⟨3514597415719368493447015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18744519550503298631717413 3514597415719368493447015)
                      ·
                        rfl

theorem cell23_6844654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_6844654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844654 prefixEnd_6844654 := by exact prefixLift 6844654
  have htrace : WordTrace (prefixWord ++ tailWord_6844654) baseStart_6844654 baseEnd_6844654 := by
    simpa [prefixWord, tailWord_6844654, baseEnd_6844654] using wordTrace_append hprefix tailTrace_6844654
  have hstable : (prefixWord ++ tailWord_6844654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844654).length < 2 ^ (prefixWord ++ tailWord_6844654).sum := by decide
  have hdescent : baseEnd_6844654 < baseStart_6844654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844658 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_6844658 : Nat := 118140960795 + 6844658 * 2 ^ 59
def prefixEnd_6844658 : Nat := 4983230072969 + 3 ^ 40 * 6844658 * 2
def baseEnd_6844658 : Nat := 3514599469641986477796997

theorem tailTrace_6844658 : CollatzResearch.WordTrace tailWord_6844658 prefixEnd_6844658 3514599469641986477796997 := by
  unfold tailWord_6844658
  simp only [CollatzResearch.WordTrace]
  refine ⟨62411296609245128841173657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166430124291320343576463085 62411296609245128841173657)
  ·
    refine ⟨46808472456933846630880243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62411296609245128841173657 46808472456933846630880243)
    ·
      refine ⟨70212708685400769946320365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46808472456933846630880243 70212708685400769946320365)
      ·
        refine ⟨26329765757025288729870137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70212708685400769946320365 26329765757025288729870137)
        ·
          refine ⟨19747324317768966547402603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26329765757025288729870137 19747324317768966547402603)
          ·
            refine ⟨29620986476653449821103905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19747324317768966547402603 29620986476653449821103905)
            ·
              refine ⟨22215739857490087365827929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29620986476653449821103905 22215739857490087365827929)
              ·
                refine ⟨16661804893117565524370947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22215739857490087365827929 16661804893117565524370947)
                ·
                  refine ⟨24992707339676348286556421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16661804893117565524370947 24992707339676348286556421)
                  ·
                    refine ⟨4686132626189315303729329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24992707339676348286556421 4686132626189315303729329)
                    ·
                      refine ⟨3514599469641986477796997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686132626189315303729329 3514599469641986477796997)
                      ·
                        rfl

theorem cell23_6844658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_6844658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844658 prefixEnd_6844658 := by exact prefixLift 6844658
  have htrace : WordTrace (prefixWord ++ tailWord_6844658) baseStart_6844658 baseEnd_6844658 := by
    simpa [prefixWord, tailWord_6844658, baseEnd_6844658] using wordTrace_append hprefix tailTrace_6844658
  have hstable : (prefixWord ++ tailWord_6844658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844658).length < 2 ^ (prefixWord ++ tailWord_6844658).sum := by decide
  have hdescent : baseEnd_6844658 < baseStart_6844658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844681 : List Nat := [1, 2, 1, 1, 3, 4, 2, 4, 5]
def baseStart_6844681 : Nat := 118140960795 + 6844681 * 2 ^ 59
def prefixEnd_6844681 : Nat := 4983230072969 + 3 ^ 40 * 6844681 * 2
def baseEnd_6844681 : Nat := 390512364410782209756599

theorem tailTrace_6844681 : CollatzResearch.WordTrace tailWord_6844681 prefixEnd_6844681 390512364410782209756599 := by
  unfold tailWord_6844681
  simp only [CollatzResearch.WordTrace]
  refine ⟨249646025315897190292781897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166430683543931460195187931 249646025315897190292781897)
  ·
    refine ⟨187234518986922892719586423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249646025315897190292781897 187234518986922892719586423)
    ·
      refine ⟨280851778480384339079379635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187234518986922892719586423 280851778480384339079379635)
      ·
        refine ⟨421277667720576508619069453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280851778480384339079379635 421277667720576508619069453)
        ·
          refine ⟨157979125395216190732151045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421277667720576508619069453 157979125395216190732151045)
          ·
            refine ⟨29621086011603035762278321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157979125395216190732151045 29621086011603035762278321)
            ·
              refine ⟨22215814508702276821708741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29621086011603035762278321 22215814508702276821708741)
              ·
                refine ⟨4165465220381676904070389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22215814508702276821708741 4165465220381676904070389)
                ·
                  refine ⟨390512364410782209756599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4165465220381676904070389 390512364410782209756599)
                  ·
                    rfl

theorem cell23_6844681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 5].length) (baseStart_6844681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844681 prefixEnd_6844681 := by exact prefixLift 6844681
  have htrace : WordTrace (prefixWord ++ tailWord_6844681) baseStart_6844681 baseEnd_6844681 := by
    simpa [prefixWord, tailWord_6844681, baseEnd_6844681] using wordTrace_append hprefix tailTrace_6844681
  have hstable : (prefixWord ++ tailWord_6844681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844681).length < 2 ^ (prefixWord ++ tailWord_6844681).sum := by decide
  have hdescent : baseEnd_6844681 < baseStart_6844681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844744 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6844744 : Nat := 118140960795 + 6844744 * 2 ^ 59
def prefixEnd_6844744 : Nat := 4983230072969 + 3 ^ 40 * 6844744 * 2
def baseEnd_6844744 : Nat := 3514643628978273141321601

theorem tailTrace_6844744 : CollatzResearch.WordTrace tailWord_6844744 prefixEnd_6844744 3514643628978273141321601 := by
  unfold tailWord_6844744
  simp only [CollatzResearch.WordTrace]
  refine ⟨124824161557334476026162643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166432215409779301368216857 124824161557334476026162643)
  ·
    refine ⟨187236242336001714039243965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124824161557334476026162643 187236242336001714039243965)
    ·
      refine ⟨70213590876000642764716487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187236242336001714039243965 70213590876000642764716487)
      ·
        refine ⟨105320386314000964147074731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70213590876000642764716487 105320386314000964147074731)
        ·
          refine ⟨157980579471001446220612097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105320386314000964147074731 157980579471001446220612097)
          ·
            refine ⟨118485434603251084665459073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157980579471001446220612097 118485434603251084665459073)
            ·
              refine ⟨88864075952438313499094305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118485434603251084665459073 88864075952438313499094305)
              ·
                refine ⟨66648056964328735124320729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88864075952438313499094305 66648056964328735124320729)
                ·
                  refine ⟨49986042723246551343240547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66648056964328735124320729 49986042723246551343240547)
                  ·
                    refine ⟨74979064084869827014860821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49986042723246551343240547 74979064084869827014860821)
                    ·
                      refine ⟨3514643628978273141321601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74979064084869827014860821 3514643628978273141321601)
                      ·
                        rfl

theorem cell23_6844744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6844744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844744 prefixEnd_6844744 := by exact prefixLift 6844744
  have htrace : WordTrace (prefixWord ++ tailWord_6844744) baseStart_6844744 baseEnd_6844744 := by
    simpa [prefixWord, tailWord_6844744, baseEnd_6844744] using wordTrace_append hprefix tailTrace_6844744
  have hstable : (prefixWord ++ tailWord_6844744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844744).length < 2 ^ (prefixWord ++ tailWord_6844744).sum := by decide
  have hdescent : baseEnd_6844744 < baseStart_6844744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844794 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_6844794 : Nat := 118140960795 + 6844794 * 2 ^ 59
def prefixEnd_6844794 : Nat := 4983230072969 + 3 ^ 40 * 6844794 * 2
def baseEnd_6844794 : Nat := 3514669303010997945696371

theorem tailTrace_6844794 : CollatzResearch.WordTrace tailWord_6844794 prefixEnd_6844794 3514669303010997945696371 := by
  unfold tailWord_6844794
  simp only [CollatzResearch.WordTrace]
  refine ⟨62412536691121952647911359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166433431176325207061096957 62412536691121952647911359)
  ·
    refine ⟨93618805036682928971867039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62412536691121952647911359 93618805036682928971867039)
    ·
      refine ⟨140428207555024393457800559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93618805036682928971867039 140428207555024393457800559)
      ·
        refine ⟨210642311332536590186700839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140428207555024393457800559 210642311332536590186700839)
        ·
          refine ⟨315963466998804885280051259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210642311332536590186700839 315963466998804885280051259)
          ·
            refine ⟨473945200498207327920076889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315963466998804885280051259 473945200498207327920076889)
            ·
              refine ⟨355458900373655495940057667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473945200498207327920076889 355458900373655495940057667)
              ·
                refine ⟨533188350560483243910086501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 355458900373655495940057667 533188350560483243910086501)
                ·
                  refine ⟨99972815730090608233141219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 533188350560483243910086501 99972815730090608233141219)
                  ·
                    refine ⟨149959223595135912349711829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99972815730090608233141219 149959223595135912349711829)
                    ·
                      refine ⟨3514669303010997945696371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149959223595135912349711829 3514669303010997945696371)
                      ·
                        rfl

theorem cell23_6844794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_6844794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844794 prefixEnd_6844794 := by exact prefixLift 6844794
  have htrace : WordTrace (prefixWord ++ tailWord_6844794) baseStart_6844794 baseEnd_6844794 := by
    simpa [prefixWord, tailWord_6844794, baseEnd_6844794] using wordTrace_append hprefix tailTrace_6844794
  have hstable : (prefixWord ++ tailWord_6844794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844794).length < 2 ^ (prefixWord ++ tailWord_6844794).sum := by decide
  have hdescent : baseEnd_6844794 < baseStart_6844794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844808 : List Nat := [2, 1, 3, 3, 1, 1, 2, 2, 1, 5, 2]
def baseStart_6844808 : Nat := 118140960795 + 6844808 * 2 ^ 59
def prefixEnd_6844808 : Nat := 4983230072969 + 3 ^ 40 * 6844808 * 2
def baseEnd_6844808 : Nat := 3514676491740160890921307

theorem tailTrace_6844808 : CollatzResearch.WordTrace tailWord_6844808 prefixEnd_6844808 3514676491740160890921307 := by
  unfold tailWord_6844808
  simp only [CollatzResearch.WordTrace]
  refine ⟨124825328693218545491327539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166433771590958060655103385 124825328693218545491327539)
  ·
    refine ⟨187237993039827818236991309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124825328693218545491327539 187237993039827818236991309)
    ·
      refine ⟨70214247389935431838871741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187237993039827818236991309 70214247389935431838871741)
      ·
        refine ⟨26330342771225786939576903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70214247389935431838871741 26330342771225786939576903)
        ·
          refine ⟨39495514156838680409365355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26330342771225786939576903 39495514156838680409365355)
          ·
            refine ⟨59243271235258020614048033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39495514156838680409365355 59243271235258020614048033)
            ·
              refine ⟨44432453426443515460536025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59243271235258020614048033 44432453426443515460536025)
              ·
                refine ⟨33324340069832636595402019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44432453426443515460536025 33324340069832636595402019)
                ·
                  refine ⟨49986510104748954893103029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33324340069832636595402019 49986510104748954893103029)
                  ·
                    refine ⟨4686235322320214521228409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49986510104748954893103029 4686235322320214521228409)
                    ·
                      refine ⟨3514676491740160890921307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686235322320214521228409 3514676491740160890921307)
                      ·
                        rfl

theorem cell23_6844808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_6844808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844808 prefixEnd_6844808 := by exact prefixLift 6844808
  have htrace : WordTrace (prefixWord ++ tailWord_6844808) baseStart_6844808 baseEnd_6844808 := by
    simpa [prefixWord, tailWord_6844808, baseEnd_6844808] using wordTrace_append hprefix tailTrace_6844808
  have hstable : (prefixWord ++ tailWord_6844808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844808).length < 2 ^ (prefixWord ++ tailWord_6844808).sum := by decide
  have hdescent : baseEnd_6844808 < baseStart_6844808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844831 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 1, 6]
def baseStart_6844831 : Nat := 118140960795 + 6844831 * 2 ^ 59
def prefixEnd_6844831 : Nat := 4983230072969 + 3 ^ 40 * 6844831 * 2
def baseEnd_6844831 : Nat := 1171562767265071433644567

theorem tailTrace_6844831 : CollatzResearch.WordTrace tailWord_6844831 prefixEnd_6844831 1171562767265071433644567 := by
  unfold tailWord_6844831
  simp only [CollatzResearch.WordTrace]
  refine ⟨249651496265353765910742347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166434330843569177273828231 249651496265353765910742347)
  ·
    refine ⟨374477244398030648866113521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249651496265353765910742347 374477244398030648866113521)
    ·
      refine ⟨280857933298522986649585141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374477244398030648866113521 280857933298522986649585141)
      ·
        refine ⟨26330431246736529998398607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280857933298522986649585141 26330431246736529998398607)
        ·
          refine ⟨39495646870104794997597911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26330431246736529998398607 39495646870104794997597911)
          ·
            refine ⟨59243470305157192496396867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39495646870104794997597911 59243470305157192496396867)
            ·
              refine ⟨88865205457735788744595301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59243470305157192496396867 88865205457735788744595301)
              ·
                refine ⟨16662226023325460389611619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88865205457735788744595301 16662226023325460389611619)
                ·
                  refine ⟨24993339034988190584417429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16662226023325460389611619 24993339034988190584417429)
                  ·
                    refine ⟨1171562767265071433644567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24993339034988190584417429 1171562767265071433644567)
                    ·
                      rfl

theorem cell23_6844831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_6844831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844831 prefixEnd_6844831 := by exact prefixLift 6844831
  have htrace : WordTrace (prefixWord ++ tailWord_6844831) baseStart_6844831 baseEnd_6844831 := by
    simpa [prefixWord, tailWord_6844831, baseEnd_6844831] using wordTrace_append hprefix tailTrace_6844831
  have hstable : (prefixWord ++ tailWord_6844831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844831).length < 2 ^ (prefixWord ++ tailWord_6844831).sum := by decide
  have hdescent : baseEnd_6844831 < baseStart_6844831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844832 : List Nat := [2, 1, 1, 4, 1, 4, 2, 3, 1, 1, 3]
def baseStart_6844832 : Nat := 118140960795 + 6844832 * 2 ^ 59
def prefixEnd_6844832 : Nat := 4983230072969 + 3 ^ 40 * 6844832 * 2
def baseEnd_6844832 : Nat := 3514688815275868797021197

theorem tailTrace_6844832 : CollatzResearch.WordTrace tailWord_6844832 prefixEnd_6844832 3514688815275868797021197 := by
  unfold tailWord_6844832
  simp only [CollatzResearch.WordTrace]
  refine ⟨124825766369175071540764375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166434355158900095387685833 124825766369175071540764375)
  ·
    refine ⟨187238649553762607311146563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124825766369175071540764375 187238649553762607311146563)
    ·
      refine ⟨280857974330643910966719845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187238649553762607311146563 280857974330643910966719845)
      ·
        refine ⟨52660870186995733306259971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280857974330643910966719845 52660870186995733306259971)
        ·
          refine ⟨78991305280493599959389957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52660870186995733306259971 78991305280493599959389957)
          ·
            refine ⟨14810869740092549992385617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78991305280493599959389957 14810869740092549992385617)
            ·
              refine ⟨11108152305069412494289213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14810869740092549992385617 11108152305069412494289213)
              ·
                refine ⟨4165557114401029685358455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11108152305069412494289213 4165557114401029685358455)
                ·
                  refine ⟨6248335671601544528037683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165557114401029685358455 6248335671601544528037683)
                  ·
                    refine ⟨9372503507402316792056525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6248335671601544528037683 9372503507402316792056525)
                    ·
                      refine ⟨3514688815275868797021197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9372503507402316792056525 3514688815275868797021197)
                      ·
                        rfl

theorem cell23_6844832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_6844832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844832 prefixEnd_6844832 := by exact prefixLift 6844832
  have htrace : WordTrace (prefixWord ++ tailWord_6844832) baseStart_6844832 baseEnd_6844832 := by
    simpa [prefixWord, tailWord_6844832, baseEnd_6844832] using wordTrace_append hprefix tailTrace_6844832
  have hstable : (prefixWord ++ tailWord_6844832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844832).length < 2 ^ (prefixWord ++ tailWord_6844832).sum := by decide
  have hdescent : baseEnd_6844832 < baseStart_6844832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844835 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 1, 5]
def baseStart_6844835 : Nat := 118140960795 + 6844835 * 2 ^ 59
def prefixEnd_6844835 : Nat := 4983230072969 + 3 ^ 40 * 6844835 * 2
def baseEnd_6844835 : Nat := 1171563451905944095094561

theorem tailTrace_6844835 : CollatzResearch.WordTrace tailWord_6844835 prefixEnd_6844835 1171563451905944095094561 := by
  unfold tailWord_6844835
  simp only [CollatzResearch.WordTrace]
  refine ⟨249651642157339274593887959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166434428104892849729258639 249651642157339274593887959)
  ·
    refine ⟨374477463236008911890831939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249651642157339274593887959 374477463236008911890831939)
    ·
      refine ⟨561716194854013367836247909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374477463236008911890831939 561716194854013367836247909)
      ·
        refine ⟨105321786535127506469296483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 561716194854013367836247909 105321786535127506469296483)
        ·
          refine ⟨157982679802691259703944725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105321786535127506469296483 157982679802691259703944725)
          ·
            refine ⟨7405438115751152798622409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157982679802691259703944725 7405438115751152798622409)
            ·
              refine ⟨5554078586813364598966807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7405438115751152798622409 5554078586813364598966807)
              ·
                refine ⟨8331117880220046898450211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5554078586813364598966807 8331117880220046898450211)
                ·
                  refine ⟨12496676820330070347675317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8331117880220046898450211 12496676820330070347675317)
                  ·
                    refine ⟨1171563451905944095094561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12496676820330070347675317 1171563451905944095094561)
                    ·
                      rfl

theorem cell23_6844835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 1, 5].length) (baseStart_6844835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844835 prefixEnd_6844835 := by exact prefixLift 6844835
  have htrace : WordTrace (prefixWord ++ tailWord_6844835) baseStart_6844835 baseEnd_6844835 := by
    simpa [prefixWord, tailWord_6844835, baseEnd_6844835] using wordTrace_append hprefix tailTrace_6844835
  have hstable : (prefixWord ++ tailWord_6844835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844835).length < 2 ^ (prefixWord ++ tailWord_6844835).sum := by decide
  have hdescent : baseEnd_6844835 < baseStart_6844835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844855 : List Nat := [1, 1, 3, 1, 3, 3, 1, 3, 3, 2, 2]
def baseStart_6844855 : Nat := 118140960795 + 6844855 * 2 ^ 59
def prefixEnd_6844855 : Nat := 4983230072969 + 3 ^ 40 * 6844855 * 2
def baseEnd_6844855 : Nat := 3514700625330922207033591

theorem tailTrace_6844855 : CollatzResearch.WordTrace tailWord_6844855 prefixEnd_6844855 3514700625330922207033591 := by
  unfold tailWord_6844855
  simp only [CollatzResearch.WordTrace]
  refine ⟨249652371617266818009616019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166434914411511212006410679 249652371617266818009616019)
  ·
    refine ⟨374478557425900227014424029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249652371617266818009616019 374478557425900227014424029)
    ·
      refine ⟨140429459034712585130409011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374478557425900227014424029 140429459034712585130409011)
      ·
        refine ⟨210644188552068877695613517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140429459034712585130409011 210644188552068877695613517)
        ·
          refine ⟨78991570707025829135855069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210644188552068877695613517 78991570707025829135855069)
          ·
            refine ⟨29621839015134685925945651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78991570707025829135855069 29621839015134685925945651)
            ·
              refine ⟨44432758522702028888918477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29621839015134685925945651 44432758522702028888918477)
              ·
                refine ⟨16662284446013260833344429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44432758522702028888918477 16662284446013260833344429)
                ·
                  refine ⟨6248356667254972812504161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16662284446013260833344429 6248356667254972812504161)
                  ·
                    refine ⟨4686267500441229609378121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6248356667254972812504161 4686267500441229609378121)
                    ·
                      refine ⟨3514700625330922207033591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686267500441229609378121 3514700625330922207033591)
                      ·
                        rfl

theorem cell23_6844855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_6844855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844855 prefixEnd_6844855 := by exact prefixLift 6844855
  have htrace : WordTrace (prefixWord ++ tailWord_6844855) baseStart_6844855 baseEnd_6844855 := by
    simpa [prefixWord, tailWord_6844855, baseEnd_6844855] using wordTrace_append hprefix tailTrace_6844855
  have hstable : (prefixWord ++ tailWord_6844855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844855).length < 2 ^ (prefixWord ++ tailWord_6844855).sum := by decide
  have hdescent : baseEnd_6844855 < baseStart_6844855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844906 : List Nat := [3, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_6844906 : Nat := 118140960795 + 6844906 * 2 ^ 59
def prefixEnd_6844906 : Nat := 4983230072969 + 3 ^ 40 * 6844906 * 2
def baseEnd_6844906 : Nat := 3514726812844301507495857

theorem tailTrace_6844906 : CollatzResearch.WordTrace tailWord_6844906 prefixEnd_6844906 3514726812844301507495857 := by
  unfold tailWord_6844906
  simp only [CollatzResearch.WordTrace]
  refine ⟨62413557935020513429930643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166436154493388035813148381 62413557935020513429930643)
  ·
    refine ⟨93620336902530770144895965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62413557935020513429930643 93620336902530770144895965)
    ·
      refine ⟨35107626338449038804335987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93620336902530770144895965 35107626338449038804335987)
      ·
        refine ⟨52661439507673558206503981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35107626338449038804335987 52661439507673558206503981)
        ·
          refine ⟨19748039815377584327438993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52661439507673558206503981 19748039815377584327438993)
          ·
            refine ⟨14811029861533188245579245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19748039815377584327438993 14811029861533188245579245)
            ·
              refine ⟨5554136198074945592092217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14811029861533188245579245 5554136198074945592092217)
              ·
                refine ⟨4165602148556209194069163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5554136198074945592092217 4165602148556209194069163)
                ·
                  refine ⟨6248403222834313791103745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165602148556209194069163 6248403222834313791103745)
                  ·
                    refine ⟨4686302417125735343327809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6248403222834313791103745 4686302417125735343327809)
                    ·
                      refine ⟨3514726812844301507495857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686302417125735343327809 3514726812844301507495857)
                      ·
                        rfl

theorem cell23_6844906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_6844906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844906 prefixEnd_6844906 := by exact prefixLift 6844906
  have htrace : WordTrace (prefixWord ++ tailWord_6844906) baseStart_6844906 baseEnd_6844906 := by
    simpa [prefixWord, tailWord_6844906, baseEnd_6844906] using wordTrace_append hprefix tailTrace_6844906
  have hstable : (prefixWord ++ tailWord_6844906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844906).length < 2 ^ (prefixWord ++ tailWord_6844906).sum := by decide
  have hdescent : baseEnd_6844906 < baseStart_6844906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844911 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_6844911 : Nat := 118140960795 + 6844911 * 2 ^ 59
def prefixEnd_6844911 : Nat := 4983230072969 + 3 ^ 40 * 6844911 * 2
def baseEnd_6844911 : Nat := 3514729380247573987933333

theorem tailTrace_6844911 : CollatzResearch.WordTrace tailWord_6844911 prefixEnd_6844911 3514729380247573987933333 := by
  unfold tailWord_6844911
  simp only [CollatzResearch.WordTrace]
  refine ⟨249654414105063939573654587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166436276070042626382436391 249654414105063939573654587)
  ·
    refine ⟨374481621157595909360481881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249654414105063939573654587 374481621157595909360481881)
    ·
      refine ⟨280861215868196932020361411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374481621157595909360481881 280861215868196932020361411)
      ·
        refine ⟨421291823802295398030542117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280861215868196932020361411 421291823802295398030542117)
        ·
          refine ⟨78992216962930387130726647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421291823802295398030542117 78992216962930387130726647)
          ·
            refine ⟨118488325444395580696089971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78992216962930387130726647 118488325444395580696089971)
            ·
              refine ⟨177732488166593371044134957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118488325444395580696089971 177732488166593371044134957)
              ·
                refine ⟨66649683062472514141550609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177732488166593371044134957 66649683062472514141550609)
                ·
                  refine ⟨49987262296854385606162957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66649683062472514141550609 49987262296854385606162957)
                  ·
                    refine ⟨18745223361320394602311109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49987262296854385606162957 18745223361320394602311109)
                    ·
                      refine ⟨3514729380247573987933333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18745223361320394602311109 3514729380247573987933333)
                      ·
                        rfl

theorem cell23_6844911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_6844911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844911 prefixEnd_6844911 := by exact prefixLift 6844911
  have htrace : WordTrace (prefixWord ++ tailWord_6844911) baseStart_6844911 baseEnd_6844911 := by
    simpa [prefixWord, tailWord_6844911, baseEnd_6844911] using wordTrace_append hprefix tailTrace_6844911
  have hstable : (prefixWord ++ tailWord_6844911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844911).length < 2 ^ (prefixWord ++ tailWord_6844911).sum := by decide
  have hdescent : baseEnd_6844911 < baseStart_6844911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844921 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 2, 6]
def baseStart_6844921 : Nat := 118140960795 + 6844921 * 2 ^ 59
def prefixEnd_6844921 : Nat := 4983230072969 + 3 ^ 40 * 6844921 * 2
def baseEnd_6844921 : Nat := 1171578171684706316269429

theorem tailTrace_6844921 : CollatzResearch.WordTrace tailWord_6844921 prefixEnd_6844921 1171578171684706316269429 := by
  unfold tailWord_6844921
  simp only [CollatzResearch.WordTrace]
  refine ⟨249654778835027711281518617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166436519223351807521012411 249654778835027711281518617)
  ·
    refine ⟨187241084126270783461138963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249654778835027711281518617 187241084126270783461138963)
    ·
      refine ⟨280861626189406175191708445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187241084126270783461138963 280861626189406175191708445)
      ·
        refine ⟨105323109821027315696890667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280861626189406175191708445 105323109821027315696890667)
        ·
          refine ⟨157984664731540973545336001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105323109821027315696890667 157984664731540973545336001)
          ·
            refine ⟨118488498548655730159002001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157984664731540973545336001 118488498548655730159002001)
            ·
              refine ⟨88866373911491797619251501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118488498548655730159002001 88866373911491797619251501)
              ·
                refine ⟨33324890216809424107219313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88866373911491797619251501 33324890216809424107219313)
                ·
                  refine ⟨24993667662607068080414485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33324890216809424107219313 24993667662607068080414485)
                  ·
                    refine ⟨1171578171684706316269429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24993667662607068080414485 1171578171684706316269429)
                    ·
                      rfl

theorem cell23_6844921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 6].length) (baseStart_6844921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844921 prefixEnd_6844921 := by exact prefixLift 6844921
  have htrace : WordTrace (prefixWord ++ tailWord_6844921) baseStart_6844921 baseEnd_6844921 := by
    simpa [prefixWord, tailWord_6844921, baseEnd_6844921] using wordTrace_append hprefix tailTrace_6844921
  have hstable : (prefixWord ++ tailWord_6844921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844921).length < 2 ^ (prefixWord ++ tailWord_6844921).sum := by decide
  have hdescent : baseEnd_6844921 < baseStart_6844921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844928 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 7, 4, 2]
def baseStart_6844928 : Nat := 118140960795 + 6844928 * 2 ^ 59
def prefixEnd_6844928 : Nat := 4983230072969 + 3 ^ 40 * 6844928 * 2
def baseEnd_6844928 : Nat := 3514738109418700421420755

theorem tailTrace_6844928 : CollatzResearch.WordTrace tailWord_6844928 prefixEnd_6844928 3514738109418700421420755 := by
  unfold tailWord_6844928
  simp only [CollatzResearch.WordTrace]
  refine ⟨124827517073001175738511719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166436689430668234318015625 124827517073001175738511719)
  ·
    refine ⟨187241275609501763607767579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124827517073001175738511719 187241275609501763607767579)
    ·
      refine ⟨280861913414252645411651369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187241275609501763607767579 280861913414252645411651369)
      ·
        refine ⟨210646435060689484058738527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280861913414252645411651369 210646435060689484058738527)
        ·
          refine ⟨315969652591034226088107791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210646435060689484058738527 315969652591034226088107791)
          ·
            refine ⟨473954478886551339132161687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315969652591034226088107791 473954478886551339132161687)
            ·
              refine ⟨710931718329827008698242531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473954478886551339132161687 710931718329827008698242531)
              ·
                refine ⟨1066397577494740513047363797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 710931718329827008698242531 1066397577494740513047363797)
                ·
                  refine ⟨24993693222532980774547589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1066397577494740513047363797 24993693222532980774547589)
                  ·
                    refine ⟨4686317479224933895227673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24993693222532980774547589 4686317479224933895227673)
                    ·
                      refine ⟨3514738109418700421420755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686317479224933895227673 3514738109418700421420755)
                      ·
                        rfl

theorem cell23_6844928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_6844928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844928 prefixEnd_6844928 := by exact prefixLift 6844928
  have htrace : WordTrace (prefixWord ++ tailWord_6844928) baseStart_6844928 baseEnd_6844928 := by
    simpa [prefixWord, tailWord_6844928, baseEnd_6844928] using wordTrace_append hprefix tailTrace_6844928
  have hstable : (prefixWord ++ tailWord_6844928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844928).length < 2 ^ (prefixWord ++ tailWord_6844928).sum := by decide
  have hdescent : baseEnd_6844928 < baseStart_6844928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844931 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5]
def baseStart_6844931 : Nat := 118140960795 + 6844931 * 2 ^ 59
def prefixEnd_6844931 : Nat := 4983230072969 + 3 ^ 40 * 6844931 * 2
def baseEnd_6844931 : Nat := 3514739649860663909683241

theorem tailTrace_6844931 : CollatzResearch.WordTrace tailWord_6844931 prefixEnd_6844931 3514739649860663909683241 := by
  unfold tailWord_6844931
  simp only [CollatzResearch.WordTrace]
  refine ⟨249655143564991482989382647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166436762376660988659588431 249655143564991482989382647)
  ·
    refine ⟨374482715347487224484073971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249655143564991482989382647 374482715347487224484073971)
    ·
      refine ⟨561724073021230836726110957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374482715347487224484073971 561724073021230836726110957)
      ·
        refine ⟨210646527382961563772291609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561724073021230836726110957 210646527382961563772291609)
        ·
          refine ⟨157984895537221172829218707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210646527382961563772291609 157984895537221172829218707)
          ·
            refine ⟨236977343305831759243828061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157984895537221172829218707 236977343305831759243828061)
            ·
              refine ⟨88866503739686909716435523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236977343305831759243828061 88866503739686909716435523)
              ·
                refine ⟨133299755609530364574653285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88866503739686909716435523 133299755609530364574653285)
                ·
                  refine ⟨24993704176786943357747491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133299755609530364574653285 24993704176786943357747491)
                  ·
                    refine ⟨37490556265180415036621237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24993704176786943357747491 37490556265180415036621237)
                    ·
                      refine ⟨3514739649860663909683241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37490556265180415036621237 3514739649860663909683241)
                      ·
                        rfl

theorem cell23_6844931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_6844931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844931 prefixEnd_6844931 := by exact prefixLift 6844931
  have htrace : WordTrace (prefixWord ++ tailWord_6844931) baseStart_6844931 baseEnd_6844931 := by
    simpa [prefixWord, tailWord_6844931, baseEnd_6844931] using wordTrace_append hprefix tailTrace_6844931
  have hstable : (prefixWord ++ tailWord_6844931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844931).length < 2 ^ (prefixWord ++ tailWord_6844931).sum := by decide
  have hdescent : baseEnd_6844931 < baseStart_6844931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844932 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6844932 : Nat := 118140960795 + 6844932 * 2 ^ 59
def prefixEnd_6844932 : Nat := 4983230072969 + 3 ^ 40 * 6844932 * 2
def baseEnd_6844932 : Nat := 3514740163341318405770737

theorem tailTrace_6844932 : CollatzResearch.WordTrace tailWord_6844932 prefixEnd_6844932 3514740163341318405770737 := by
  unfold tailWord_6844932
  simp only [CollatzResearch.WordTrace]
  refine ⟨124827590018993930080084525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166436786691991906773446033 124827590018993930080084525)
  ·
    refine ⟨46810346257122723780031697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124827590018993930080084525 46810346257122723780031697)
    ·
      refine ⟨35107759692842042835023773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46810346257122723780031697 35107759692842042835023773)
      ·
        refine ⟨13165409884815766063133915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35107759692842042835023773 13165409884815766063133915)
        ·
          refine ⟨19748114827223649094700873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13165409884815766063133915 19748114827223649094700873)
          ·
            refine ⟨14811086120417736821025655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19748114827223649094700873 14811086120417736821025655)
            ·
              refine ⟨22216629180626605231538483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14811086120417736821025655 22216629180626605231538483)
              ·
                refine ⟨33324943770939907847307725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22216629180626605231538483 33324943770939907847307725)
                ·
                  refine ⟨12496853914102465442740397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33324943770939907847307725 12496853914102465442740397)
                  ·
                    refine ⟨4686320217788424541027649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12496853914102465442740397 4686320217788424541027649)
                    ·
                      refine ⟨3514740163341318405770737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686320217788424541027649 3514740163341318405770737)
                      ·
                        rfl

theorem cell23_6844932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6844932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844932 prefixEnd_6844932 := by exact prefixLift 6844932
  have htrace : WordTrace (prefixWord ++ tailWord_6844932) baseStart_6844932 baseEnd_6844932 := by
    simpa [prefixWord, tailWord_6844932, baseEnd_6844932] using wordTrace_append hprefix tailTrace_6844932
  have hstable : (prefixWord ++ tailWord_6844932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844932).length < 2 ^ (prefixWord ++ tailWord_6844932).sum := by decide
  have hdescent : baseEnd_6844932 < baseStart_6844932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844945 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 4, 2, 2]
def baseStart_6844945 : Nat := 118140960795 + 6844945 * 2 ^ 59
def prefixEnd_6844945 : Nat := 4983230072969 + 3 ^ 40 * 6844945 * 2
def baseEnd_6844945 : Nat := 3514746838589826854908177

theorem tailTrace_6844945 : CollatzResearch.WordTrace tailWord_6844945 prefixEnd_6844945 3514746838589826854908177 := by
  unfold tailWord_6844945
  simp only [CollatzResearch.WordTrace]
  refine ⟨249655654186940763380392289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166437102791293842253594859 249655654186940763380392289)
  ·
    refine ⟨187241740640205572535294217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249655654186940763380392289 187241740640205572535294217)
    ·
      refine ⟨140431305480154179401470663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187241740640205572535294217 140431305480154179401470663)
      ·
        refine ⟨210646958220231269102205995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140431305480154179401470663 210646958220231269102205995)
        ·
          refine ⟨315970437330346903653308993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210646958220231269102205995 315970437330346903653308993)
          ·
            refine ⟨236977827997760177739981745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315970437330346903653308993 236977827997760177739981745)
            ·
              refine ⟨177733370998320133304986309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236977827997760177739981745 177733370998320133304986309)
              ·
                refine ⟨33325007062185024994684933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177733370998320133304986309 33325007062185024994684933)
                ·
                  refine ⟨6248438824159692186503425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33325007062185024994684933 6248438824159692186503425)
                  ·
                    refine ⟨4686329118119769139877569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6248438824159692186503425 4686329118119769139877569)
                    ·
                      refine ⟨3514746838589826854908177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686329118119769139877569 3514746838589826854908177)
                      ·
                        rfl

theorem cell23_6844945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_6844945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844945 prefixEnd_6844945 := by exact prefixLift 6844945
  have htrace : WordTrace (prefixWord ++ tailWord_6844945) baseStart_6844945 baseEnd_6844945 := by
    simpa [prefixWord, tailWord_6844945, baseEnd_6844945] using wordTrace_append hprefix tailTrace_6844945
  have hstable : (prefixWord ++ tailWord_6844945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844945).length < 2 ^ (prefixWord ++ tailWord_6844945).sum := by decide
  have hdescent : baseEnd_6844945 < baseStart_6844945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6844978 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_6844978 : Nat := 118140960795 + 6844978 * 2 ^ 59
def prefixEnd_6844978 : Nat := 4983230072969 + 3 ^ 40 * 6844978 * 2
def baseEnd_6844978 : Nat := 3514763783451425225795525

theorem tailTrace_6844978 : CollatzResearch.WordTrace tailWord_6844978 prefixEnd_6844978 3514763783451425225795525 := by
  unfold tailWord_6844978
  simp only [CollatzResearch.WordTrace]
  refine ⟨62414214448955302504085897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166437905197214140010895725 62414214448955302504085897)
  ·
    refine ⟨46810660836716476878064423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62414214448955302504085897 46810660836716476878064423)
    ·
      refine ⟨70215991255074715317096635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46810660836716476878064423 70215991255074715317096635)
      ·
        refine ⟨105323986882612072975644953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70215991255074715317096635 105323986882612072975644953)
        ·
          refine ⟨78992990161959054731733715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105323986882612072975644953 78992990161959054731733715)
          ·
            refine ⟨118489485242938582097600573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78992990161959054731733715 118489485242938582097600573)
            ·
              refine ⟨44433556966101968286600215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118489485242938582097600573 44433556966101968286600215)
              ·
                refine ⟨66650335449152952429900323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44433556966101968286600215 66650335449152952429900323)
                ·
                  refine ⟨99975503173729428644850485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66650335449152952429900323 99975503173729428644850485)
                  ·
                    refine ⟨9372703422537133935454733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99975503173729428644850485 9372703422537133935454733)
                    ·
                      refine ⟨3514763783451425225795525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9372703422537133935454733 3514763783451425225795525)
                      ·
                        rfl

theorem cell23_6844978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_6844978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6844978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6844978 prefixEnd_6844978 := by exact prefixLift 6844978
  have htrace : WordTrace (prefixWord ++ tailWord_6844978) baseStart_6844978 baseEnd_6844978 := by
    simpa [prefixWord, tailWord_6844978, baseEnd_6844978] using wordTrace_append hprefix tailTrace_6844978
  have hstable : (prefixWord ++ tailWord_6844978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6844978).length < 2 ^ (prefixWord ++ tailWord_6844978).sum := by decide
  have hdescent : baseEnd_6844978 < baseStart_6844978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6844978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845079 : List Nat := [1, 1, 3, 3, 2, 1, 5, 2, 1, 4]
def baseStart_6845079 : Nat := 118140960795 + 6845079 * 2 ^ 59
def prefixEnd_6845079 : Nat := 4983230072969 + 3 ^ 40 * 6845079 * 2
def baseEnd_6845079 : Nat := 1171605214999176443544187

theorem tailTrace_6845079 : CollatzResearch.WordTrace tailWord_6845079 prefixEnd_6845079 1171605214999176443544187 := by
  unfold tailWord_6845079
  simp only [CollatzResearch.WordTrace]
  refine ⟨249660541568455304265770291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166440361045636869510513527 249660541568455304265770291)
  ·
    refine ⟨374490812352682956398655437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249660541568455304265770291 374490812352682956398655437)
    ·
      refine ⟨140434054632256108649495789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374490812352682956398655437 140434054632256108649495789)
      ·
        refine ⟨52662770487096040743560921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140434054632256108649495789 52662770487096040743560921)
        ·
          refine ⟨39497077865322030557670691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52662770487096040743560921 39497077865322030557670691)
          ·
            refine ⟨59245616797983045836506037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39497077865322030557670691 59245616797983045836506037)
            ·
              refine ⟨5554276574810910547172441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59245616797983045836506037 5554276574810910547172441)
              ·
                refine ⟨4165707431108182910379331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5554276574810910547172441 4165707431108182910379331)
                ·
                  refine ⟨6248561146662274365568997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165707431108182910379331 6248561146662274365568997)
                  ·
                    refine ⟨1171605214999176443544187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6248561146662274365568997 1171605214999176443544187)
                    ·
                      rfl

theorem cell23_6845079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_6845079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845079 prefixEnd_6845079 := by exact prefixLift 6845079
  have htrace : WordTrace (prefixWord ++ tailWord_6845079) baseStart_6845079 baseEnd_6845079 := by
    simpa [prefixWord, tailWord_6845079, baseEnd_6845079] using wordTrace_append hprefix tailTrace_6845079
  have hstable : (prefixWord ++ tailWord_6845079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845079).length < 2 ^ (prefixWord ++ tailWord_6845079).sum := by decide
  have hdescent : baseEnd_6845079 < baseStart_6845079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845126 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_6845126 : Nat := 118140960795 + 6845126 * 2 ^ 59
def prefixEnd_6845126 : Nat := 4983230072969 + 3 ^ 40 * 6845126 * 2
def baseEnd_6845126 : Nat := 390537753176476738527205

theorem tailTrace_6845126 : CollatzResearch.WordTrace tailWord_6845126 prefixEnd_6845126 390537753176476738527205 := by
  unfold tailWord_6845126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7801945493727657227897851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166441503866190020861820821 7801945493727657227897851)
  ·
    refine ⟨11702918240591485841846777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7801945493727657227897851 11702918240591485841846777)
    ·
      refine ⟨8777188680443614381385083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11702918240591485841846777 8777188680443614381385083)
      ·
        refine ⟨13165783020665421572077625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8777188680443614381385083 13165783020665421572077625)
        ·
          refine ⟨9874337265499066179058219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13165783020665421572077625 9874337265499066179058219)
          ·
            refine ⟨14811505898248599268587329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9874337265499066179058219 14811505898248599268587329)
            ·
              refine ⟨11108629423686449451440497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14811505898248599268587329 11108629423686449451440497)
              ·
                refine ⟨8331472067764837088580373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11108629423686449451440497 8331472067764837088580373)
                ·
                  refine ⟨390537753176476738527205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8331472067764837088580373 390537753176476738527205)
                  ·
                    rfl

theorem cell23_6845126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_6845126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845126 prefixEnd_6845126 := by exact prefixLift 6845126
  have htrace : WordTrace (prefixWord ++ tailWord_6845126) baseStart_6845126 baseEnd_6845126 := by
    simpa [prefixWord, tailWord_6845126, baseEnd_6845126] using wordTrace_append hprefix tailTrace_6845126
  have hstable : (prefixWord ++ tailWord_6845126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845126).length < 2 ^ (prefixWord ++ tailWord_6845126).sum := by decide
  have hdescent : baseEnd_6845126 < baseStart_6845126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845145 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 3]
def baseStart_6845145 : Nat := 118140960795 + 6845145 * 2 ^ 59
def prefixEnd_6845145 : Nat := 4983230072969 + 3 ^ 40 * 6845145 * 2
def baseEnd_6845145 : Nat := 3514849534720726072407257

theorem tailTrace_6845145 : CollatzResearch.WordTrace tailWord_6845145 prefixEnd_6845145 3514849534720726072407257 := by
  unfold tailWord_6845145
  simp only [CollatzResearch.WordTrace]
  refine ⟨249662948786216197537672889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166441965857477465025115259 249662948786216197537672889)
  ·
    refine ⟨187247211589662148153254667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249662948786216197537672889 187247211589662148153254667)
    ·
      refine ⟨280870817384493222229882001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187247211589662148153254667 280870817384493222229882001)
      ·
        refine ⟨210653113038369916672411501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280870817384493222229882001 210653113038369916672411501)
        ·
          refine ⟨78994917389388718752154313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210653113038369916672411501 78994917389388718752154313)
          ·
            refine ⟨59246188042041539064115735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78994917389388718752154313 59246188042041539064115735)
            ·
              refine ⟨88869282063062308596173603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59246188042041539064115735 88869282063062308596173603)
              ·
                refine ⟨133303923094593462894260405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88869282063062308596173603 133303923094593462894260405)
                ·
                  refine ⟨12497242790118137146336913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133303923094593462894260405 12497242790118137146336913)
                  ·
                    refine ⟨9372932092588602859752685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12497242790118137146336913 9372932092588602859752685)
                    ·
                      refine ⟨3514849534720726072407257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9372932092588602859752685 3514849534720726072407257)
                      ·
                        rfl

theorem cell23_6845145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_6845145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845145 prefixEnd_6845145 := by exact prefixLift 6845145
  have htrace : WordTrace (prefixWord ++ tailWord_6845145) baseStart_6845145 baseEnd_6845145 := by
    simpa [prefixWord, tailWord_6845145, baseEnd_6845145] using wordTrace_append hprefix tailTrace_6845145
  have hstable : (prefixWord ++ tailWord_6845145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845145).length < 2 ^ (prefixWord ++ tailWord_6845145).sum := by decide
  have hdescent : baseEnd_6845145 < baseStart_6845145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845162 : List Nat := [3, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_6845162 : Nat := 118140960795 + 6845162 * 2 ^ 59
def prefixEnd_6845162 : Nat := 4983230072969 + 3 ^ 40 * 6845162 * 2
def baseEnd_6845162 : Nat := 3514858263891852505894679

theorem tailTrace_6845162 : CollatzResearch.WordTrace tailWord_6845162 prefixEnd_6845162 3514858263891852505894679 := by
  unfold tailWord_6845162
  simp only [CollatzResearch.WordTrace]
  refine ⟨62415892206788652360260435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166442379218103072960694493 62415892206788652360260435)
  ·
    refine ⟨93623838310182978540390653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62415892206788652360260435 93623838310182978540390653)
    ·
      refine ⟨35108939366318616952646495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93623838310182978540390653 35108939366318616952646495)
      ·
        refine ⟨52663409049477925428969743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35108939366318616952646495 52663409049477925428969743)
        ·
          refine ⟨78995113574216888143454615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52663409049477925428969743 78995113574216888143454615)
          ·
            refine ⟨118492670361325332215181923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78995113574216888143454615 118492670361325332215181923)
            ·
              refine ⟨177739005541987998322772885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118492670361325332215181923 177739005541987998322772885)
              ·
                refine ⟨8331515884780687421379979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177739005541987998322772885 8331515884780687421379979)
                ·
                  refine ⟨12497273827171031132069969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8331515884780687421379979 12497273827171031132069969)
                  ·
                    refine ⟨9372955370378273349052477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12497273827171031132069969 9372955370378273349052477)
                    ·
                      refine ⟨3514858263891852505894679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9372955370378273349052477 3514858263891852505894679)
                      ·
                        rfl

theorem cell23_6845162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_6845162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845162 prefixEnd_6845162 := by exact prefixLift 6845162
  have htrace : WordTrace (prefixWord ++ tailWord_6845162) baseStart_6845162 baseEnd_6845162 := by
    simpa [prefixWord, tailWord_6845162, baseEnd_6845162] using wordTrace_append hprefix tailTrace_6845162
  have hstable : (prefixWord ++ tailWord_6845162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845162).length < 2 ^ (prefixWord ++ tailWord_6845162).sum := by decide
  have hdescent : baseEnd_6845162 < baseStart_6845162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845176 : List Nat := [2, 1, 2, 1, 1, 2, 6, 3, 1, 2, 2]
def baseStart_6845176 : Nat := 118140960795 + 6845176 * 2 ^ 59
def prefixEnd_6845176 : Nat := 4983230072969 + 3 ^ 40 * 6845176 * 2
def baseEnd_6845176 : Nat := 3514865452621015451119615

theorem tailTrace_6845176 : CollatzResearch.WordTrace tailWord_6845176 prefixEnd_6845176 3514865452621015451119615 := by
  unfold tailWord_6845176
  simp only [CollatzResearch.WordTrace]
  refine ⟨124832039724551944916025691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166442719632735926554700921 124832039724551944916025691)
  ·
    refine ⟨187248059586827917374038537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124832039724551944916025691 187248059586827917374038537)
    ·
      refine ⟨140436044690120938030528903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187248059586827917374038537 140436044690120938030528903)
      ·
        refine ⟨210654067035181407045793355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140436044690120938030528903 210654067035181407045793355)
        ·
          refine ⟨315981100552772110568690033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210654067035181407045793355 315981100552772110568690033)
          ·
            refine ⟨236985825414579082926517525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315981100552772110568690033 236985825414579082926517525)
            ·
              refine ⟨11108710566308394512180509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236985825414579082926517525 11108710566308394512180509)
              ·
                refine ⟨4165766462365647942067691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11108710566308394512180509 4165766462365647942067691)
                ·
                  refine ⟨6248649693548471913101537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165766462365647942067691 6248649693548471913101537)
                  ·
                    refine ⟨4686487270161353934826153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6248649693548471913101537 4686487270161353934826153)
                    ·
                      refine ⟨3514865452621015451119615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686487270161353934826153 3514865452621015451119615)
                      ·
                        rfl

theorem cell23_6845176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 3, 1, 2, 2].length) (baseStart_6845176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845176 prefixEnd_6845176 := by exact prefixLift 6845176
  have htrace : WordTrace (prefixWord ++ tailWord_6845176) baseStart_6845176 baseEnd_6845176 := by
    simpa [prefixWord, tailWord_6845176, baseEnd_6845176] using wordTrace_append hprefix tailTrace_6845176
  have hstable : (prefixWord ++ tailWord_6845176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845176).length < 2 ^ (prefixWord ++ tailWord_6845176).sum := by decide
  have hdescent : baseEnd_6845176 < baseStart_6845176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845186 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_6845186 : Nat := 118140960795 + 6845186 * 2 ^ 59
def prefixEnd_6845186 : Nat := 4983230072969 + 3 ^ 40 * 6845186 * 2
def baseEnd_6845186 : Nat := 1171623529142520137331523

theorem tailTrace_6845186 : CollatzResearch.WordTrace tailWord_6845186 prefixEnd_6845186 1171623529142520137331523 := by
  unfold tailWord_6845186
  simp only [CollatzResearch.WordTrace]
  refine ⟨62416111044766915384978853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166442962786045107693276941 62416111044766915384978853)
  ·
    refine ⟨11703020820893796634683535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62416111044766915384978853 11703020820893796634683535)
    ·
      refine ⟨17554531231340694952025303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11703020820893796634683535 17554531231340694952025303)
      ·
        refine ⟨26331796847011042428037955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17554531231340694952025303 26331796847011042428037955)
        ·
          refine ⟨39497695270516563642056933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26331796847011042428037955 39497695270516563642056933)
          ·
            refine ⟨7405817863221855682885675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39497695270516563642056933 7405817863221855682885675)
            ·
              refine ⟨11108726794832783524328513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7405817863221855682885675 11108726794832783524328513)
              ·
                refine ⟨8331545096124587643246385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11108726794832783524328513 8331545096124587643246385)
                ·
                  refine ⟨6248658822093440732434789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8331545096124587643246385 6248658822093440732434789)
                  ·
                    refine ⟨1171623529142520137331523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6248658822093440732434789 1171623529142520137331523)
                    ·
                      rfl

theorem cell23_6845186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_6845186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845186 prefixEnd_6845186 := by exact prefixLift 6845186
  have htrace : WordTrace (prefixWord ++ tailWord_6845186) baseStart_6845186 baseEnd_6845186 := by
    simpa [prefixWord, tailWord_6845186, baseEnd_6845186] using wordTrace_append hprefix tailTrace_6845186
  have hstable : (prefixWord ++ tailWord_6845186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845186).length < 2 ^ (prefixWord ++ tailWord_6845186).sum := by decide
  have hdescent : baseEnd_6845186 < baseStart_6845186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845232 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 1, 4, 2]
def baseStart_6845232 : Nat := 118140960795 + 6845232 * 2 ^ 59
def prefixEnd_6845232 : Nat := 4983230072969 + 3 ^ 40 * 6845232 * 2
def baseEnd_6845232 : Nat := 3514894207537667232019357

theorem tailTrace_6845232 : CollatzResearch.WordTrace tailWord_6845232 prefixEnd_6845232 3514894207537667232019357 := by
  unfold tailWord_6845232
  simp only [CollatzResearch.WordTrace]
  refine ⟨124833060968450505698044975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166444081291267340930726633 124833060968450505698044975)
  ·
    refine ⟨187249591452675758547067463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124833060968450505698044975 187249591452675758547067463)
    ·
      refine ⟨280874387179013637820601195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187249591452675758547067463 280874387179013637820601195)
      ·
        refine ⟨421311580768520456730901793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280874387179013637820601195 421311580768520456730901793)
        ·
          refine ⟨315983685576390342548176345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421311580768520456730901793 315983685576390342548176345)
          ·
            refine ⟨236987764182292756911132259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315983685576390342548176345 236987764182292756911132259)
            ·
              refine ⟨355481646273439135366698389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236987764182292756911132259 355481646273439135366698389)
              ·
                refine ⟨16663202169067459470313987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 355481646273439135366698389 16663202169067459470313987)
                ·
                  refine ⟨24994803253601189205470981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16663202169067459470313987 24994803253601189205470981)
                  ·
                    refine ⟨4686525610050222976025809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24994803253601189205470981 4686525610050222976025809)
                    ·
                      refine ⟨3514894207537667232019357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686525610050222976025809 3514894207537667232019357)
                      ·
                        rfl

theorem cell23_6845232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 1, 4, 2].length) (baseStart_6845232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845232 prefixEnd_6845232 := by exact prefixLift 6845232
  have htrace : WordTrace (prefixWord ++ tailWord_6845232) baseStart_6845232 baseEnd_6845232 := by
    simpa [prefixWord, tailWord_6845232, baseEnd_6845232] using wordTrace_append hprefix tailTrace_6845232
  have hstable : (prefixWord ++ tailWord_6845232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845232).length < 2 ^ (prefixWord ++ tailWord_6845232).sum := by decide
  have hdescent : baseEnd_6845232 < baseStart_6845232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845235 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5]
def baseStart_6845235 : Nat := 118140960795 + 6845235 * 2 ^ 59
def prefixEnd_6845235 : Nat := 4983230072969 + 3 ^ 40 * 6845235 * 2
def baseEnd_6845235 : Nat := 3514895747979630720281843

theorem tailTrace_6845235 : CollatzResearch.WordTrace tailWord_6845235 prefixEnd_6845235 3514895747979630720281843 := by
  unfold tailWord_6845235
  simp only [CollatzResearch.WordTrace]
  refine ⟨249666231355890142908449159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166444154237260095272299439 249666231355890142908449159)
  ·
    refine ⟨374499347033835214362673739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249666231355890142908449159 374499347033835214362673739)
    ·
      refine ⟨561749020550752821544010609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374499347033835214362673739 561749020550752821544010609)
      ·
        refine ⟨421311765413064616158007957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561749020550752821544010609 421311765413064616158007957)
        ·
          refine ⟨19748989003737403882406623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 421311765413064616158007957 19748989003737403882406623)
          ·
            refine ⟨29623483505606105823609935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19748989003737403882406623 29623483505606105823609935)
            ·
              refine ⟨44435225258409158735414903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29623483505606105823609935 44435225258409158735414903)
              ·
                refine ⟨66652837887613738103122355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44435225258409158735414903 66652837887613738103122355)
                ·
                  refine ⟨99979256831420607154683533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66652837887613738103122355 99979256831420607154683533)
                  ·
                    refine ⟨37492221311782727683006325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99979256831420607154683533 37492221311782727683006325)
                    ·
                      refine ⟨3514895747979630720281843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37492221311782727683006325 3514895747979630720281843)
                      ·
                        rfl

theorem cell23_6845235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_6845235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845235 prefixEnd_6845235 := by exact prefixLift 6845235
  have htrace : WordTrace (prefixWord ++ tailWord_6845235) baseStart_6845235 baseEnd_6845235 := by
    simpa [prefixWord, tailWord_6845235, baseEnd_6845235] using wordTrace_append hprefix tailTrace_6845235
  have hstable : (prefixWord ++ tailWord_6845235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845235).length < 2 ^ (prefixWord ++ tailWord_6845235).sum := by decide
  have hdescent : baseEnd_6845235 < baseStart_6845235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845266 : List Nat := [3, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_6845266 : Nat := 118140960795 + 6845266 * 2 ^ 59
def prefixEnd_6845266 : Nat := 4983230072969 + 3 ^ 40 * 6845266 * 2
def baseEnd_6845266 : Nat := 3514911665879920098994201

theorem tailTrace_6845266 : CollatzResearch.WordTrace tailWord_6845266 prefixEnd_6845266 3514911665879920098994201 := by
  unfold tailWord_6845266
  simp only [CollatzResearch.WordTrace]
  refine ⟨62416840504694458800706913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166444908012518556801885101 62416840504694458800706913)
  ·
    refine ⟨46812630378520844100530185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62416840504694458800706913 46812630378520844100530185)
    ·
      refine ⟨35109472783890633075397639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46812630378520844100530185 35109472783890633075397639)
      ·
        refine ⟨52664209175835949613096459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35109472783890633075397639 52664209175835949613096459)
        ·
          refine ⟨78996313763753924419644689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52664209175835949613096459 78996313763753924419644689)
          ·
            refine ⟨59247235322815443314733517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78996313763753924419644689 59247235322815443314733517)
            ·
              refine ⟨22217713246055791243025069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59247235322815443314733517 22217713246055791243025069)
              ·
                refine ⟨8331642467270921716134401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22217713246055791243025069 8331642467270921716134401)
                ·
                  refine ⟨6248731850453191287100801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8331642467270921716134401 6248731850453191287100801)
                  ·
                    refine ⟨4686548887839893465325601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6248731850453191287100801 4686548887839893465325601)
                    ·
                      refine ⟨3514911665879920098994201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686548887839893465325601 3514911665879920098994201)
                      ·
                        rfl

theorem cell23_6845266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_6845266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845266 prefixEnd_6845266 := by exact prefixLift 6845266
  have htrace : WordTrace (prefixWord ++ tailWord_6845266) baseStart_6845266 baseEnd_6845266 := by
    simpa [prefixWord, tailWord_6845266, baseEnd_6845266] using wordTrace_append hprefix tailTrace_6845266
  have hstable : (prefixWord ++ tailWord_6845266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845266).length < 2 ^ (prefixWord ++ tailWord_6845266).sum := by decide
  have hdescent : baseEnd_6845266 < baseStart_6845266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845285 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_6845285 : Nat := 118140960795 + 6845285 * 2 ^ 59
def prefixEnd_6845285 : Nat := 4983230072969 + 3 ^ 40 * 6845285 * 2
def baseEnd_6845285 : Nat := 1171640474004118508218871

theorem tailTrace_6845285 : CollatzResearch.WordTrace tailWord_6845285 prefixEnd_6845285 1171640474004118508218871 := by
  unfold tailWord_6845285
  simp only [CollatzResearch.WordTrace]
  refine ⟨249668055005709001447769309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166445370003806000965179539 249668055005709001447769309)
  ·
    refine ⟨93625520627140875542913491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249668055005709001447769309 93625520627140875542913491)
    ·
      refine ⟨140438280940711313314370237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93625520627140875542913491 140438280940711313314370237)
      ·
        refine ⟨52664355352766742492888839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140438280940711313314370237 52664355352766742492888839)
        ·
          refine ⟨78996533029150113739333259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52664355352766742492888839 78996533029150113739333259)
          ·
            refine ⟨118494799543725170608999889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78996533029150113739333259 118494799543725170608999889)
            ·
              refine ⟨88871099657793877956749917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118494799543725170608999889 88871099657793877956749917)
              ·
                refine ⟨33326662371672704233781219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88871099657793877956749917 33326662371672704233781219)
                ·
                  refine ⟨49989993557509056350671829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33326662371672704233781219 49989993557509056350671829)
                  ·
                    refine ⟨1171640474004118508218871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49989993557509056350671829 1171640474004118508218871)
                    ·
                      rfl

theorem cell23_6845285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_6845285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845285 prefixEnd_6845285 := by exact prefixLift 6845285
  have htrace : WordTrace (prefixWord ++ tailWord_6845285) baseStart_6845285 baseEnd_6845285 := by
    simpa [prefixWord, tailWord_6845285, baseEnd_6845285] using wordTrace_append hprefix tailTrace_6845285
  have hstable : (prefixWord ++ tailWord_6845285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845285).length < 2 ^ (prefixWord ++ tailWord_6845285).sum := by decide
  have hdescent : baseEnd_6845285 < baseStart_6845285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845375 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 9]
def baseStart_6845375 : Nat := 118140960795 + 6845375 * 2 ^ 59
def prefixEnd_6845375 : Nat := 4983230072969 + 3 ^ 40 * 6845375 * 2
def baseEnd_6845375 : Nat := 1171655878423753390843733

theorem tailTrace_6845375 : CollatzResearch.WordTrace tailWord_6845375 prefixEnd_6845375 1171655878423753390843733 := by
  unfold tailWord_6845375
  simp only [CollatzResearch.WordTrace]
  refine ⟨249671337575382946818545579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166447558383588631212363719 249671337575382946818545579)
  ·
    refine ⟨374507006363074420227818369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249671337575382946818545579 374507006363074420227818369)
    ·
      refine ⟨280880254772305815170863777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374507006363074420227818369 280880254772305815170863777)
      ·
        refine ⟨210660191079229361378147833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280880254772305815170863777 210660191079229361378147833)
        ·
          refine ⟨157995143309422021033610875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210660191079229361378147833 157995143309422021033610875)
          ·
            refine ⟨236992714964133031550416313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157995143309422021033610875 236992714964133031550416313)
            ·
              refine ⟨177744536223099773662812235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236992714964133031550416313 177744536223099773662812235)
              ·
                refine ⟨266616804334649660494218353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177744536223099773662812235 266616804334649660494218353)
                ·
                  refine ⟨199962603250987245370663765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266616804334649660494218353 199962603250987245370663765)
                  ·
                    refine ⟨1171655878423753390843733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199962603250987245370663765 1171655878423753390843733)
                    ·
                      rfl

theorem cell23_6845375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_6845375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845375 prefixEnd_6845375 := by exact prefixLift 6845375
  have htrace : WordTrace (prefixWord ++ tailWord_6845375) baseStart_6845375 baseEnd_6845375 := by
    simpa [prefixWord, tailWord_6845375, baseEnd_6845375] using wordTrace_append hprefix tailTrace_6845375
  have hstable : (prefixWord ++ tailWord_6845375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845375).length < 2 ^ (prefixWord ++ tailWord_6845375).sum := by decide
  have hdescent : baseEnd_6845375 < baseStart_6845375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845432 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_6845432 : Nat := 118140960795 + 6845432 * 2 ^ 59
def prefixEnd_6845432 : Nat := 4983230072969 + 3 ^ 40 * 6845432 * 2
def baseEnd_6845432 : Nat := 3514996903668566449518437

theorem tailTrace_6845432 : CollatzResearch.WordTrace tailWord_6845432 prefixEnd_6845432 3514996903668566449518437 := by
  unfold tailWord_6845432
  simp only [CollatzResearch.WordTrace]
  refine ⟨124836708268088222776685275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166448944357450963702247033 124836708268088222776685275)
  ·
    refine ⟨187255062402132334165027913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124836708268088222776685275 187255062402132334165027913)
    ·
      refine ⟨140441296801599250623770935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187255062402132334165027913 140441296801599250623770935)
      ·
        refine ⟨210661945202398875935656403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140441296801599250623770935 210661945202398875935656403)
        ·
          refine ⟨315992917803598313903484605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210661945202398875935656403 315992917803598313903484605)
          ·
            refine ⟨118497344176349367713806727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315992917803598313903484605 118497344176349367713806727)
            ·
              refine ⟨177746016264524051570710091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118497344176349367713806727 177746016264524051570710091)
              ·
                refine ⟨266619024396786077356065137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177746016264524051570710091 266619024396786077356065137)
                ·
                  refine ⟨199964268297589558017048853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266619024396786077356065137 199964268297589558017048853)
                  ·
                    refine ⟨9373325076449510532049165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 199964268297589558017048853 9373325076449510532049165)
                    ·
                      refine ⟨3514996903668566449518437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9373325076449510532049165 3514996903668566449518437)
                      ·
                        rfl

theorem cell23_6845432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_6845432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845432 prefixEnd_6845432 := by exact prefixLift 6845432
  have htrace : WordTrace (prefixWord ++ tailWord_6845432) baseStart_6845432 baseEnd_6845432 := by
    simpa [prefixWord, tailWord_6845432, baseEnd_6845432] using wordTrace_append hprefix tailTrace_6845432
  have hstable : (prefixWord ++ tailWord_6845432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845432).length < 2 ^ (prefixWord ++ tailWord_6845432).sum := by decide
  have hdescent : baseEnd_6845432 < baseStart_6845432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845452 : List Nat := [2, 2, 1, 2, 3, 2, 2, 9]
def baseStart_6845452 : Nat := 118140960795 + 6845452 * 2 ^ 59
def prefixEnd_6845452 : Nat := 4983230072969 + 3 ^ 40 * 6845452 * 2
def baseEnd_6845452 : Nat := 130185450862283569306235

theorem tailTrace_6845452 : CollatzResearch.WordTrace tailWord_6845452 prefixEnd_6845452 130185450862283569306235 := by
  unfold tailWord_6845452
  simp only [CollatzResearch.WordTrace]
  refine ⟨124837072998051994484549305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166449430664069325979399073 124837072998051994484549305)
  ·
    refine ⟨93627804748538995863411979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124837072998051994484549305 93627804748538995863411979)
    ·
      refine ⟨140441707122808493795117969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93627804748538995863411979 140441707122808493795117969)
      ·
        refine ⟨105331280342106370346338477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140441707122808493795117969 105331280342106370346338477)
        ·
          refine ⟨39499230128289888879876929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105331280342106370346338477 39499230128289888879876929)
          ·
            refine ⟨29624422596217416659907697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39499230128289888879876929 29624422596217416659907697)
            ·
              refine ⟨22218316947163062494930773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29624422596217416659907697 22218316947163062494930773)
              ·
                refine ⟨130185450862283569306235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22218316947163062494930773 130185450862283569306235)
                ·
                  rfl

theorem cell23_6845452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 9].length) (baseStart_6845452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845452 prefixEnd_6845452 := by exact prefixLift 6845452
  have htrace : WordTrace (prefixWord ++ tailWord_6845452) baseStart_6845452 baseEnd_6845452 := by
    simpa [prefixWord, tailWord_6845452, baseEnd_6845452] using wordTrace_append hprefix tailTrace_6845452
  have hstable : (prefixWord ++ tailWord_6845452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845452).length < 2 ^ (prefixWord ++ tailWord_6845452).sum := by decide
  have hdescent : baseEnd_6845452 < baseStart_6845452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845463 : List Nat := [1, 1, 3, 5, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6845463 : Nat := 118140960795 + 6845463 * 2 ^ 59
def prefixEnd_6845463 : Nat := 4983230072969 + 3 ^ 40 * 6845463 * 2
def baseEnd_6845463 : Nat := 3515012821568855828230795

theorem tailTrace_6845463 : CollatzResearch.WordTrace tailWord_6845463 prefixEnd_6845463 3515012821568855828230795 := by
  unfold tailWord_6845463
  simp only [CollatzResearch.WordTrace]
  refine ⟨249674547199064137847749043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166449698132709425231832695 249674547199064137847749043)
  ·
    refine ⟨374511820798596206771623565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249674547199064137847749043 374511820798596206771623565)
    ·
      refine ⟨140441932799473577539358837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374511820798596206771623565 140441932799473577539358837)
      ·
        refine ⟨13166431199950647894314891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140441932799473577539358837 13166431199950647894314891)
        ·
          refine ⟨19749646799925971841472337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13166431199950647894314891 19749646799925971841472337)
          ·
            refine ⟨14812235099944478881104253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19749646799925971841472337 14812235099944478881104253)
            ·
              refine ⟨5554588162479179580414095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14812235099944478881104253 5554588162479179580414095)
              ·
                refine ⟨8331882243718769370621143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5554588162479179580414095 8331882243718769370621143)
                ·
                  refine ⟨12497823365578154055931715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8331882243718769370621143 12497823365578154055931715)
                  ·
                    refine ⟨18746735048367231083897573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12497823365578154055931715 18746735048367231083897573)
                    ·
                      refine ⟨3515012821568855828230795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18746735048367231083897573 3515012821568855828230795)
                      ·
                        rfl

theorem cell23_6845463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6845463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845463 prefixEnd_6845463 := by exact prefixLift 6845463
  have htrace : WordTrace (prefixWord ++ tailWord_6845463) baseStart_6845463 baseEnd_6845463 := by
    simpa [prefixWord, tailWord_6845463, baseEnd_6845463] using wordTrace_append hprefix tailTrace_6845463
  have hstable : (prefixWord ++ tailWord_6845463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845463).length < 2 ^ (prefixWord ++ tailWord_6845463).sum := by decide
  have hdescent : baseEnd_6845463 < baseStart_6845463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845469 : List Nat := [1, 4, 2, 2, 4, 10]
def baseStart_6845469 : Nat := 118140960795 + 6845469 * 2 ^ 59
def prefixEnd_6845469 : Nat := 4983230072969 + 3 ^ 40 * 6845469 * 2
def baseEnd_6845469 : Nat := 14465086018324209073069

theorem tailTrace_6845469 : CollatzResearch.WordTrace tailWord_6845469 prefixEnd_6845469 14465086018324209073069 := by
  unfold tailWord_6845469
  simp only [CollatzResearch.WordTrace]
  refine ⟨249674766037042400872467461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166449844024694933914978307 249674766037042400872467461)
  ·
    refine ⟨46814018631945450163587649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249674766037042400872467461 46814018631945450163587649)
    ·
      refine ⟨35110513973959087622690737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46814018631945450163587649 35110513973959087622690737)
      ·
        refine ⟨26332885480469315717018053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35110513973959087622690737 26332885480469315717018053)
        ·
          refine ⟨4937416027587996696940885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26332885480469315717018053 4937416027587996696940885)
          ·
            refine ⟨14465086018324209073069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4937416027587996696940885 14465086018324209073069)
            ·
              rfl

theorem cell23_6845469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 10].length) (baseStart_6845469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845469 prefixEnd_6845469 := by exact prefixLift 6845469
  have htrace : WordTrace (prefixWord ++ tailWord_6845469) baseStart_6845469 baseEnd_6845469 := by
    simpa [prefixWord, tailWord_6845469, baseEnd_6845469] using wordTrace_append hprefix tailTrace_6845469
  have hstable : (prefixWord ++ tailWord_6845469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845469).length < 2 ^ (prefixWord ++ tailWord_6845469).sum := by decide
  have hdescent : baseEnd_6845469 < baseStart_6845469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845496 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_6845496 : Nat := 118140960795 + 6845496 * 2 ^ 59
def prefixEnd_6845496 : Nat := 4983230072969 + 3 ^ 40 * 6845496 * 2
def baseEnd_6845496 : Nat := 3515029766430454199118143

theorem tailTrace_6845496 : CollatzResearch.WordTrace tailWord_6845496 prefixEnd_6845496 3515029766430454199118143 := by
  unfold tailWord_6845496
  simp only [CollatzResearch.WordTrace]
  refine ⟨124837875403972292241850171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166450500538629722989133561 124837875403972292241850171)
  ·
    refine ⟨187256813105958438362775257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124837875403972292241850171 187256813105958438362775257)
    ·
      refine ⟨140442609829468828772081443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187256813105958438362775257 140442609829468828772081443)
      ·
        refine ⟨210663914744203243158122165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140442609829468828772081443 210663914744203243158122165)
        ·
          refine ⟨19749742007269054046073953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210663914744203243158122165 19749742007269054046073953)
          ·
            refine ⟨14812306505451790534555465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19749742007269054046073953 14812306505451790534555465)
            ·
              refine ⟨11109229879088842900916599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14812306505451790534555465 11109229879088842900916599)
              ·
                refine ⟨16663844818633264351374899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11109229879088842900916599 16663844818633264351374899)
                ·
                  refine ⟨24995767227949896527062349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16663844818633264351374899 24995767227949896527062349)
                  ·
                    refine ⟨9373412710481211197648381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24995767227949896527062349 9373412710481211197648381)
                    ·
                      refine ⟨3515029766430454199118143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9373412710481211197648381 3515029766430454199118143)
                      ·
                        rfl

theorem cell23_6845496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_6845496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845496 prefixEnd_6845496 := by exact prefixLift 6845496
  have htrace : WordTrace (prefixWord ++ tailWord_6845496) baseStart_6845496 baseEnd_6845496 := by
    simpa [prefixWord, tailWord_6845496, baseEnd_6845496] using wordTrace_append hprefix tailTrace_6845496
  have hstable : (prefixWord ++ tailWord_6845496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845496).length < 2 ^ (prefixWord ++ tailWord_6845496).sum := by decide
  have hdescent : baseEnd_6845496 < baseStart_6845496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845512 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 1, 8]
def baseStart_6845512 : Nat := 118140960795 + 6845512 * 2 ^ 59
def prefixEnd_6845512 : Nat := 4983230072969 + 3 ^ 40 * 6845512 * 2
def baseEnd_6845512 : Nat := 1171679327373642045506023

theorem tailTrace_6845512 : CollatzResearch.WordTrace tailWord_6845512 prefixEnd_6845512 1171679327373642045506023 := by
  unfold tailWord_6845512
  simp only [CollatzResearch.WordTrace]
  refine ⟨124838167187943309608141395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166450889583924412810855193 124838167187943309608141395)
  ·
    refine ⟨187257250781914964412212093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124838167187943309608141395 187257250781914964412212093)
    ·
      refine ⟨70221469043218111654579535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187257250781914964412212093 70221469043218111654579535)
      ·
        refine ⟨105332203564827167481869303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70221469043218111654579535 105332203564827167481869303)
        ·
          refine ⟨157998305347240751222803955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105332203564827167481869303 157998305347240751222803955)
          ·
            refine ⟨236997458020861126834205933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157998305347240751222803955 236997458020861126834205933)
            ·
              refine ⟨88874046757822922562827225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236997458020861126834205933 88874046757822922562827225)
              ·
                refine ⟨66655535068367191922120419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88874046757822922562827225 66655535068367191922120419)
                ·
                  refine ⟨99983302602550787883180629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66655535068367191922120419 99983302602550787883180629)
                  ·
                    refine ⟨1171679327373642045506023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99983302602550787883180629 1171679327373642045506023)
                    ·
                      rfl

theorem cell23_6845512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_6845512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845512 prefixEnd_6845512 := by exact prefixLift 6845512
  have htrace : WordTrace (prefixWord ++ tailWord_6845512) baseStart_6845512 baseEnd_6845512 := by
    simpa [prefixWord, tailWord_6845512, baseEnd_6845512] using wordTrace_append hprefix tailTrace_6845512
  have hstable : (prefixWord ++ tailWord_6845512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845512).length < 2 ^ (prefixWord ++ tailWord_6845512).sum := by decide
  have hdescent : baseEnd_6845512 < baseStart_6845512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845557 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_6845557 : Nat := 118140960795 + 6845557 * 2 ^ 59
def prefixEnd_6845557 : Nat := 4983230072969 + 3 ^ 40 * 6845557 * 2
def baseEnd_6845557 : Nat := 3515061088750378460455363

theorem tailTrace_6845557 : CollatzResearch.WordTrace tailWord_6845557 prefixEnd_6845557 3515061088750378460455363 := by
  unfold tailWord_6845557
  simp only [CollatzResearch.WordTrace]
  refine ⟨249677975660723591901670925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166451983773815727934447283 249677975660723591901670925)
  ·
    refine ⟨93629240872771346963126597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249677975660723591901670925 93629240872771346963126597)
    ·
      refine ⟨17555482663644627555586237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93629240872771346963126597 17555482663644627555586237)
      ·
        refine ⟨6583305998866735333344839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17555482663644627555586237 6583305998866735333344839)
        ·
          refine ⟨9874958998300103000017259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6583305998866735333344839 9874958998300103000017259)
          ·
            refine ⟨14812438497450154500025889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9874958998300103000017259 14812438497450154500025889)
            ·
              refine ⟨11109328873087615875019417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14812438497450154500025889 11109328873087615875019417)
              ·
                refine ⟨8331996654815711906264563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11109328873087615875019417 8331996654815711906264563)
                ·
                  refine ⟨12497994982223567859396845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8331996654815711906264563 12497994982223567859396845)
                  ·
                    refine ⟨4686748118333837947273817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12497994982223567859396845 4686748118333837947273817)
                    ·
                      refine ⟨3515061088750378460455363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686748118333837947273817 3515061088750378460455363)
                      ·
                        rfl

theorem cell23_6845557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_6845557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845557 prefixEnd_6845557 := by exact prefixLift 6845557
  have htrace : WordTrace (prefixWord ++ tailWord_6845557) baseStart_6845557 baseEnd_6845557 := by
    simpa [prefixWord, tailWord_6845557, baseEnd_6845557] using wordTrace_append hprefix tailTrace_6845557
  have hstable : (prefixWord ++ tailWord_6845557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845557).length < 2 ^ (prefixWord ++ tailWord_6845557).sum := by decide
  have hdescent : baseEnd_6845557 < baseStart_6845557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845626 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2]
def baseStart_6845626 : Nat := 118140960795 + 6845626 * 2 ^ 59
def prefixEnd_6845626 : Nat := 4983230072969 + 3 ^ 40 * 6845626 * 2
def baseEnd_6845626 : Nat := 3515096518915538690492545

theorem tailTrace_6845626 : CollatzResearch.WordTrace tailWord_6845626 prefixEnd_6845626 3515096518915538690492545 := by
  unfold tailWord_6845626
  simp only [CollatzResearch.WordTrace]
  refine ⟨62420123074368404171483183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166453661531649077790621821 62420123074368404171483183)
  ·
    refine ⟨93630184611552606257224775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62420123074368404171483183 93630184611552606257224775)
    ·
      refine ⟨140445276917328909385837163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93630184611552606257224775 140445276917328909385837163)
      ·
        refine ⟨210667915375993364078755745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140445276917328909385837163 210667915375993364078755745)
        ·
          refine ⟨158000936531995023059066809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210667915375993364078755745 158000936531995023059066809)
          ·
            refine ⟨118500702398996267294300107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158000936531995023059066809 118500702398996267294300107)
            ·
              refine ⟨177751053598494400941450161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118500702398996267294300107 177751053598494400941450161)
              ·
                refine ⟨133313290198870800706087621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177751053598494400941450161 133313290198870800706087621)
                ·
                  refine ⟨24996241912288275132391429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133313290198870800706087621 24996241912288275132391429)
                  ·
                    refine ⟨4686795358554051587323393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24996241912288275132391429 4686795358554051587323393)
                    ·
                      refine ⟨3515096518915538690492545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686795358554051587323393 3515096518915538690492545)
                      ·
                        rfl

theorem cell23_6845626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2].length) (baseStart_6845626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845626 prefixEnd_6845626 := by exact prefixLift 6845626
  have htrace : WordTrace (prefixWord ++ tailWord_6845626) baseStart_6845626 baseEnd_6845626 := by
    simpa [prefixWord, tailWord_6845626, baseEnd_6845626] using wordTrace_append hprefix tailTrace_6845626
  have hstable : (prefixWord ++ tailWord_6845626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845626).length < 2 ^ (prefixWord ++ tailWord_6845626).sum := by decide
  have hdescent : baseEnd_6845626 < baseStart_6845626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845710 : List Nat := [4, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_6845710 : Nat := 118140960795 + 6845710 * 2 ^ 59
def prefixEnd_6845710 : Nat := 4983230072969 + 3 ^ 40 * 6845710 * 2
def baseEnd_6845710 : Nat := 3515139651290516361842159

theorem tailTrace_6845710 : CollatzResearch.WordTrace tailWord_6845710 prefixEnd_6845710 3515139651290516361842159 := by
  unfold tailWord_6845710
  simp only [CollatzResearch.WordTrace]
  refine ⟨31210444503646162378998823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166455704019446199354660389 31210444503646162378998823)
  ·
    refine ⟨46815666755469243568498235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31210444503646162378998823 46815666755469243568498235)
    ·
      refine ⟨70223500133203865352747353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46815666755469243568498235 70223500133203865352747353)
      ·
        refine ⟨52667625099902899014560515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70223500133203865352747353 52667625099902899014560515)
        ·
          refine ⟨79001437649854348521840773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52667625099902899014560515 79001437649854348521840773)
          ·
            refine ⟨14812769559347690347845145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79001437649854348521840773 14812769559347690347845145)
            ·
              refine ⟨11109577169510767760883859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14812769559347690347845145 11109577169510767760883859)
              ·
                refine ⟨16664365754266151641325789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11109577169510767760883859 16664365754266151641325789)
                ·
                  refine ⟨6249137157849806865497171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16664365754266151641325789 6249137157849806865497171)
                  ·
                    refine ⟨9373705736774710298245757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6249137157849806865497171 9373705736774710298245757)
                    ·
                      refine ⟨3515139651290516361842159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9373705736774710298245757 3515139651290516361842159)
                      ·
                        rfl

theorem cell23_6845710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_6845710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845710 prefixEnd_6845710 := by exact prefixLift 6845710
  have htrace : WordTrace (prefixWord ++ tailWord_6845710) baseStart_6845710 baseEnd_6845710 := by
    simpa [prefixWord, tailWord_6845710, baseEnd_6845710] using wordTrace_append hprefix tailTrace_6845710
  have hstable : (prefixWord ++ tailWord_6845710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845710).length < 2 ^ (prefixWord ++ tailWord_6845710).sum := by decide
  have hdescent : baseEnd_6845710 < baseStart_6845710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845730 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_6845730 : Nat := 118140960795 + 6845730 * 2 ^ 59
def prefixEnd_6845730 : Nat := 4983230072969 + 3 ^ 40 * 6845730 * 2
def baseEnd_6845730 : Nat := 1171716640301202094530689

theorem tailTrace_6845730 : CollatzResearch.WordTrace tailWord_6845730 prefixEnd_6845730 1171716640301202094530689 := by
  unfold tailWord_6845730
  simp only [CollatzResearch.WordTrace]
  refine ⟨62421071372274210611929661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166456190326064561631812429 62421071372274210611929661)
  ·
    refine ⟨23407901764602828979473623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62421071372274210611929661 23407901764602828979473623)
    ·
      refine ⟨35111852646904243469210435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23407901764602828979473623 35111852646904243469210435)
      ·
        refine ⟨52667778970356365203815653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35111852646904243469210435 52667778970356365203815653)
        ·
          refine ⟨9875208556941818475715435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52667778970356365203815653 9875208556941818475715435)
          ·
            refine ⟨14812812835412727713573153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9875208556941818475715435 14812812835412727713573153)
            ·
              refine ⟨11109609626559545785179865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14812812835412727713573153 11109609626559545785179865)
              ·
                refine ⟨8332207219919659338884899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11109609626559545785179865 8332207219919659338884899)
                ·
                  refine ⟨12498310829879489008327349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8332207219919659338884899 12498310829879489008327349)
                  ·
                    refine ⟨1171716640301202094530689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12498310829879489008327349 1171716640301202094530689)
                    ·
                      rfl

theorem cell23_6845730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_6845730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845730 prefixEnd_6845730 := by exact prefixLift 6845730
  have htrace : WordTrace (prefixWord ++ tailWord_6845730) baseStart_6845730 baseEnd_6845730 := by
    simpa [prefixWord, tailWord_6845730, baseEnd_6845730] using wordTrace_append hprefix tailTrace_6845730
  have hstable : (prefixWord ++ tailWord_6845730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845730).length < 2 ^ (prefixWord ++ tailWord_6845730).sum := by decide
  have hdescent : baseEnd_6845730 < baseStart_6845730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845733 : List Nat := [1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_6845733 : Nat := 118140960795 + 6845733 * 2 ^ 59
def prefixEnd_6845733 : Nat := 4983230072969 + 3 ^ 40 * 6845733 * 2
def baseEnd_6845733 : Nat := 3515151461345569771854553

theorem tailTrace_6845733 : CollatzResearch.WordTrace tailWord_6845733 prefixEnd_6845733 3515151461345569771854553 := by
  unfold tailWord_6845733
  simp only [CollatzResearch.WordTrace]
  refine ⟨249684394908085973960077853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166456263272057315973385235 249684394908085973960077853)
  ·
    refine ⟨93631648090532240235029195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249684394908085973960077853 93631648090532240235029195)
    ·
      refine ⟨140447472135798360352543793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93631648090532240235029195 140447472135798360352543793)
      ·
        refine ⟨105335604101848770264407845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140447472135798360352543793 105335604101848770264407845)
        ·
          refine ⟨19750425769096644424576471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105335604101848770264407845 19750425769096644424576471)
          ·
            refine ⟨29625638653644966636864707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19750425769096644424576471 29625638653644966636864707)
            ·
              refine ⟨44438457980467449955297061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29625638653644966636864707 44438457980467449955297061)
              ·
                refine ⟨8332210871337646866618199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44438457980467449955297061 8332210871337646866618199)
                ·
                  refine ⟨12498316307006470299927299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8332210871337646866618199 12498316307006470299927299)
                  ·
                    refine ⟨18747474460509705449890949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12498316307006470299927299 18747474460509705449890949)
                    ·
                      refine ⟨3515151461345569771854553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18747474460509705449890949 3515151461345569771854553)
                      ·
                        rfl

theorem cell23_6845733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_6845733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845733 prefixEnd_6845733 := by exact prefixLift 6845733
  have htrace : WordTrace (prefixWord ++ tailWord_6845733) baseStart_6845733 baseEnd_6845733 := by
    simpa [prefixWord, tailWord_6845733, baseEnd_6845733] using wordTrace_append hprefix tailTrace_6845733
  have hstable : (prefixWord ++ tailWord_6845733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845733).length < 2 ^ (prefixWord ++ tailWord_6845733).sum := by decide
  have hdescent : baseEnd_6845733 < baseStart_6845733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845756 : List Nat := [2, 2, 2, 2, 1, 5, 9]
def baseStart_6845756 : Nat := 118140960795 + 6845756 * 2 ^ 59
def prefixEnd_6845756 : Nat := 4983230072969 + 3 ^ 40 * 6845756 * 2
def baseEnd_6845756 : Nat := 43397077424699051627987

theorem tailTrace_6845756 : CollatzResearch.WordTrace tailWord_6845756 prefixEnd_6845756 43397077424699051627987 := by
  unfold tailWord_6845756
  simp only [CollatzResearch.WordTrace]
  refine ⟨124842616893501324444082561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166456822524668432592110081 124842616893501324444082561)
  ·
    refine ⟨93631962670125993333061921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124842616893501324444082561 93631962670125993333061921)
    ·
      refine ⟨70223972002594494999796441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93631962670125993333061921 70223972002594494999796441)
      ·
        refine ⟨52667979001945871249847331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70223972002594494999796441 52667979001945871249847331)
        ·
          refine ⟨79001968502918806874770997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52667979001945871249847331 79001968502918806874770997)
          ·
            refine ⟨7406434547148638144509781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79001968502918806874770997 7406434547148638144509781)
            ·
              refine ⟨43397077424699051627987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7406434547148638144509781 43397077424699051627987)
              ·
                rfl

theorem cell23_6845756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 9].length) (baseStart_6845756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845756 prefixEnd_6845756 := by exact prefixLift 6845756
  have htrace : WordTrace (prefixWord ++ tailWord_6845756) baseStart_6845756 baseEnd_6845756 := by
    simpa [prefixWord, tailWord_6845756, baseEnd_6845756] using wordTrace_append hprefix tailTrace_6845756
  have hstable : (prefixWord ++ tailWord_6845756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845756).length < 2 ^ (prefixWord ++ tailWord_6845756).sum := by decide
  have hdescent : baseEnd_6845756 < baseStart_6845756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845767 : List Nat := [1, 1, 4, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_6845767 : Nat := 118140960795 + 6845767 * 2 ^ 59
def prefixEnd_6845767 : Nat := 4983230072969 + 3 ^ 40 * 6845767 * 2
def baseEnd_6845767 : Nat := 3515168919687822638829397

theorem tailTrace_6845767 : CollatzResearch.WordTrace tailWord_6845767 prefixEnd_6845767 3515168919687822638829397 := by
  unfold tailWord_6845767
  simp only [CollatzResearch.WordTrace]
  refine ⟨249685634989962797766815555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166457089993308531844543703 249685634989962797766815555)
  ·
    refine ⟨374528452484944196650223333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249685634989962797766815555 374528452484944196650223333)
    ·
      refine ⟨70224084840927036871916875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374528452484944196650223333 70224084840927036871916875)
      ·
        refine ⟨105336127261390555307875313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70224084840927036871916875 105336127261390555307875313)
        ·
          refine ⟨79002095446042916480906485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105336127261390555307875313 79002095446042916480906485)
          ·
            refine ⟨7406446448066523420084983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79002095446042916480906485 7406446448066523420084983)
            ·
              refine ⟨11109669672099785130127475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406446448066523420084983 11109669672099785130127475)
              ·
                refine ⟨16664504508149677695191213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11109669672099785130127475 16664504508149677695191213)
                ·
                  refine ⟨6249189190556129135696705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16664504508149677695191213 6249189190556129135696705)
                  ·
                    refine ⟨4686891892917096851772529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6249189190556129135696705 4686891892917096851772529)
                    ·
                      refine ⟨3515168919687822638829397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4686891892917096851772529 3515168919687822638829397)
                      ·
                        rfl

theorem cell23_6845767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_6845767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845767 prefixEnd_6845767 := by exact prefixLift 6845767
  have htrace : WordTrace (prefixWord ++ tailWord_6845767) baseStart_6845767 baseEnd_6845767 := by
    simpa [prefixWord, tailWord_6845767, baseEnd_6845767] using wordTrace_append hprefix tailTrace_6845767
  have hstable : (prefixWord ++ tailWord_6845767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845767).length < 2 ^ (prefixWord ++ tailWord_6845767).sum := by decide
  have hdescent : baseEnd_6845767 < baseStart_6845767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845800 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_6845800 : Nat := 118140960795 + 6845800 * 2 ^ 59
def prefixEnd_6845800 : Nat := 4983230072969 + 3 ^ 40 * 6845800 * 2
def baseEnd_6845800 : Nat := 3515185864549421009716745

theorem tailTrace_6845800 : CollatzResearch.WordTrace tailWord_6845800 prefixEnd_6845800 3515185864549421009716745 := by
  unfold tailWord_6845800
  simp only [CollatzResearch.WordTrace]
  refine ⟨124843419299421622201383427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166457892399228829601844569 124843419299421622201383427)
  ·
    refine ⟨187265128949132433302075141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124843419299421622201383427 187265128949132433302075141)
    ·
      refine ⟨35112211677962331244139089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187265128949132433302075141 35112211677962331244139089)
      ·
        refine ⟨26334158758471748433104317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35112211677962331244139089 26334158758471748433104317)
        ·
          refine ⟨9875309534426905662414119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26334158758471748433104317 9875309534426905662414119)
          ·
            refine ⟨14812964301640358493621179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9875309534426905662414119 14812964301640358493621179)
            ·
              refine ⟨22219446452460537740431769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14812964301640358493621179 22219446452460537740431769)
              ·
                refine ⟨16664584839345403305323827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22219446452460537740431769 16664584839345403305323827)
                ·
                  refine ⟨24996877259018104957985741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16664584839345403305323827 24996877259018104957985741)
                  ·
                    refine ⟨9373828972131789359244653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24996877259018104957985741 9373828972131789359244653)
                    ·
                      refine ⟨3515185864549421009716745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9373828972131789359244653 3515185864549421009716745)
                      ·
                        rfl

theorem cell23_6845800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_6845800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845800 prefixEnd_6845800 := by exact prefixLift 6845800
  have htrace : WordTrace (prefixWord ++ tailWord_6845800) baseStart_6845800 baseEnd_6845800 := by
    simpa [prefixWord, tailWord_6845800, baseEnd_6845800] using wordTrace_append hprefix tailTrace_6845800
  have hstable : (prefixWord ++ tailWord_6845800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845800).length < 2 ^ (prefixWord ++ tailWord_6845800).sum := by decide
  have hdescent : baseEnd_6845800 < baseStart_6845800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845833 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 2, 6]
def baseStart_6845833 : Nat := 118140960795 + 6845833 * 2 ^ 59
def prefixEnd_6845833 : Nat := 4983230072969 + 3 ^ 40 * 6845833 * 2
def baseEnd_6845833 : Nat := 1171734269803673126868031

theorem tailTrace_6845833 : CollatzResearch.WordTrace tailWord_6845833 prefixEnd_6845833 1171734269803673126868031 := by
  unfold tailWord_6845833
  simp only [CollatzResearch.WordTrace]
  refine ⟨249688042207723691038718153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166458694805149127359145435 249688042207723691038718153)
  ·
    refine ⟨187266031655792768279038615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249688042207723691038718153 187266031655792768279038615)
    ·
      refine ⟨280899047483689152418557923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187266031655792768279038615 280899047483689152418557923)
      ·
        refine ⟨421348571225533728627836885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280899047483689152418557923 421348571225533728627836885)
        ·
          refine ⟨9875357138098446764714927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 421348571225533728627836885 9875357138098446764714927)
          ·
            refine ⟨14813035707147670147072391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9875357138098446764714927 14813035707147670147072391)
            ·
              refine ⟨22219553560721505220608587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14813035707147670147072391 22219553560721505220608587)
              ·
                refine ⟨33329330341082257830912881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22219553560721505220608587 33329330341082257830912881)
                ·
                  refine ⟨24996997755811693373184661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33329330341082257830912881 24996997755811693373184661)
                  ·
                    refine ⟨1171734269803673126868031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24996997755811693373184661 1171734269803673126868031)
                    ·
                      rfl

theorem cell23_6845833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_6845833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845833 prefixEnd_6845833 := by exact prefixLift 6845833
  have htrace : WordTrace (prefixWord ++ tailWord_6845833) baseStart_6845833 baseEnd_6845833 := by
    simpa [prefixWord, tailWord_6845833, baseEnd_6845833] using wordTrace_append hprefix tailTrace_6845833
  have hstable : (prefixWord ++ tailWord_6845833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845833).length < 2 ^ (prefixWord ++ tailWord_6845833).sum := by decide
  have hdescent : baseEnd_6845833 < baseStart_6845833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845873 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_6845873 : Nat := 118140960795 + 6845873 * 2 ^ 59
def prefixEnd_6845873 : Nat := 4983230072969 + 3 ^ 40 * 6845873 * 2
def baseEnd_6845873 : Nat := 3515223348637199224103909

theorem tailTrace_6845873 : CollatzResearch.WordTrace tailWord_6845873 prefixEnd_6845873 3515223348637199224103909 := by
  unfold tailWord_6845873
  simp only [CollatzResearch.WordTrace]
  refine ⟨249689501127578777870174273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166459667418385851913449515 249689501127578777870174273)
  ·
    refine ⟨187267125845684083402630705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249689501127578777870174273 187267125845684083402630705)
    ·
      refine ⟨140450344384263062551973029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187267125845684083402630705 140450344384263062551973029)
      ·
        refine ⟨26334439572049324228494943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140450344384263062551973029 26334439572049324228494943)
        ·
          refine ⟨39501659358073986342742415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26334439572049324228494943 39501659358073986342742415)
          ·
            refine ⟨59252489037110979514113623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39501659358073986342742415 59252489037110979514113623)
            ·
              refine ⟨88878733555666469271170435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59252489037110979514113623 88878733555666469271170435)
              ·
                refine ⟨133318100333499703906755653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88878733555666469271170435 133318100333499703906755653)
                ·
                  refine ⟨24997143812531194482516685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133318100333499703906755653 24997143812531194482516685)
                  ·
                    refine ⟨9373928929699197930943757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24997143812531194482516685 9373928929699197930943757)
                    ·
                      refine ⟨3515223348637199224103909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9373928929699197930943757 3515223348637199224103909)
                      ·
                        rfl

theorem cell23_6845873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_6845873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845873 prefixEnd_6845873 := by exact prefixLift 6845873
  have htrace : WordTrace (prefixWord ++ tailWord_6845873) baseStart_6845873 baseEnd_6845873 := by
    simpa [prefixWord, tailWord_6845873, baseEnd_6845873] using wordTrace_append hprefix tailTrace_6845873
  have hstable : (prefixWord ++ tailWord_6845873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845873).length < 2 ^ (prefixWord ++ tailWord_6845873).sum := by decide
  have hdescent : baseEnd_6845873 < baseStart_6845873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845910 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_6845910 : Nat := 118140960795 + 6845910 * 2 ^ 59
def prefixEnd_6845910 : Nat := 4983230072969 + 3 ^ 40 * 6845910 * 2
def baseEnd_6845910 : Nat := 1171747449140471859780413

theorem tailTrace_6845910 : CollatzResearch.WordTrace tailWord_6845910 prefixEnd_6845910 1171747449140471859780413 := by
  unfold tailWord_6845910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605678164277795824329449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166460567085629822126180789 15605678164277795824329449)
  ·
    refine ⟨11704258623208346868247087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15605678164277795824329449 11704258623208346868247087)
    ·
      refine ⟨17556387934812520302370631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11704258623208346868247087 17556387934812520302370631)
      ·
        refine ⟨26334581902218780453555947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17556387934812520302370631 26334581902218780453555947)
        ·
          refine ⟨39501872853328170680333921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26334581902218780453555947 39501872853328170680333921)
          ·
            refine ⟨29626404639996128010250441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39501872853328170680333921 29626404639996128010250441)
            ·
              refine ⟨22219803479997096007687831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29626404639996128010250441 22219803479997096007687831)
              ·
                refine ⟨33329705219995644011531747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22219803479997096007687831 33329705219995644011531747)
                ·
                  refine ⟨49994557829993466017297621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33329705219995644011531747 49994557829993466017297621)
                  ·
                    refine ⟨1171747449140471859780413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49994557829993466017297621 1171747449140471859780413)
                    ·
                      rfl

theorem cell23_6845910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_6845910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845910 prefixEnd_6845910 := by exact prefixLift 6845910
  have htrace : WordTrace (prefixWord ++ tailWord_6845910) baseStart_6845910 baseEnd_6845910 := by
    simpa [prefixWord, tailWord_6845910, baseEnd_6845910] using wordTrace_append hprefix tailTrace_6845910
  have hstable : (prefixWord ++ tailWord_6845910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845910).length < 2 ^ (prefixWord ++ tailWord_6845910).sum := by decide
  have hdescent : baseEnd_6845910 < baseStart_6845910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6845913 : List Nat := [1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_6845913 : Nat := 118140960795 + 6845913 * 2 ^ 59
def prefixEnd_6845913 : Nat := 4983230072969 + 3 ^ 40 * 6845913 * 2
def baseEnd_6845913 : Nat := 3515243887863379067603725

theorem tailTrace_6845913 : CollatzResearch.WordTrace tailWord_6845913 prefixEnd_6845913 3515243887863379067603725 := by
  unfold tailWord_6845913
  simp only [CollatzResearch.WordTrace]
  refine ⟨249690960047433864701630393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166460640031622576467753595 249690960047433864701630393)
  ·
    refine ⟨187268220035575398526222795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249690960047433864701630393 187268220035575398526222795)
    ·
      refine ⟨280902330053363097789334193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187268220035575398526222795 280902330053363097789334193)
      ·
        refine ⟨210676747540022323342000645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280902330053363097789334193 210676747540022323342000645)
        ·
          refine ⟨39501890163754185626625121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210676747540022323342000645 39501890163754185626625121)
          ·
            refine ⟨29626417622815639219968841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39501890163754185626625121 29626417622815639219968841)
            ·
              refine ⟨22219813217111729414976631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29626417622815639219968841 22219813217111729414976631)
              ·
                refine ⟨33329719825667594122464947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22219813217111729414976631 33329719825667594122464947)
                ·
                  refine ⟨49994579738501391183697421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33329719825667594122464947 49994579738501391183697421)
                  ·
                    refine ⟨18747967401938021693886533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49994579738501391183697421 18747967401938021693886533)
                    ·
                      refine ⟨3515243887863379067603725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18747967401938021693886533 3515243887863379067603725)
                      ·
                        rfl

theorem cell23_6845913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_6845913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6845913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6845913 prefixEnd_6845913 := by exact prefixLift 6845913
  have htrace : WordTrace (prefixWord ++ tailWord_6845913) baseStart_6845913 baseEnd_6845913 := by
    simpa [prefixWord, tailWord_6845913, baseEnd_6845913] using wordTrace_append hprefix tailTrace_6845913
  have hstable : (prefixWord ++ tailWord_6845913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6845913).length < 2 ^ (prefixWord ++ tailWord_6845913).sum := by decide
  have hdescent : baseEnd_6845913 < baseStart_6845913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6845913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846030 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_6846030 : Nat := 118140960795 + 6846030 * 2 ^ 59
def prefixEnd_6846030 : Nat := 4983230072969 + 3 ^ 40 * 6846030 * 2
def baseEnd_6846030 : Nat := 1171767988366651703280229

theorem tailTrace_6846030 : CollatzResearch.WordTrace tailWord_6846030 prefixEnd_6846030 1171767988366651703280229 := by
  unfold tailWord_6846030
  simp only [CollatzResearch.WordTrace]
  refine ⟨31211903423501249210454943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166463484925339995789093029 31211903423501249210454943)
  ·
    refine ⟨46817855135251873815682415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31211903423501249210454943 46817855135251873815682415)
    ·
      refine ⟨70226782702877810723523623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46817855135251873815682415 70226782702877810723523623)
      ·
        refine ⟨105340174054316716085285435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70226782702877810723523623 105340174054316716085285435)
        ·
          refine ⟨158010261081475074127928153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105340174054316716085285435 158010261081475074127928153)
          ·
            refine ⟨118507695811106305595946115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158010261081475074127928153 118507695811106305595946115)
            ·
              refine ⟨177761543716659458393919173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118507695811106305595946115 177761543716659458393919173)
              ·
                refine ⟨33330289446873648448859845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177761543716659458393919173 33330289446873648448859845)
                ·
                  refine ⟨6249429271288809084161221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33330289446873648448859845 6249429271288809084161221)
                  ·
                    refine ⟨1171767988366651703280229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6249429271288809084161221 1171767988366651703280229)
                    ·
                      rfl

theorem cell23_6846030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_6846030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846030 prefixEnd_6846030 := by exact prefixLift 6846030
  have htrace : WordTrace (prefixWord ++ tailWord_6846030) baseStart_6846030 baseEnd_6846030 := by
    simpa [prefixWord, tailWord_6846030, baseEnd_6846030] using wordTrace_append hprefix tailTrace_6846030
  have hstable : (prefixWord ++ tailWord_6846030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846030).length < 2 ^ (prefixWord ++ tailWord_6846030).sum := by decide
  have hdescent : baseEnd_6846030 < baseStart_6846030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846034 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_6846034 : Nat := 118140960795 + 6846034 * 2 ^ 59
def prefixEnd_6846034 : Nat := 4983230072969 + 3 ^ 40 * 6846034 * 2
def baseEnd_6846034 : Nat := 1171768673007524364730223

theorem tailTrace_6846034 : CollatzResearch.WordTrace tailWord_6846034 prefixEnd_6846034 1171768673007524364730223 := by
  unfold tailWord_6846034
  simp only [CollatzResearch.WordTrace]
  refine ⟨62423843319998875591696289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166463582186663668244523437 62423843319998875591696289)
  ·
    refine ⟨46817882489999156693772217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62423843319998875591696289 46817882489999156693772217)
    ·
      refine ⟨35113411867499367520329163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46817882489999156693772217 35113411867499367520329163)
      ·
        refine ⟨52670117801249051280493745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35113411867499367520329163 52670117801249051280493745)
        ·
          refine ⟨39502588350936788460370309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52670117801249051280493745 39502588350936788460370309)
          ·
            refine ⟨7406735315800647836319433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39502588350936788460370309 7406735315800647836319433)
            ·
              refine ⟨5555051486850485877239575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7406735315800647836319433 5555051486850485877239575)
              ·
                refine ⟨8332577230275728815859363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555051486850485877239575 8332577230275728815859363)
                ·
                  refine ⟨12498865845413593223789045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8332577230275728815859363 12498865845413593223789045)
                  ·
                    refine ⟨1171768673007524364730223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12498865845413593223789045 1171768673007524364730223)
                    ·
                      rfl

theorem cell23_6846034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_6846034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846034 prefixEnd_6846034 := by exact prefixLift 6846034
  have htrace : WordTrace (prefixWord ++ tailWord_6846034) baseStart_6846034 baseEnd_6846034 := by
    simpa [prefixWord, tailWord_6846034, baseEnd_6846034] using wordTrace_append hprefix tailTrace_6846034
  have hstable : (prefixWord ++ tailWord_6846034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846034).length < 2 ^ (prefixWord ++ tailWord_6846034).sum := by decide
  have hdescent : baseEnd_6846034 < baseStart_6846034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846037 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_6846037 : Nat := 118140960795 + 6846037 * 2 ^ 59
def prefixEnd_6846037 : Nat := 4983230072969 + 3 ^ 40 * 6846037 * 2
def baseEnd_6846037 : Nat := 3515307559464536582453155

theorem tailTrace_6846037 : CollatzResearch.WordTrace tailWord_6846037 prefixEnd_6846037 3515307559464536582453155 := by
  unfold tailWord_6846037
  simp only [CollatzResearch.WordTrace]
  refine ⟨249695482698984633879144365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166463655132656422586096243 249695482698984633879144365)
  ·
    refine ⟨93635806012119237704679137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249695482698984633879144365 93635806012119237704679137)
    ·
      refine ⟨70226854509089428278509353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93635806012119237704679137 70226854509089428278509353)
      ·
        refine ⟨52670140881817071208882015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70226854509089428278509353 52670140881817071208882015)
        ·
          refine ⟨79005211322725606813323023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52670140881817071208882015 79005211322725606813323023)
          ·
            refine ⟨118507816984088410219984535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79005211322725606813323023 118507816984088410219984535)
            ·
              refine ⟨177761725476132615329976803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118507816984088410219984535 177761725476132615329976803)
              ·
                refine ⟨266642588214198922994965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177761725476132615329976803 266642588214198922994965205)
                ·
                  refine ⟨6249435661270287257694497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266642588214198922994965205 6249435661270287257694497)
                  ·
                    refine ⟨4687076745952715443270873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6249435661270287257694497 4687076745952715443270873)
                    ·
                      refine ⟨3515307559464536582453155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687076745952715443270873 3515307559464536582453155)
                      ·
                        rfl

theorem cell23_6846037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_6846037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846037 prefixEnd_6846037 := by exact prefixLift 6846037
  have htrace : WordTrace (prefixWord ++ tailWord_6846037) baseStart_6846037 baseEnd_6846037 := by
    simpa [prefixWord, tailWord_6846037, baseEnd_6846037] using wordTrace_append hprefix tailTrace_6846037
  have hstable : (prefixWord ++ tailWord_6846037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846037).length < 2 ^ (prefixWord ++ tailWord_6846037).sum := by decide
  have hdescent : baseEnd_6846037 < baseStart_6846037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846038 : List Nat := [5, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_6846038 : Nat := 118140960795 + 6846038 * 2 ^ 59
def prefixEnd_6846038 : Nat := 4983230072969 + 3 ^ 40 * 6846038 * 2
def baseEnd_6846038 : Nat := 390589785882799008726739

theorem tailTrace_6846038 : CollatzResearch.WordTrace tailWord_6846038 prefixEnd_6846038 390589785882799008726739 := by
  unfold tailWord_6846038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605969948248813190620673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166463679447987340699953845 15605969948248813190620673)
  ·
    refine ⟨11704477461186609892965505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15605969948248813190620673 11704477461186609892965505)
    ·
      refine ⟨8778358095889957419724129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11704477461186609892965505 8778358095889957419724129)
      ·
        refine ⟨6583768571917468064793097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8778358095889957419724129 6583768571917468064793097)
        ·
          refine ⟨4937826428938101048594823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6583768571917468064793097 4937826428938101048594823)
          ·
            refine ⟨7406739643407151572892235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937826428938101048594823 7406739643407151572892235)
            ·
              refine ⟨11110109465110727359338353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406739643407151572892235 11110109465110727359338353)
              ·
                refine ⟨8332582098833045519503765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110109465110727359338353 8332582098833045519503765)
                ·
                  refine ⟨390589785882799008726739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8332582098833045519503765 390589785882799008726739)
                  ·
                    rfl

theorem cell23_6846038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_6846038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846038 prefixEnd_6846038 := by exact prefixLift 6846038
  have htrace : WordTrace (prefixWord ++ tailWord_6846038) baseStart_6846038 baseEnd_6846038 := by
    simpa [prefixWord, tailWord_6846038, baseEnd_6846038] using wordTrace_append hprefix tailTrace_6846038
  have hstable : (prefixWord ++ tailWord_6846038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846038).length < 2 ^ (prefixWord ++ tailWord_6846038).sum := by decide
  have hdescent : baseEnd_6846038 < baseStart_6846038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846064 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 2, 4]
def baseStart_6846064 : Nat := 118140960795 + 6846064 * 2 ^ 59
def prefixEnd_6846064 : Nat := 4983230072969 + 3 ^ 40 * 6846064 * 2
def baseEnd_6846064 : Nat := 1171773807814069325605177

theorem tailTrace_6846064 : CollatzResearch.WordTrace tailWord_6846064 prefixEnd_6846064 1171773807814069325605177 := by
  unfold tailWord_6846064
  simp only [CollatzResearch.WordTrace]
  refine ⟨124848233734943408745188623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166464311646591211660251497 124848233734943408745188623)
  ·
    refine ⟨187272350602415113117782935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124848233734943408745188623 187272350602415113117782935)
    ·
      refine ⟨280908525903622669676674403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187272350602415113117782935 280908525903622669676674403)
      ·
        refine ⟨421362788855434004515011605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280908525903622669676674403 421362788855434004515011605)
        ·
          refine ⟨19751380727598468961641169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 421362788855434004515011605 19751380727598468961641169)
          ·
            refine ⟨14813535545698851721230877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19751380727598468961641169 14813535545698851721230877)
            ·
              refine ⟨5555075829637069395461579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14813535545698851721230877 5555075829637069395461579)
              ·
                refine ⟨8332613744455604093192369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555075829637069395461579 8332613744455604093192369)
                ·
                  refine ⟨6249460308341703069894277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8332613744455604093192369 6249460308341703069894277)
                  ·
                    refine ⟨1171773807814069325605177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6249460308341703069894277 1171773807814069325605177)
                    ·
                      rfl

theorem cell23_6846064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 2, 4].length) (baseStart_6846064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846064 prefixEnd_6846064 := by exact prefixLift 6846064
  have htrace : WordTrace (prefixWord ++ tailWord_6846064) baseStart_6846064 baseEnd_6846064 := by
    simpa [prefixWord, tailWord_6846064, baseEnd_6846064] using wordTrace_append hprefix tailTrace_6846064
  have hstable : (prefixWord ++ tailWord_6846064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846064).length < 2 ^ (prefixWord ++ tailWord_6846064).sum := by decide
  have hdescent : baseEnd_6846064 < baseStart_6846064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846077 : List Nat := [1, 4, 1, 1, 4, 3, 2, 7]
def baseStart_6846077 : Nat := 118140960795 + 6846077 * 2 ^ 59
def prefixEnd_6846077 : Nat := 4983230072969 + 3 ^ 40 * 6846077 * 2
def baseEnd_6846077 : Nat := 130197336988545052813073

theorem tailTrace_6846077 : CollatzResearch.WordTrace tailWord_6846077 prefixEnd_6846077 130197336988545052813073 := by
  unfold tailWord_6846077
  simp only [CollatzResearch.WordTrace]
  refine ⟨249696941618839720710600485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166464627745893147140400323 249696941618839720710600485)
  ·
    refine ⟨46818176553532447633237591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249696941618839720710600485 46818176553532447633237591)
    ·
      refine ⟨70227264830298671449856387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46818176553532447633237591 70227264830298671449856387)
      ·
        refine ⟨105340897245448007174784581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70227264830298671449856387 105340897245448007174784581)
        ·
          refine ⟨19751418233521501345272109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105340897245448007174784581 19751418233521501345272109)
          ·
            refine ⟨7406781837570563004477041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19751418233521501345272109 7406781837570563004477041)
            ·
              refine ⟨5555086378177922253357781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7406781837570563004477041 5555086378177922253357781)
              ·
                refine ⟨130197336988545052813073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5555086378177922253357781 130197336988545052813073)
                ·
                  rfl

theorem cell23_6846077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 7].length) (baseStart_6846077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846077 prefixEnd_6846077 := by exact prefixLift 6846077
  have htrace : WordTrace (prefixWord ++ tailWord_6846077) baseStart_6846077 baseEnd_6846077 := by
    simpa [prefixWord, tailWord_6846077, baseEnd_6846077] using wordTrace_append hprefix tailTrace_6846077
  have hstable : (prefixWord ++ tailWord_6846077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846077).length < 2 ^ (prefixWord ++ tailWord_6846077).sum := by decide
  have hdescent : baseEnd_6846077 < baseStart_6846077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846087 : List Nat := [1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_6846087 : Nat := 118140960795 + 6846087 * 2 ^ 59
def prefixEnd_6846087 : Nat := 4983230072969 + 3 ^ 40 * 6846087 * 2
def baseEnd_6846087 : Nat := 3515333233497261386827925

theorem tailTrace_6846087 : CollatzResearch.WordTrace tailWord_6846087 prefixEnd_6846087 3515333233497261386827925 := by
  unfold tailWord_6846087
  simp only [CollatzResearch.WordTrace]
  refine ⟨249697306348803492418464515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166464870899202328278976343 249697306348803492418464515)
  ·
    refine ⟨374545959523205238627696773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249697306348803492418464515 374545959523205238627696773)
    ·
      refine ⟨70227367410600982242693145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374545959523205238627696773 70227367410600982242693145)
      ·
        refine ⟨52670525557950736682019859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70227367410600982242693145 52670525557950736682019859)
        ·
          refine ⟨79005788336926105023029789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52670525557950736682019859 79005788336926105023029789)
          ·
            refine ⟨29627170626347289383636171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79005788336926105023029789 29627170626347289383636171)
            ·
              refine ⟨44440755939520934075454257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29627170626347289383636171 44440755939520934075454257)
              ·
                refine ⟨33330566954640700556590693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44440755939520934075454257 33330566954640700556590693)
                ·
                  refine ⟨6249481303995131354360755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33330566954640700556590693 6249481303995131354360755)
                  ·
                    refine ⟨9374221955992697031541133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6249481303995131354360755 9374221955992697031541133)
                    ·
                      refine ⟨3515333233497261386827925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9374221955992697031541133 3515333233497261386827925)
                      ·
                        rfl

theorem cell23_6846087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_6846087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846087 prefixEnd_6846087 := by exact prefixLift 6846087
  have htrace : WordTrace (prefixWord ++ tailWord_6846087) baseStart_6846087 baseEnd_6846087 := by
    simpa [prefixWord, tailWord_6846087, baseEnd_6846087] using wordTrace_append hprefix tailTrace_6846087
  have hstable : (prefixWord ++ tailWord_6846087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846087).length < 2 ^ (prefixWord ++ tailWord_6846087).sum := by decide
  have hdescent : baseEnd_6846087 < baseStart_6846087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846127 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 1, 4, 2]
def baseStart_6846127 : Nat := 118140960795 + 6846127 * 2 ^ 59
def prefixEnd_6846127 : Nat := 4983230072969 + 3 ^ 40 * 6846127 * 2
def baseEnd_6846127 : Nat := 3515353772723441230327741

theorem tailTrace_6846127 : CollatzResearch.WordTrace tailWord_6846127 prefixEnd_6846127 3515353772723441230327741 := by
  unfold tailWord_6846127
  simp only [CollatzResearch.WordTrace]
  refine ⟨249698765268658579249920635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166465843512439052833280423 249698765268658579249920635)
  ·
    refine ⟨374548147902987868874880953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249698765268658579249920635 374548147902987868874880953)
    ·
      refine ⟨280911110927240901656160715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374548147902987868874880953 280911110927240901656160715)
      ·
        refine ⟨421366666390861352484241073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280911110927240901656160715 421366666390861352484241073)
        ·
          refine ⟨316024999793146014363180805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421366666390861352484241073 316024999793146014363180805)
          ·
            refine ⟨59254687461214877693096401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316024999793146014363180805 59254687461214877693096401)
            ·
              refine ⟨44441015595911158269822301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59254687461214877693096401 44441015595911158269822301)
              ·
                refine ⟨16665380848466684351183363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44441015595911158269822301 16665380848466684351183363)
                ·
                  refine ⟨24998071272700026526775045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16665380848466684351183363 24998071272700026526775045)
                  ·
                    refine ⟨4687138363631254973770321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24998071272700026526775045 4687138363631254973770321)
                    ·
                      refine ⟨3515353772723441230327741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687138363631254973770321 3515353772723441230327741)
                      ·
                        rfl

theorem cell23_6846127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 1, 4, 2].length) (baseStart_6846127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846127 prefixEnd_6846127 := by exact prefixLift 6846127
  have htrace : WordTrace (prefixWord ++ tailWord_6846127) baseStart_6846127 baseEnd_6846127 := by
    simpa [prefixWord, tailWord_6846127, baseEnd_6846127] using wordTrace_append hprefix tailTrace_6846127
  have hstable : (prefixWord ++ tailWord_6846127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846127).length < 2 ^ (prefixWord ++ tailWord_6846127).sum := by decide
  have hdescent : baseEnd_6846127 < baseStart_6846127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846130 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_6846130 : Nat := 118140960795 + 6846130 * 2 ^ 59
def prefixEnd_6846130 : Nat := 4983230072969 + 3 ^ 40 * 6846130 * 2
def baseEnd_6846130 : Nat := 3515355313165404718590227

theorem tailTrace_6846130 : CollatzResearch.WordTrace tailWord_6846130 prefixEnd_6846130 3515355313165404718590227 := by
  unfold tailWord_6846130
  simp only [CollatzResearch.WordTrace]
  refine ⟨62424718671911927690569961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166465916458431807174853229 62424718671911927690569961)
  ·
    refine ⟨46818539003933945767927471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62424718671911927690569961 46818539003933945767927471)
    ·
      refine ⟨70227808505900918651891207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46818539003933945767927471 70227808505900918651891207)
      ·
        refine ⟨105341712758851377977836811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70227808505900918651891207 105341712758851377977836811)
        ·
          refine ⟨158012569138277066966755217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105341712758851377977836811 158012569138277066966755217)
          ·
            refine ⟨118509426853707800225066413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158012569138277066966755217 118509426853707800225066413)
            ·
              refine ⟨44441035070140425084399905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118509426853707800225066413 44441035070140425084399905)
              ·
                refine ⟨33330776302605318813299929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44441035070140425084399905 33330776302605318813299929)
                ·
                  refine ⟨24998082226953989109974947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33330776302605318813299929 24998082226953989109974947)
                  ·
                    refine ⟨37497123340430983664962421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24998082226953989109974947 37497123340430983664962421)
                    ·
                      refine ⟨3515355313165404718590227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37497123340430983664962421 3515355313165404718590227)
                      ·
                        rfl

theorem cell23_6846130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_6846130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846130 prefixEnd_6846130 := by exact prefixLift 6846130
  have htrace : WordTrace (prefixWord ++ tailWord_6846130) baseStart_6846130 baseEnd_6846130 := by
    simpa [prefixWord, tailWord_6846130, baseEnd_6846130] using wordTrace_append hprefix tailTrace_6846130
  have hstable : (prefixWord ++ tailWord_6846130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846130).length < 2 ^ (prefixWord ++ tailWord_6846130).sum := by decide
  have hdescent : baseEnd_6846130 < baseStart_6846130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846161 : List Nat := [1, 2, 2, 1, 2, 5, 2, 2, 2, 2, 2]
def baseStart_6846161 : Nat := 118140960795 + 6846161 * 2 ^ 59
def prefixEnd_6846161 : Nat := 4983230072969 + 3 ^ 40 * 6846161 * 2
def baseEnd_6846161 : Nat := 3515371231065694097302585

theorem tailTrace_6846161 : CollatzResearch.WordTrace tailWord_6846161 prefixEnd_6846161 3515371231065694097302585 := by
  unfold tailWord_6846161
  simp only [CollatzResearch.WordTrace]
  refine ⟨249700005350535403056658337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166466670233690268704438891 249700005350535403056658337)
  ·
    refine ⟨187275004012901552292493753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249700005350535403056658337 187275004012901552292493753)
    ·
      refine ⟨140456253009676164219370315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187275004012901552292493753 140456253009676164219370315)
      ·
        refine ⟨210684379514514246329055473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140456253009676164219370315 210684379514514246329055473)
        ·
          refine ⟨158013284635885684746791605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210684379514514246329055473 158013284635885684746791605)
          ·
            refine ⟨14813745434614282945011713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158013284635885684746791605 14813745434614282945011713)
            ·
              refine ⟨11110309075960712208758785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14813745434614282945011713 11110309075960712208758785)
              ·
                refine ⟨8332731806970534156569089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110309075960712208758785 8332731806970534156569089)
                ·
                  refine ⟨6249548855227900617426817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8332731806970534156569089 6249548855227900617426817)
                  ·
                    refine ⟨4687161641420925463070113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6249548855227900617426817 4687161641420925463070113)
                    ·
                      refine ⟨3515371231065694097302585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687161641420925463070113 3515371231065694097302585)
                      ·
                        rfl

theorem cell23_6846161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_6846161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846161 prefixEnd_6846161 := by exact prefixLift 6846161
  have htrace : WordTrace (prefixWord ++ tailWord_6846161) baseStart_6846161 baseEnd_6846161 := by
    simpa [prefixWord, tailWord_6846161, baseEnd_6846161] using wordTrace_append hprefix tailTrace_6846161
  have hstable : (prefixWord ++ tailWord_6846161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846161).length < 2 ^ (prefixWord ++ tailWord_6846161).sum := by decide
  have hdescent : baseEnd_6846161 < baseStart_6846161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846167 : List Nat := [1, 1, 3, 2, 1, 3, 3, 4, 5]
def baseStart_6846167 : Nat := 118140960795 + 6846167 * 2 ^ 59
def prefixEnd_6846167 : Nat := 4983230072969 + 3 ^ 40 * 6846167 * 2
def baseEnd_6846167 : Nat := 390597145772180119314173

theorem tailTrace_6846167 : CollatzResearch.WordTrace tailWord_6846167 prefixEnd_6846167 390597145772180119314173 := by
  unfold tailWord_6846167
  simp only [CollatzResearch.WordTrace]
  refine ⟨249700224188513666081376755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166466816125675777387584503 249700224188513666081376755)
  ·
    refine ⟨374550336282770499122065133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249700224188513666081376755 374550336282770499122065133)
    ·
      refine ⟨140456376106038937170774425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374550336282770499122065133 140456376106038937170774425)
      ·
        refine ⟨105342282079529202878080819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140456376106038937170774425 105342282079529202878080819)
        ·
          refine ⟨158013423119293804317121229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105342282079529202878080819 158013423119293804317121229)
          ·
            refine ⟨59255033669735176618920461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158013423119293804317121229 59255033669735176618920461)
            ·
              refine ⟨22220637626150691232095173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59255033669735176618920461 22220637626150691232095173)
              ·
                refine ⟨4166369554903254606017845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22220637626150691232095173 4166369554903254606017845)
                ·
                  refine ⟨390597145772180119314173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4166369554903254606017845 390597145772180119314173)
                  ·
                    rfl

theorem cell23_6846167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 4, 5].length) (baseStart_6846167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846167 prefixEnd_6846167 := by exact prefixLift 6846167
  have htrace : WordTrace (prefixWord ++ tailWord_6846167) baseStart_6846167 baseEnd_6846167 := by
    simpa [prefixWord, tailWord_6846167, baseEnd_6846167] using wordTrace_append hprefix tailTrace_6846167
  have hstable : (prefixWord ++ tailWord_6846167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846167).length < 2 ^ (prefixWord ++ tailWord_6846167).sum := by decide
  have hdescent : baseEnd_6846167 < baseStart_6846167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846180 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_6846180 : Nat := 118140960795 + 6846180 * 2 ^ 59
def prefixEnd_6846180 : Nat := 4983230072969 + 3 ^ 40 * 6846180 * 2
def baseEnd_6846180 : Nat := 1171793662399376507654999

theorem tailTrace_6846180 : CollatzResearch.WordTrace tailWord_6846180 prefixEnd_6846180 1171793662399376507654999 := by
  unfold tailWord_6846180
  simp only [CollatzResearch.WordTrace]
  refine ⟨124850349168733284650799997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166467132224977712867733329 124850349168733284650799997)
  ·
    refine ⟨46818880938274981744049999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124850349168733284650799997 46818880938274981744049999)
    ·
      refine ⟨70228321407412472616074999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46818880938274981744049999 70228321407412472616074999)
      ·
        refine ⟨105342482111118708924112499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70228321407412472616074999 105342482111118708924112499)
        ·
          refine ⟨158013723166678063386168749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105342482111118708924112499 158013723166678063386168749)
          ·
            refine ⟨59255146187504273769813281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158013723166678063386168749 59255146187504273769813281)
            ·
              refine ⟨44441359640628205327359961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59255146187504273769813281 44441359640628205327359961)
              ·
                refine ⟨33331019730471153995519971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44441359640628205327359961 33331019730471153995519971)
                ·
                  refine ⟨49996529595706730993279957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33331019730471153995519971 49996529595706730993279957)
                  ·
                    refine ⟨1171793662399376507654999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49996529595706730993279957 1171793662399376507654999)
                    ·
                      rfl

theorem cell23_6846180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_6846180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846180 prefixEnd_6846180 := by exact prefixLift 6846180
  have htrace : WordTrace (prefixWord ++ tailWord_6846180) baseStart_6846180 baseEnd_6846180 := by
    simpa [prefixWord, tailWord_6846180, baseEnd_6846180] using wordTrace_append hprefix tailTrace_6846180
  have hstable : (prefixWord ++ tailWord_6846180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846180).length < 2 ^ (prefixWord ++ tailWord_6846180).sum := by decide
  have hdescent : baseEnd_6846180 < baseStart_6846180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846220 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_6846220 : Nat := 118140960795 + 6846220 * 2 ^ 59
def prefixEnd_6846220 : Nat := 4983230072969 + 3 ^ 40 * 6846220 * 2
def baseEnd_6846220 : Nat := 3515401526424309366464813

theorem tailTrace_6846220 : CollatzResearch.WordTrace tailWord_6846220 prefixEnd_6846220 3515401526424309366464813 := by
  unfold tailWord_6846220
  simp only [CollatzResearch.WordTrace]
  refine ⟨124851078628660828066528057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166468104838214437422037409 124851078628660828066528057)
  ·
    refine ⟨93638308971495621049896043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124851078628660828066528057 93638308971495621049896043)
    ·
      refine ⟨140457463457243431574844065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93638308971495621049896043 140457463457243431574844065)
      ·
        refine ⟨105343097592932573681133049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140457463457243431574844065 105343097592932573681133049)
        ·
          refine ⟨79007323194699430260849787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105343097592932573681133049 79007323194699430260849787)
          ·
            refine ⟨118510984792049145391274681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79007323194699430260849787 118510984792049145391274681)
            ·
              refine ⟨88883238594036859043456011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118510984792049145391274681 88883238594036859043456011)
              ·
                refine ⟨133324857891055288565184017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88883238594036859043456011 133324857891055288565184017)
                ·
                  refine ⟨99993643418291466423888013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133324857891055288565184017 99993643418291466423888013)
                  ·
                    refine ⟨37497616281859299908958005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99993643418291466423888013 37497616281859299908958005)
                    ·
                      refine ⟨3515401526424309366464813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37497616281859299908958005 3515401526424309366464813)
                      ·
                        rfl

theorem cell23_6846220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_6846220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846220 prefixEnd_6846220 := by exact prefixLift 6846220
  have htrace : WordTrace (prefixWord ++ tailWord_6846220) baseStart_6846220 baseEnd_6846220 := by
    simpa [prefixWord, tailWord_6846220, baseEnd_6846220] using wordTrace_append hprefix tailTrace_6846220
  have hstable : (prefixWord ++ tailWord_6846220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846220).length < 2 ^ (prefixWord ++ tailWord_6846220).sum := by decide
  have hdescent : baseEnd_6846220 < baseStart_6846220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846234 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2]
def baseStart_6846234 : Nat := 118140960795 + 6846234 * 2 ^ 59
def prefixEnd_6846234 : Nat := 4983230072969 + 3 ^ 40 * 6846234 * 2
def baseEnd_6846234 : Nat := 3515408715153472311689749

theorem tailTrace_6846234 : CollatzResearch.WordTrace tailWord_6846234 prefixEnd_6846234 3515408715153472311689749 := by
  unfold tailWord_6846234
  simp only [CollatzResearch.WordTrace]
  refine ⟨62425666969817734131016439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166468445252847291016043837 62425666969817734131016439)
  ·
    refine ⟨93638500454726601196524659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62425666969817734131016439 93638500454726601196524659)
    ·
      refine ⟨140457750682089901794786989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93638500454726601196524659 140457750682089901794786989)
      ·
        refine ⟨52671656505783713173045121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140457750682089901794786989 52671656505783713173045121)
        ·
          refine ⟨39503742379337784879783841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52671656505783713173045121 39503742379337784879783841)
          ·
            refine ⟨29627806784503338659837881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39503742379337784879783841 29627806784503338659837881)
            ·
              refine ⟨22220855088377503994878411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29627806784503338659837881 22220855088377503994878411)
              ·
                refine ⟨33331282632566255992317617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22220855088377503994878411 33331282632566255992317617)
                ·
                  refine ⟨24998461974424691994238213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33331282632566255992317617 24998461974424691994238213)
                  ·
                    refine ⟨4687211620204629748919665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24998461974424691994238213 4687211620204629748919665)
                    ·
                      refine ⟨3515408715153472311689749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687211620204629748919665 3515408715153472311689749)
                      ·
                        rfl

theorem cell23_6846234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_6846234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846234 prefixEnd_6846234 := by exact prefixLift 6846234
  have htrace : WordTrace (prefixWord ++ tailWord_6846234) baseStart_6846234 baseEnd_6846234 := by
    simpa [prefixWord, tailWord_6846234, baseEnd_6846234] using wordTrace_append hprefix tailTrace_6846234
  have hstable : (prefixWord ++ tailWord_6846234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846234).length < 2 ^ (prefixWord ++ tailWord_6846234).sum := by decide
  have hdescent : baseEnd_6846234 < baseStart_6846234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846244 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_6846244 : Nat := 118140960795 + 6846244 * 2 ^ 59
def prefixEnd_6846244 : Nat := 4983230072969 + 3 ^ 40 * 6846244 * 2
def baseEnd_6846244 : Nat := 1171804616653339090854901

theorem tailTrace_6846244 : CollatzResearch.WordTrace tailWord_6846244 prefixEnd_6846244 1171804616653339090854901 := by
  unfold tailWord_6846244
  simp only [CollatzResearch.WordTrace]
  refine ⟨124851516304617354115964893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166468688406156472154619857 124851516304617354115964893)
  ·
    refine ⟨46819318614231507793486835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124851516304617354115964893 46819318614231507793486835)
    ·
      refine ⟨70228977921347261690230253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46819318614231507793486835 70228977921347261690230253)
      ·
        refine ⟨26335866720505223133836345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70228977921347261690230253 26335866720505223133836345)
        ·
          refine ⟨19751900040378917350377259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26335866720505223133836345 19751900040378917350377259)
          ·
            refine ⟨29627850060568376025565889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19751900040378917350377259 29627850060568376025565889)
            ·
              refine ⟨22220887545426282019174417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29627850060568376025565889 22220887545426282019174417)
              ·
                refine ⟨16665665659069711514380813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22220887545426282019174417 16665665659069711514380813)
                ·
                  refine ⟨6249624622151141817892805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16665665659069711514380813 6249624622151141817892805)
                  ·
                    refine ⟨1171804616653339090854901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6249624622151141817892805 1171804616653339090854901)
                    ·
                      rfl

theorem cell23_6846244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_6846244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846244 prefixEnd_6846244 := by exact prefixLift 6846244
  have htrace : WordTrace (prefixWord ++ tailWord_6846244) baseStart_6846244 baseEnd_6846244 := by
    simpa [prefixWord, tailWord_6846244, baseEnd_6846244] using wordTrace_append hprefix tailTrace_6846244
  have hstable : (prefixWord ++ tailWord_6846244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846244).length < 2 ^ (prefixWord ++ tailWord_6846244).sum := by decide
  have hdescent : baseEnd_6846244 < baseStart_6846244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846278 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_6846278 : Nat := 118140960795 + 6846278 * 2 ^ 59
def prefixEnd_6846278 : Nat := 4983230072969 + 3 ^ 40 * 6846278 * 2
def baseEnd_6846278 : Nat := 1171810436100756713179849

theorem tailTrace_6846278 : CollatzResearch.WordTrace tailWord_6846278 prefixEnd_6846278 1171810436100756713179849 := by
  unfold tailWord_6846278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803258521597235376208359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166469515127407688025778325 7803258521597235376208359)
  ·
    refine ⟨11704887782395853064312539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7803258521597235376208359 11704887782395853064312539)
    ·
      refine ⟨17557331673593779596468809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11704887782395853064312539 17557331673593779596468809)
      ·
        refine ⟨13167998755195334697351607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17557331673593779596468809 13167998755195334697351607)
        ·
          refine ⟨19751998132793002046027411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13167998755195334697351607 19751998132793002046027411)
          ·
            refine ⟨29627997199189503069041117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19751998132793002046027411 29627997199189503069041117)
            ·
              refine ⟨11110498949696063650890419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29627997199189503069041117 11110498949696063650890419)
              ·
                refine ⟨16665748424544095476335629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11110498949696063650890419 16665748424544095476335629)
                ·
                  refine ⟨6249655659204035803625861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16665748424544095476335629 6249655659204035803625861)
                  ·
                    refine ⟨1171810436100756713179849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6249655659204035803625861 1171810436100756713179849)
                    ·
                      rfl

theorem cell23_6846278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_6846278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846278 prefixEnd_6846278 := by exact prefixLift 6846278
  have htrace : WordTrace (prefixWord ++ tailWord_6846278) baseStart_6846278 baseEnd_6846278 := by
    simpa [prefixWord, tailWord_6846278, baseEnd_6846278] using wordTrace_append hprefix tailTrace_6846278
  have hstable : (prefixWord ++ tailWord_6846278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846278).length < 2 ^ (prefixWord ++ tailWord_6846278).sum := by decide
  have hdescent : baseEnd_6846278 < baseStart_6846278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846304 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 1, 5]
def baseStart_6846304 : Nat := 118140960795 + 6846304 * 2 ^ 59
def prefixEnd_6846304 : Nat := 4983230072969 + 3 ^ 40 * 6846304 * 2
def baseEnd_6846304 : Nat := 1171814886266429012604809

theorem tailTrace_6846304 : CollatzResearch.WordTrace tailWord_6846304 prefixEnd_6846304 1171814886266429012604809 := by
  unfold tailWord_6846304
  simp only [CollatzResearch.WordTrace]
  refine ⟨124852610494508669239556983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166470147326011558986075977 124852610494508669239556983)
  ·
    refine ⟨187278915741763003859335475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124852610494508669239556983 187278915741763003859335475)
    ·
      refine ⟨280918373612644505789003213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187278915741763003859335475 280918373612644505789003213)
      ·
        refine ⟨105344390104741689670876205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280918373612644505789003213 105344390104741689670876205)
        ·
          refine ⟨39504146289278133626578577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105344390104741689670876205 39504146289278133626578577)
          ·
            refine ⟨29628109716958600219933933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39504146289278133626578577 29628109716958600219933933)
            ·
              refine ⟨11110541143859475082475225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29628109716958600219933933 11110541143859475082475225)
              ·
                refine ⟨8332905857894606311856419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110541143859475082475225 8332905857894606311856419)
                ·
                  refine ⟨12499358786841909467784629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8332905857894606311856419 12499358786841909467784629)
                  ·
                    refine ⟨1171814886266429012604809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12499358786841909467784629 1171814886266429012604809)
                    ·
                      rfl

theorem cell23_6846304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_6846304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846304 prefixEnd_6846304 := by exact prefixLift 6846304
  have htrace : WordTrace (prefixWord ++ tailWord_6846304) baseStart_6846304 baseEnd_6846304 := by
    simpa [prefixWord, tailWord_6846304, baseEnd_6846304] using wordTrace_append hprefix tailTrace_6846304
  have hstable : (prefixWord ++ tailWord_6846304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846304).length < 2 ^ (prefixWord ++ tailWord_6846304).sum := by decide
  have hdescent : baseEnd_6846304 < baseStart_6846304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846311 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_6846311 : Nat := 118140960795 + 6846311 * 2 ^ 59
def prefixEnd_6846311 : Nat := 4983230072969 + 3 ^ 40 * 6846311 * 2
def baseEnd_6846311 : Nat := 3515448253163868510426895

theorem tailTrace_6846311 : CollatzResearch.WordTrace tailWord_6846311 prefixEnd_6846311 3515448253163868510426895 := by
  unfold tailWord_6846311
  simp only [CollatzResearch.WordTrace]
  refine ⟨249705476299991978674618787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166470317533327985783079191 249705476299991978674618787)
  ·
    refine ⟨374558214449987968011928181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249705476299991978674618787 374558214449987968011928181)
    ·
      refine ⟨35114832604686372001118267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 374558214449987968011928181 35114832604686372001118267)
      ·
        refine ⟨52672248907029558001677401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35114832604686372001118267 52672248907029558001677401)
        ·
          refine ⟨39504186680272168501258051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52672248907029558001677401 39504186680272168501258051)
          ·
            refine ⟨59256280020408252751887077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39504186680272168501258051 59256280020408252751887077)
            ·
              refine ⟨11110552503826547390978827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59256280020408252751887077 11110552503826547390978827)
              ·
                refine ⟨16665828755739821086468241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11110552503826547390978827 16665828755739821086468241)
                ·
                  refine ⟨12499371566804865814851181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16665828755739821086468241 12499371566804865814851181)
                  ·
                    refine ⟨4687264337551824680569193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12499371566804865814851181 4687264337551824680569193)
                    ·
                      refine ⟨3515448253163868510426895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687264337551824680569193 3515448253163868510426895)
                      ·
                        rfl

theorem cell23_6846311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_6846311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846311 prefixEnd_6846311 := by exact prefixLift 6846311
  have htrace : WordTrace (prefixWord ++ tailWord_6846311) baseStart_6846311 baseEnd_6846311 := by
    simpa [prefixWord, tailWord_6846311, baseEnd_6846311] using wordTrace_append hprefix tailTrace_6846311
  have hstable : (prefixWord ++ tailWord_6846311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846311).length < 2 ^ (prefixWord ++ tailWord_6846311).sum := by decide
  have hdescent : baseEnd_6846311 < baseStart_6846311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846317 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_6846317 : Nat := 118140960795 + 6846317 * 2 ^ 59
def prefixEnd_6846317 : Nat := 4983230072969 + 3 ^ 40 * 6846317 * 2
def baseEnd_6846317 : Nat := 1171817111349265162317289

theorem tailTrace_6846317 : CollatzResearch.WordTrace tailWord_6846317 prefixEnd_6846317 1171817111349265162317289 := by
  unfold tailWord_6846317
  simp only [CollatzResearch.WordTrace]
  refine ⟨249705695137970241699337205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166470463425313494466224803 249705695137970241699337205)
  ·
    refine ⟨23409908919184710159312863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249705695137970241699337205 23409908919184710159312863)
    ·
      refine ⟨35114863378777065238969295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23409908919184710159312863 35114863378777065238969295)
      ·
        refine ⟨52672295068165597858453943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35114863378777065238969295 52672295068165597858453943)
        ·
          refine ⟨79008442602248396787680915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52672295068165597858453943 79008442602248396787680915)
          ·
            refine ⟨118512663903372595181521373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79008442602248396787680915 118512663903372595181521373)
            ·
              refine ⟨44442248963764723193070515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118512663903372595181521373 44442248963764723193070515)
              ·
                refine ⟨66663373445647084789605773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44442248963764723193070515 66663373445647084789605773)
                ·
                  refine ⟨24998765042117656796102165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66663373445647084789605773 24998765042117656796102165)
                  ·
                    refine ⟨1171817111349265162317289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24998765042117656796102165 1171817111349265162317289)
                    ·
                      rfl

theorem cell23_6846317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_6846317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846317 prefixEnd_6846317 := by exact prefixLift 6846317
  have htrace : WordTrace (prefixWord ++ tailWord_6846317) baseStart_6846317 baseEnd_6846317 := by
    simpa [prefixWord, tailWord_6846317, baseEnd_6846317] using wordTrace_append hprefix tailTrace_6846317
  have hstable : (prefixWord ++ tailWord_6846317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846317).length < 2 ^ (prefixWord ++ tailWord_6846317).sum := by decide
  have hdescent : baseEnd_6846317 < baseStart_6846317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846341 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 3, 2, 2]
def baseStart_6846341 : Nat := 118140960795 + 6846341 * 2 ^ 59
def prefixEnd_6846341 : Nat := 4983230072969 + 3 ^ 40 * 6846341 * 2
def baseEnd_6846341 : Nat := 3515463657583503393051757

theorem tailTrace_6846341 : CollatzResearch.WordTrace tailWord_6846341 prefixEnd_6846341 3515463657583503393051757 := by
  unfold tailWord_6846341
  simp only [CollatzResearch.WordTrace]
  refine ⟨249706570489883293798210877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166471046993255529198807251 249706570489883293798210877)
  ·
    refine ⟨93639963933706235174329079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249706570489883293798210877 93639963933706235174329079)
    ·
      refine ⟨140459945900559352761493619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93639963933706235174329079 140459945900559352761493619)
      ·
        refine ⟨210689918850839029142240429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140459945900559352761493619 210689918850839029142240429)
        ·
          refine ⟨79008719569064635928340161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210689918850839029142240429 79008719569064635928340161)
          ·
            refine ⟨59256539676798476946255121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79008719569064635928340161 59256539676798476946255121)
            ·
              refine ⟨44442404757598857709691341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59256539676798476946255121 44442404757598857709691341)
              ·
                refine ⟨16665901784099571641134253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44442404757598857709691341 16665901784099571641134253)
                ·
                  refine ⟨6249713169037339365425345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16665901784099571641134253 6249713169037339365425345)
                  ·
                    refine ⟨4687284876778004524069009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6249713169037339365425345 4687284876778004524069009)
                    ·
                      refine ⟨3515463657583503393051757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687284876778004524069009 3515463657583503393051757)
                      ·
                        rfl

theorem cell23_6846341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_6846341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846341 prefixEnd_6846341 := by exact prefixLift 6846341
  have htrace : WordTrace (prefixWord ++ tailWord_6846341) baseStart_6846341 baseEnd_6846341 := by
    simpa [prefixWord, tailWord_6846341, baseEnd_6846341] using wordTrace_append hprefix tailTrace_6846341
  have hstable : (prefixWord ++ tailWord_6846341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846341).length < 2 ^ (prefixWord ++ tailWord_6846341).sum := by decide
  have hdescent : baseEnd_6846341 < baseStart_6846341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846375 : List Nat := [1, 1, 6, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_6846375 : Nat := 118140960795 + 6846375 * 2 ^ 59
def prefixEnd_6846375 : Nat := 4983230072969 + 3 ^ 40 * 6846375 * 2
def baseEnd_6846375 : Nat := 3515481115925756260026601

theorem tailTrace_6846375 : CollatzResearch.WordTrace tailWord_6846375 prefixEnd_6846375 3515481115925756260026601 := by
  unfold tailWord_6846375
  simp only [CollatzResearch.WordTrace]
  refine ⟨249707810571760117604948579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166471873714506745069965719 249707810571760117604948579)
  ·
    refine ⟨374561715857640176407422869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249707810571760117604948579 374561715857640176407422869)
    ·
      refine ⟨17557580430826883269097947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 374561715857640176407422869 17557580430826883269097947)
      ·
        refine ⟨26336370646240324903646921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17557580430826883269097947 26336370646240324903646921)
        ·
          refine ⟨19752277984680243677735191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26336370646240324903646921 19752277984680243677735191)
          ·
            refine ⟨29628416977020365516602787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19752277984680243677735191 29628416977020365516602787)
            ·
              refine ⟨44442625465530548274904181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29628416977020365516602787 44442625465530548274904181)
              ·
                refine ⟨4166496137393488900772267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44442625465530548274904181 4166496137393488900772267)
                ·
                  refine ⟨6249744206090233351158401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166496137393488900772267 6249744206090233351158401)
                  ·
                    refine ⟨4687308154567675013368801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6249744206090233351158401 4687308154567675013368801)
                    ·
                      refine ⟨3515481115925756260026601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687308154567675013368801 3515481115925756260026601)
                      ·
                        rfl

theorem cell23_6846375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_6846375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846375 prefixEnd_6846375 := by exact prefixLift 6846375
  have htrace : WordTrace (prefixWord ++ tailWord_6846375) baseStart_6846375 baseEnd_6846375 := by
    simpa [prefixWord, tailWord_6846375, baseEnd_6846375] using wordTrace_append hprefix tailTrace_6846375
  have hstable : (prefixWord ++ tailWord_6846375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846375).length < 2 ^ (prefixWord ++ tailWord_6846375).sum := by decide
  have hdescent : baseEnd_6846375 < baseStart_6846375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846447 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_6846447 : Nat := 118140960795 + 6846447 * 2 ^ 59
def prefixEnd_6846447 : Nat := 4983230072969 + 3 ^ 40 * 6846447 * 2
def baseEnd_6846447 : Nat := 3515518086532879978326269

theorem tailTrace_6846447 : CollatzResearch.WordTrace tailWord_6846447 prefixEnd_6846447 3515518086532879978326269 := by
  unfold tailWord_6846447
  simp only [CollatzResearch.WordTrace]
  refine ⟨249710436627499273901569595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166473624418332849267713063 249710436627499273901569595)
  ·
    refine ⟨374565654941248910852354393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249710436627499273901569595 374565654941248910852354393)
    ·
      refine ⟨280924241205936683139265795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374565654941248910852354393 280924241205936683139265795)
      ·
        refine ⟨421386361808905024708898693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280924241205936683139265795 421386361808905024708898693)
        ·
          refine ⟨79009942839169692132918505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 421386361808905024708898693 79009942839169692132918505)
          ·
            refine ⟨59257457129377269099688879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79009942839169692132918505 59257457129377269099688879)
            ·
              refine ⟨88886185694065903649533319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59257457129377269099688879 88886185694065903649533319)
              ·
                refine ⟨133329278541098855474299979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88886185694065903649533319 133329278541098855474299979)
                ·
                  refine ⟨199993917811648283211449969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133329278541098855474299979 199993917811648283211449969)
                  ·
                    refine ⟨149995438358736212408587477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199993917811648283211449969 149995438358736212408587477)
                    ·
                      refine ⟨3515518086532879978326269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149995438358736212408587477 3515518086532879978326269)
                      ·
                        rfl

theorem cell23_6846447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_6846447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846447 prefixEnd_6846447 := by exact prefixLift 6846447
  have htrace : WordTrace (prefixWord ++ tailWord_6846447) baseStart_6846447 baseEnd_6846447 := by
    simpa [prefixWord, tailWord_6846447, baseEnd_6846447] using wordTrace_append hprefix tailTrace_6846447
  have hstable : (prefixWord ++ tailWord_6846447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846447).length < 2 ^ (prefixWord ++ tailWord_6846447).sum := by decide
  have hdescent : baseEnd_6846447 < baseStart_6846447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846467 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 3, 7]
def baseStart_6846467 : Nat := 118140960795 + 6846467 * 2 ^ 59
def prefixEnd_6846467 : Nat := 4983230072969 + 3 ^ 40 * 6846467 * 2
def baseEnd_6846467 : Nat := 1171842785381989966692059

theorem tailTrace_6846467 : CollatzResearch.WordTrace tailWord_6846467 prefixEnd_6846467 1171842785381989966692059 := by
  unfold tailWord_6846467
  simp only [CollatzResearch.WordTrace]
  refine ⟨249711166087426817317297655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166474110724951211544865103 249711166087426817317297655)
  ·
    refine ⟨374566749131140225975946483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249711166087426817317297655 374566749131140225975946483)
    ·
      refine ⟨561850123696710338963919725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374566749131140225975946483 561850123696710338963919725)
      ·
        refine ⟨210693796386266377111469897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 561850123696710338963919725 210693796386266377111469897)
        ·
          refine ⟨158020347289699782833602423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210693796386266377111469897 158020347289699782833602423)
          ·
            refine ⟨237030520934549674250403635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158020347289699782833602423 237030520934549674250403635)
            ·
              refine ⟨355545781401824511375605453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237030520934549674250403635 355545781401824511375605453)
              ·
                refine ⟨133329668025684191765852045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355545781401824511375605453 133329668025684191765852045)
                ·
                  refine ⟨49998625509631571912194517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133329668025684191765852045 49998625509631571912194517)
                  ·
                    refine ⟨1171842785381989966692059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49998625509631571912194517 1171842785381989966692059)
                    ·
                      rfl

theorem cell23_6846467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 7].length) (baseStart_6846467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846467 prefixEnd_6846467 := by exact prefixLift 6846467
  have htrace : WordTrace (prefixWord ++ tailWord_6846467) baseStart_6846467 baseEnd_6846467 := by
    simpa [prefixWord, tailWord_6846467, baseEnd_6846467] using wordTrace_append hprefix tailTrace_6846467
  have hstable : (prefixWord ++ tailWord_6846467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846467).length < 2 ^ (prefixWord ++ tailWord_6846467).sum := by decide
  have hdescent : baseEnd_6846467 < baseStart_6846467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846564 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_6846564 : Nat := 118140960795 + 6846564 * 2 ^ 59
def prefixEnd_6846564 : Nat := 4983230072969 + 3 ^ 40 * 6846564 * 2
def baseEnd_6846564 : Nat := 3515578163769456020563231

theorem tailTrace_6846564 : CollatzResearch.WordTrace tailWord_6846564 prefixEnd_6846564 3515578163769456020563231 := by
  unfold tailWord_6846564
  simp only [CollatzResearch.WordTrace]
  refine ⟨124857351984037701441789373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166476469312050268589052497 124857351984037701441789373)
  ·
    refine ⟨46821506994014138040671015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124857351984037701441789373 46821506994014138040671015)
    ·
      refine ⟨70232260491021207061006523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46821506994014138040671015 70232260491021207061006523)
      ·
        refine ⟨105348390736531810591509785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70232260491021207061006523 105348390736531810591509785)
        ·
          refine ⟨79011293052398857943632339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105348390736531810591509785 79011293052398857943632339)
          ·
            refine ⟨118516939578598286915448509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79011293052398857943632339 118516939578598286915448509)
            ·
              refine ⟨44443852341974357593293191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118516939578598286915448509 44443852341974357593293191)
              ·
                refine ⟨66665778512961536389939787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44443852341974357593293191 66665778512961536389939787)
                ·
                  refine ⟨99998667769442304584909681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66665778512961536389939787 99998667769442304584909681)
                  ·
                    refine ⟨74999000827081728438682261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99998667769442304584909681 74999000827081728438682261)
                    ·
                      refine ⟨3515578163769456020563231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74999000827081728438682261 3515578163769456020563231)
                      ·
                        rfl

theorem cell23_6846564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_6846564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846564 prefixEnd_6846564 := by exact prefixLift 6846564
  have htrace : WordTrace (prefixWord ++ tailWord_6846564) baseStart_6846564 baseEnd_6846564 := by
    simpa [prefixWord, tailWord_6846564, baseEnd_6846564] using wordTrace_append hprefix tailTrace_6846564
  have hstable : (prefixWord ++ tailWord_6846564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846564).length < 2 ^ (prefixWord ++ tailWord_6846564).sum := by decide
  have hdescent : baseEnd_6846564 < baseStart_6846564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846578 : List Nat := [3, 2, 1, 2, 2, 3, 3, 1, 6]
def baseStart_6846578 : Nat := 118140960795 + 6846578 * 2 ^ 59
def prefixEnd_6846578 : Nat := 4983230072969 + 3 ^ 40 * 6846578 * 2
def baseEnd_6846578 : Nat := 390620594722068773976463

theorem tailTrace_6846578 : CollatzResearch.WordTrace tailWord_6846578 prefixEnd_6846578 390620594722068773976463 := by
  unfold tailWord_6846578
  simp only [CollatzResearch.WordTrace]
  refine ⟨62428803647506170818647097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166476809726683122183058925 62428803647506170818647097)
  ·
    refine ⟨46821602735629628113985323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62428803647506170818647097 46821602735629628113985323)
    ·
      refine ⟨70232404103444442170977985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46821602735629628113985323 70232404103444442170977985)
      ·
        refine ⟨52674303077583331628233489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70232404103444442170977985 52674303077583331628233489)
        ·
          refine ⟨39505727308187498721175117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52674303077583331628233489 39505727308187498721175117)
          ·
            refine ⟨14814647740570312020440669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39505727308187498721175117 14814647740570312020440669)
            ·
              refine ⟨5555492902713867007665251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14814647740570312020440669 5555492902713867007665251)
              ·
                refine ⟨8333239354070800511497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555492902713867007665251 8333239354070800511497877)
                ·
                  refine ⟨390620594722068773976463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8333239354070800511497877 390620594722068773976463)
                  ·
                    rfl

theorem cell23_6846578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_6846578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846578 prefixEnd_6846578 := by exact prefixLift 6846578
  have htrace : WordTrace (prefixWord ++ tailWord_6846578) baseStart_6846578 baseEnd_6846578 := by
    simpa [prefixWord, tailWord_6846578, baseEnd_6846578] using wordTrace_append hprefix tailTrace_6846578
  have hstable : (prefixWord ++ tailWord_6846578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846578).length < 2 ^ (prefixWord ++ tailWord_6846578).sum := by decide
  have hdescent : baseEnd_6846578 < baseStart_6846578 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846588 : List Nat := [2, 2, 2, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_6846588 : Nat := 118140960795 + 6846588 * 2 ^ 59
def prefixEnd_6846588 : Nat := 4983230072969 + 3 ^ 40 * 6846588 * 2
def baseEnd_6846588 : Nat := 3515590487305163926663121

theorem tailTrace_6846588 : CollatzResearch.WordTrace tailWord_6846588 prefixEnd_6846588 3515590487305163926663121 := by
  unfold tailWord_6846588
  simp only [CollatzResearch.WordTrace]
  refine ⟨124857789659994227491226209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166477052879992303321634945 124857789659994227491226209)
  ·
    refine ⟨93643342244995670618419657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124857789659994227491226209 93643342244995670618419657)
    ·
      refine ⟨70232506683746752963814743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93643342244995670618419657 70232506683746752963814743)
      ·
        refine ⟨105348760025620129445722115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70232506683746752963814743 105348760025620129445722115)
        ·
          refine ⟨158023140038430194168583173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105348760025620129445722115 158023140038430194168583173)
          ·
            refine ⟨29629338757205661406609345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158023140038430194168583173 29629338757205661406609345)
            ·
              refine ⟨22222004067904246054957009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29629338757205661406609345 22222004067904246054957009)
              ·
                refine ⟨16666503050928184541217757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22222004067904246054957009 16666503050928184541217757)
                ·
                  refine ⟨6249938644098069202956659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16666503050928184541217757 6249938644098069202956659)
                  ·
                    refine ⟨9374907966147103804434989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6249938644098069202956659 9374907966147103804434989)
                    ·
                      refine ⟨3515590487305163926663121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9374907966147103804434989 3515590487305163926663121)
                      ·
                        rfl

theorem cell23_6846588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_6846588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846588 prefixEnd_6846588 := by exact prefixLift 6846588
  have htrace : WordTrace (prefixWord ++ tailWord_6846588) baseStart_6846588 baseEnd_6846588 := by
    simpa [prefixWord, tailWord_6846588, baseEnd_6846588] using wordTrace_append hprefix tailTrace_6846588
  have hstable : (prefixWord ++ tailWord_6846588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846588).length < 2 ^ (prefixWord ++ tailWord_6846588).sum := by decide
  have hdescent : baseEnd_6846588 < baseStart_6846588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846615 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 2, 3, 2]
def baseStart_6846615 : Nat := 118140960795 + 6846615 * 2 ^ 59
def prefixEnd_6846615 : Nat := 4983230072969 + 3 ^ 40 * 6846615 * 2
def baseEnd_6846615 : Nat := 3515604351282835321025497

theorem tailTrace_6846615 : CollatzResearch.WordTrace tailWord_6846615 prefixEnd_6846615 3515604351282835321025497 := by
  unfold tailWord_6846615
  simp only [CollatzResearch.WordTrace]
  refine ⟨249716564090890638593685299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166477709393927092395790199 249716564090890638593685299)
  ·
    refine ⟨374574846136335957890527949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249716564090890638593685299 374574846136335957890527949)
    ·
      refine ⟨140465567301125984208947981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374574846136335957890527949 140465567301125984208947981)
      ·
        refine ⟨52674587737922244078355493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140465567301125984208947981 52674587737922244078355493)
        ·
          refine ⟨9876485200860420764691655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52674587737922244078355493 9876485200860420764691655)
          ·
            refine ⟨14814727801290631147037483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876485200860420764691655 14814727801290631147037483)
            ·
              refine ⟨22222091701935946720556225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14814727801290631147037483 22222091701935946720556225)
              ·
                refine ⟨16666568776451960040417169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22222091701935946720556225 16666568776451960040417169)
                ·
                  refine ⟨12499926582338970030312877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16666568776451960040417169 12499926582338970030312877)
                  ·
                    refine ⟨4687472468377113761367329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12499926582338970030312877 4687472468377113761367329)
                    ·
                      refine ⟨3515604351282835321025497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687472468377113761367329 3515604351282835321025497)
                      ·
                        rfl

theorem cell23_6846615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_6846615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846615 prefixEnd_6846615 := by exact prefixLift 6846615
  have htrace : WordTrace (prefixWord ++ tailWord_6846615) baseStart_6846615 baseEnd_6846615 := by
    simpa [prefixWord, tailWord_6846615, baseEnd_6846615] using wordTrace_append hprefix tailTrace_6846615
  have hstable : (prefixWord ++ tailWord_6846615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846615).length < 2 ^ (prefixWord ++ tailWord_6846615).sum := by decide
  have hdescent : baseEnd_6846615 < baseStart_6846615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846645 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_6846645 : Nat := 118140960795 + 6846645 * 2 ^ 59
def prefixEnd_6846645 : Nat := 4983230072969 + 3 ^ 40 * 6846645 * 2
def baseEnd_6846645 : Nat := 3515619755702470203650359

theorem tailTrace_6846645 : CollatzResearch.WordTrace tailWord_6846645 prefixEnd_6846645 3515619755702470203650359 := by
  unfold tailWord_6846645
  simp only [CollatzResearch.WordTrace]
  refine ⟨249717658280781953717277389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166478438853854635811518259 249717658280781953717277389)
  ·
    refine ⟨93644121855293232643979021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249717658280781953717277389 93644121855293232643979021)
    ·
      refine ⟨35116545695734962241492133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93644121855293232643979021 35116545695734962241492133)
      ·
        refine ⟨6584352317950305420279775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35116545695734962241492133 6584352317950305420279775)
        ·
          refine ⟨9876528476925458130419663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584352317950305420279775 9876528476925458130419663)
          ·
            refine ⟨14814792715388187195629495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9876528476925458130419663 14814792715388187195629495)
            ·
              refine ⟨22222189073082280793444243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14814792715388187195629495 22222189073082280793444243)
              ·
                refine ⟨33333283609623421190166365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22222189073082280793444243 33333283609623421190166365)
                ·
                  refine ⟨12499981353608782946312387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33333283609623421190166365 12499981353608782946312387)
                  ·
                    refine ⟨18749972030413174419468581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12499981353608782946312387 18749972030413174419468581)
                    ·
                      refine ⟨3515619755702470203650359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18749972030413174419468581 3515619755702470203650359)
                      ·
                        rfl

theorem cell23_6846645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_6846645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846645 prefixEnd_6846645 := by exact prefixLift 6846645
  have htrace : WordTrace (prefixWord ++ tailWord_6846645) baseStart_6846645 baseEnd_6846645 := by
    simpa [prefixWord, tailWord_6846645, baseEnd_6846645] using wordTrace_append hprefix tailTrace_6846645
  have hstable : (prefixWord ++ tailWord_6846645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846645).length < 2 ^ (prefixWord ++ tailWord_6846645).sum := by decide
  have hdescent : baseEnd_6846645 < baseStart_6846645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846661 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_6846661 : Nat := 118140960795 + 6846661 * 2 ^ 59
def prefixEnd_6846661 : Nat := 4983230072969 + 3 ^ 40 * 6846661 * 2
def baseEnd_6846661 : Nat := 3515627971392942141050285

theorem tailTrace_6846661 : CollatzResearch.WordTrace tailWord_6846661 prefixEnd_6846661 3515627971392942141050285 := by
  unfold tailWord_6846661
  simp only [CollatzResearch.WordTrace]
  refine ⟨249718241848723988449859837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166478827899149325633239891 249718241848723988449859837)
  ·
    refine ⟨93644340693271495668697439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249718241848723988449859837 93644340693271495668697439)
    ·
      refine ⟨140466511039907243503046159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93644340693271495668697439 140466511039907243503046159)
      ·
        refine ⟨210699766559860865254569239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140466511039907243503046159 210699766559860865254569239)
        ·
          refine ⟨316049649839791297881853859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210699766559860865254569239 316049649839791297881853859)
          ·
            refine ⟨474074474759686946822780789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316049649839791297881853859 474074474759686946822780789)
            ·
              refine ⟨44444482008720651264635699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 474074474759686946822780789 44444482008720651264635699)
              ·
                refine ⟨66666723013080976896953549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44444482008720651264635699 66666723013080976896953549)
                ·
                  refine ⟨25000021129905366336357581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66666723013080976896953549 25000021129905366336357581)
                  ·
                    refine ⟨9375007923714512376134093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25000021129905366336357581 9375007923714512376134093)
                    ·
                      refine ⟨3515627971392942141050285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375007923714512376134093 3515627971392942141050285)
                      ·
                        rfl

theorem cell23_6846661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_6846661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846661 prefixEnd_6846661 := by exact prefixLift 6846661
  have htrace : WordTrace (prefixWord ++ tailWord_6846661) baseStart_6846661 baseEnd_6846661 := by
    simpa [prefixWord, tailWord_6846661, baseEnd_6846661] using wordTrace_append hprefix tailTrace_6846661
  have hstable : (prefixWord ++ tailWord_6846661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846661).length < 2 ^ (prefixWord ++ tailWord_6846661).sum := by decide
  have hdescent : baseEnd_6846661 < baseStart_6846661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846668 : List Nat := [2, 2, 1, 6, 2, 10]
def baseStart_6846668 : Nat := 118140960795 + 6846668 * 2 ^ 59
def prefixEnd_6846668 : Nat := 4983230072969 + 3 ^ 40 * 6846668 * 2
def baseEnd_6846668 : Nat := 14467619612170879068571

theorem tailTrace_6846668 : CollatzResearch.WordTrace tailWord_6846668 prefixEnd_6846668 14467619612170879068571 := by
  unfold tailWord_6846668
  simp only [CollatzResearch.WordTrace]
  refine ⟨124859248579849314322682329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166478998106465752430243105 124859248579849314322682329)
  ·
    refine ⟨93644436434886985742011747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124859248579849314322682329 93644436434886985742011747)
    ·
      refine ⟨140466654652330478613017621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93644436434886985742011747 140466654652330478613017621)
      ·
        refine ⟨6584374436827991184985201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140466654652330478613017621 6584374436827991184985201)
        ·
          refine ⟨4938280827620993388738901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6584374436827991184985201 4938280827620993388738901)
          ·
            refine ⟨14467619612170879068571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4938280827620993388738901 14467619612170879068571)
            ·
              rfl

theorem cell23_6846668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 10].length) (baseStart_6846668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846668 prefixEnd_6846668 := by exact prefixLift 6846668
  have htrace : WordTrace (prefixWord ++ tailWord_6846668) baseStart_6846668 baseEnd_6846668 := by
    simpa [prefixWord, tailWord_6846668, baseEnd_6846668] using wordTrace_append hprefix tailTrace_6846668
  have hstable : (prefixWord ++ tailWord_6846668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846668).length < 2 ^ (prefixWord ++ tailWord_6846668).sum := by decide
  have hdescent : baseEnd_6846668 < baseStart_6846668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846688 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 5, 3, 2]
def baseStart_6846688 : Nat := 118140960795 + 6846688 * 2 ^ 59
def prefixEnd_6846688 : Nat := 4983230072969 + 3 ^ 40 * 6846688 * 2
def baseEnd_6846688 : Nat := 3515641835370613535412661

theorem tailTrace_6846688 : CollatzResearch.WordTrace tailWord_6846688 prefixEnd_6846688 3515641835370613535412661 := by
  unfold tailWord_6846688
  simp only [CollatzResearch.WordTrace]
  refine ⟨124859613309813086030546359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166479484413084114707395145 124859613309813086030546359)
  ·
    refine ⟨187289419964719629045819539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124859613309813086030546359 187289419964719629045819539)
    ·
      refine ⟨280934129947079443568729309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187289419964719629045819539 280934129947079443568729309)
      ·
        refine ⟨105350298730154791338273491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280934129947079443568729309 105350298730154791338273491)
        ·
          refine ⟨158025448095232187007410237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105350298730154791338273491 158025448095232187007410237)
          ·
            refine ⟨59259543035712070127778839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158025448095232187007410237 59259543035712070127778839)
            ·
              refine ⟨88889314553568105191668259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59259543035712070127778839 88889314553568105191668259)
              ·
                refine ⟨133333971830352157787502389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88889314553568105191668259 133333971830352157787502389)
                ·
                  refine ⟨12500059859095514792578349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133333971830352157787502389 12500059859095514792578349)
                  ·
                    refine ⟨4687522447160818047216881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12500059859095514792578349 4687522447160818047216881)
                    ·
                      refine ⟨3515641835370613535412661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687522447160818047216881 3515641835370613535412661)
                      ·
                        rfl

theorem cell23_6846688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_6846688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846688 prefixEnd_6846688 := by exact prefixLift 6846688
  have htrace : WordTrace (prefixWord ++ tailWord_6846688) baseStart_6846688 baseEnd_6846688 := by
    simpa [prefixWord, tailWord_6846688, baseEnd_6846688] using wordTrace_append hprefix tailTrace_6846688
  have hstable : (prefixWord ++ tailWord_6846688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846688).length < 2 ^ (prefixWord ++ tailWord_6846688).sum := by decide
  have hdescent : baseEnd_6846688 < baseStart_6846688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846695 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_6846695 : Nat := 118140960795 + 6846695 * 2 ^ 59
def prefixEnd_6846695 : Nat := 4983230072969 + 3 ^ 40 * 6846695 * 2
def baseEnd_6846695 : Nat := 3515645429735195008025129

theorem tailTrace_6846695 : CollatzResearch.WordTrace tailWord_6846695 prefixEnd_6846695 3515645429735195008025129 := by
  unfold tailWord_6846695
  simp only [CollatzResearch.WordTrace]
  refine ⟨249719481930600812256597539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166479654620400541504398359 249719481930600812256597539)
  ·
    refine ⟨374579222895901218384896309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249719481930600812256597539 374579222895901218384896309)
    ·
      refine ⟨35116802146490739223584029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 374579222895901218384896309 35116802146490739223584029)
      ·
        refine ⟨13168800804934027208844011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35116802146490739223584029 13168800804934027208844011)
        ·
          refine ⟨19753201207401040813266017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13168800804934027208844011 19753201207401040813266017)
          ·
            refine ⟨14814900905550780609949513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19753201207401040813266017 14814900905550780609949513)
            ·
              refine ⟨11111175679163085457462135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14814900905550780609949513 11111175679163085457462135)
              ·
                refine ⟨16666763518744628186193203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111175679163085457462135 16666763518744628186193203)
                ·
                  refine ⟨25000145278116942279289805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16666763518744628186193203 25000145278116942279289805)
                  ·
                    refine ⟨9375054479293853354733677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25000145278116942279289805 9375054479293853354733677)
                    ·
                      refine ⟨3515645429735195008025129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375054479293853354733677 3515645429735195008025129)
                      ·
                        rfl

theorem cell23_6846695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_6846695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846695 prefixEnd_6846695 := by exact prefixLift 6846695
  have htrace : WordTrace (prefixWord ++ tailWord_6846695) baseStart_6846695 baseEnd_6846695 := by
    simpa [prefixWord, tailWord_6846695, baseEnd_6846695] using wordTrace_append hprefix tailTrace_6846695
  have hstable : (prefixWord ++ tailWord_6846695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846695).length < 2 ^ (prefixWord ++ tailWord_6846695).sum := by decide
  have hdescent : baseEnd_6846695 < baseStart_6846695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846721 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_6846721 : Nat := 118140960795 + 6846721 * 2 ^ 59
def prefixEnd_6846721 : Nat := 4983230072969 + 3 ^ 40 * 6846721 * 2
def baseEnd_6846721 : Nat := 3515658780232211906300009

theorem tailTrace_6846721 : CollatzResearch.WordTrace tailWord_6846721 prefixEnd_6846721 3515658780232211906300009 := by
  unfold tailWord_6846721
  simp only [CollatzResearch.WordTrace]
  refine ⟨249720430228506618697044017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166480286819004412464696011 249720430228506618697044017)
  ·
    refine ⟨187290322671379964022783013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249720430228506618697044017 187290322671379964022783013)
    ·
      refine ⟨35116935500883743254271815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187290322671379964022783013 35116935500883743254271815)
      ·
        refine ⟨52675403251325614881407723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35116935500883743254271815 52675403251325614881407723)
        ·
          refine ⟨79013104876988422322111585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52675403251325614881407723 79013104876988422322111585)
          ·
            refine ⟨59259828657741316741583689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79013104876988422322111585 59259828657741316741583689)
            ·
              refine ⟨44444871493305987556187767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59259828657741316741583689 44444871493305987556187767)
              ·
                refine ⟨66667307239958981334281651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44444871493305987556187767 66667307239958981334281651)
                ·
                  refine ⟨100000960859938472001422477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66667307239958981334281651 100000960859938472001422477)
                  ·
                    refine ⟨37500360322476927000533429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100000960859938472001422477 37500360322476927000533429)
                    ·
                      refine ⟨3515658780232211906300009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37500360322476927000533429 3515658780232211906300009)
                      ·
                        rfl

theorem cell23_6846721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_6846721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846721 prefixEnd_6846721 := by exact prefixLift 6846721
  have htrace : WordTrace (prefixWord ++ tailWord_6846721) baseStart_6846721 baseEnd_6846721 := by
    simpa [prefixWord, tailWord_6846721, baseEnd_6846721] using wordTrace_append hprefix tailTrace_6846721
  have hstable : (prefixWord ++ tailWord_6846721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846721).length < 2 ^ (prefixWord ++ tailWord_6846721).sum := by decide
  have hdescent : baseEnd_6846721 < baseStart_6846721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846731 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4]
def baseStart_6846731 : Nat := 118140960795 + 6846731 * 2 ^ 59
def prefixEnd_6846731 : Nat := 4983230072969 + 3 ^ 40 * 6846731 * 2
def baseEnd_6846731 : Nat := 3515663915038756867174963

theorem tailTrace_6846731 : CollatzResearch.WordTrace tailWord_6846731 prefixEnd_6846731 3515663915038756867174963 := by
  unfold tailWord_6846731
  simp only [CollatzResearch.WordTrace]
  refine ⟨249720794958470390404908047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166480529972313593603272031 249720794958470390404908047)
  ·
    refine ⟨374581192437705585607362071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249720794958470390404908047 374581192437705585607362071)
    ·
      refine ⟨561871788656558378411043107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374581192437705585607362071 561871788656558378411043107)
      ·
        refine ⟨842807682984837567616564661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561871788656558378411043107 842807682984837567616564661)
        ·
          refine ⟨79013220279828521964052937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 842807682984837567616564661 79013220279828521964052937)
          ·
            refine ⟨59259915209871391473039703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79013220279828521964052937 59259915209871391473039703)
            ·
              refine ⟨88889872814807087209559555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59259915209871391473039703 88889872814807087209559555)
              ·
                refine ⟨133334809222210630814339333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88889872814807087209559555 133334809222210630814339333)
                ·
                  refine ⟨25000276729164493277688625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133334809222210630814339333 25000276729164493277688625)
                  ·
                    refine ⟨18750207546873369958266469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25000276729164493277688625 18750207546873369958266469)
                    ·
                      refine ⟨3515663915038756867174963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18750207546873369958266469 3515663915038756867174963)
                      ·
                        rfl

theorem cell23_6846731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_6846731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846731 prefixEnd_6846731 := by exact prefixLift 6846731
  have htrace : WordTrace (prefixWord ++ tailWord_6846731) baseStart_6846731 baseEnd_6846731 := by
    simpa [prefixWord, tailWord_6846731, baseEnd_6846731] using wordTrace_append hprefix tailTrace_6846731
  have hstable : (prefixWord ++ tailWord_6846731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846731).length < 2 ^ (prefixWord ++ tailWord_6846731).sum := by decide
  have hdescent : baseEnd_6846731 < baseStart_6846731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846741 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 7]
def baseStart_6846741 : Nat := 118140960795 + 6846741 * 2 ^ 59
def prefixEnd_6846741 : Nat := 4983230072969 + 3 ^ 40 * 6846741 * 2
def baseEnd_6846741 : Nat := 390629894427255758672213

theorem tailTrace_6846741 : CollatzResearch.WordTrace tailWord_6846741 prefixEnd_6846741 390629894427255758672213 := by
  unfold tailWord_6846741
  simp only [CollatzResearch.WordTrace]
  refine ⟨249721159688434162112772077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166480773125622774741848051 249721159688434162112772077)
  ·
    refine ⟨93645434883162810792289529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249721159688434162112772077 93645434883162810792289529)
    ·
      refine ⟨70234076162372108094217147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93645434883162810792289529 70234076162372108094217147)
      ·
        refine ⟨105351114243558162141325721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70234076162372108094217147 105351114243558162141325721)
        ·
          refine ⟨79013335682668621605994291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105351114243558162141325721 79013335682668621605994291)
          ·
            refine ⟨118520003524002932408991437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79013335682668621605994291 118520003524002932408991437)
            ·
              refine ⟨44445001321501099653371789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118520003524002932408991437 44445001321501099653371789)
              ·
                refine ⟨16666875495562912370014421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44445001321501099653371789 16666875495562912370014421)
                ·
                  refine ⟨390629894427255758672213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16666875495562912370014421 390629894427255758672213)
                  ·
                    rfl

theorem cell23_6846741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_6846741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846741 prefixEnd_6846741 := by exact prefixLift 6846741
  have htrace : WordTrace (prefixWord ++ tailWord_6846741) baseStart_6846741 baseEnd_6846741 := by
    simpa [prefixWord, tailWord_6846741, baseEnd_6846741] using wordTrace_append hprefix tailTrace_6846741
  have hstable : (prefixWord ++ tailWord_6846741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846741).length < 2 ^ (prefixWord ++ tailWord_6846741).sum := by decide
  have hdescent : baseEnd_6846741 < baseStart_6846741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846752 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 1, 4, 2]
def baseStart_6846752 : Nat := 118140960795 + 6846752 * 2 ^ 59
def prefixEnd_6846752 : Nat := 4983230072969 + 3 ^ 40 * 6846752 * 2
def baseEnd_6846752 : Nat := 3515674698132501285012367

theorem tailTrace_6846752 : CollatzResearch.WordTrace tailWord_6846752 prefixEnd_6846752 3515674698132501285012367 := by
  unfold tailWord_6846752
  simp only [CollatzResearch.WordTrace]
  refine ⟨124860780445697155495711255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166481040594262873994281673 124860780445697155495711255)
  ·
    refine ⟨187291170668545733243566883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124860780445697155495711255 187291170668545733243566883)
    ·
      refine ⟨280936756002818599865350325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187291170668545733243566883 280936756002818599865350325)
      ·
        refine ⟨26337820875264243737376593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280936756002818599865350325 26337820875264243737376593)
        ·
          refine ⟨19753365656448182803032445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26337820875264243737376593 19753365656448182803032445)
          ·
            refine ⟨7407512121168068551137167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19753365656448182803032445 7407512121168068551137167)
            ·
              refine ⟨11111268181752102826705751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407512121168068551137167 11111268181752102826705751)
              ·
                refine ⟨16666902272628154240058627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11111268181752102826705751 16666902272628154240058627)
                ·
                  refine ⟨25000353408942231360087941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16666902272628154240058627 25000353408942231360087941)
                  ·
                    refine ⟨4687566264176668380016489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25000353408942231360087941 4687566264176668380016489)
                    ·
                      refine ⟨3515674698132501285012367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687566264176668380016489 3515674698132501285012367)
                      ·
                        rfl

theorem cell23_6846752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_6846752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846752 prefixEnd_6846752 := by exact prefixLift 6846752
  have htrace : WordTrace (prefixWord ++ tailWord_6846752) baseStart_6846752 baseEnd_6846752 := by
    simpa [prefixWord, tailWord_6846752, baseEnd_6846752] using wordTrace_append hprefix tailTrace_6846752
  have hstable : (prefixWord ++ tailWord_6846752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846752).length < 2 ^ (prefixWord ++ tailWord_6846752).sum := by decide
  have hdescent : baseEnd_6846752 < baseStart_6846752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846771 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 1, 7]
def baseStart_6846771 : Nat := 118140960795 + 6846771 * 2 ^ 59
def prefixEnd_6846771 : Nat := 4983230072969 + 3 ^ 40 * 6846771 * 2
def baseEnd_6846771 : Nat := 1171894818088312236891593

theorem tailTrace_6846771 : CollatzResearch.WordTrace tailWord_6846771 prefixEnd_6846771 1171894818088312236891593 := by
  unfold tailWord_6846771
  simp only [CollatzResearch.WordTrace]
  refine ⟨249722253878325477236364167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166481502585550318157576111 249722253878325477236364167)
  ·
    refine ⟨374583380817488215854546251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249722253878325477236364167 374583380817488215854546251)
    ·
      refine ⟨561875071226232323781819377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374583380817488215854546251 561875071226232323781819377)
      ·
        refine ⟨421406303419674242836364533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561875071226232323781819377 421406303419674242836364533)
        ·
          refine ⟨39506840945594460265909175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 421406303419674242836364533 39506840945594460265909175)
          ·
            refine ⟨59260261418391690398863763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39506840945594460265909175 59260261418391690398863763)
            ·
              refine ⟨88890392127587535598295645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59260261418391690398863763 88890392127587535598295645)
              ·
                refine ⟨33333897047845325849360867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88890392127587535598295645 33333897047845325849360867)
                ·
                  refine ⟨50000845571767988774041301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33333897047845325849360867 50000845571767988774041301)
                  ·
                    refine ⟨1171894818088312236891593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50000845571767988774041301 1171894818088312236891593)
                    ·
                      rfl

theorem cell23_6846771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 7].length) (baseStart_6846771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846771 prefixEnd_6846771 := by exact prefixLift 6846771
  have htrace : WordTrace (prefixWord ++ tailWord_6846771) baseStart_6846771 baseEnd_6846771 := by
    simpa [prefixWord, tailWord_6846771, baseEnd_6846771] using wordTrace_append hprefix tailTrace_6846771
  have hstable : (prefixWord ++ tailWord_6846771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846771).length < 2 ^ (prefixWord ++ tailWord_6846771).sum := by decide
  have hdescent : baseEnd_6846771 < baseStart_6846771 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846831 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 8]
def baseStart_6846831 : Nat := 118140960795 + 6846831 * 2 ^ 59
def prefixEnd_6846831 : Nat := 4983230072969 + 3 ^ 40 * 6846831 * 2
def baseEnd_6846831 : Nat := 390635029233800719547167

theorem tailTrace_6846831 : CollatzResearch.WordTrace tailWord_6846831 prefixEnd_6846831 390635029233800719547167 := by
  unfold tailWord_6846831
  simp only [CollatzResearch.WordTrace]
  refine ⟨249724442258108107483548347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166482961505405404989032231 249724442258108107483548347)
  ·
    refine ⟨374586663387162161225322521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249724442258108107483548347 374586663387162161225322521)
    ·
      refine ⟨280939997540371620918991891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374586663387162161225322521 280939997540371620918991891)
      ·
        refine ⟨421409996310557431378487837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280939997540371620918991891 421409996310557431378487837)
        ·
          refine ⟨158028748616459036766932939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421409996310557431378487837 158028748616459036766932939)
          ·
            refine ⟨237043122924688555150399409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158028748616459036766932939 237043122924688555150399409)
            ·
              refine ⟨177782342193516416362799557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237043122924688555150399409 177782342193516416362799557)
              ·
                refine ⟨33334189161284328068024917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177782342193516416362799557 33334189161284328068024917)
                ·
                  refine ⟨390635029233800719547167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33334189161284328068024917 390635029233800719547167)
                  ·
                    rfl

theorem cell23_6846831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 8].length) (baseStart_6846831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846831 prefixEnd_6846831 := by exact prefixLift 6846831
  have htrace : WordTrace (prefixWord ++ tailWord_6846831) baseStart_6846831 baseEnd_6846831 := by
    simpa [prefixWord, tailWord_6846831, baseEnd_6846831] using wordTrace_append hprefix tailTrace_6846831
  have hstable : (prefixWord ++ tailWord_6846831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846831).length < 2 ^ (prefixWord ++ tailWord_6846831).sum := by decide
  have hdescent : baseEnd_6846831 < baseStart_6846831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846845 : List Nat := [1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 3]
def baseStart_6846845 : Nat := 118140960795 + 6846845 * 2 ^ 59
def prefixEnd_6846845 : Nat := 4983230072969 + 3 ^ 40 * 6846845 * 2
def baseEnd_6846845 : Nat := 3515722451833369421149439

theorem tailTrace_6846845 : CollatzResearch.WordTrace tailWord_6846845 prefixEnd_6846845 3515722451833369421149439 := by
  unfold tailWord_6846845
  simp only [CollatzResearch.WordTrace]
  refine ⟨249724952880057387874557989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166483301920038258583038659 249724952880057387874557989)
  ·
    refine ⟨46823428665010760226479623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249724952880057387874557989 46823428665010760226479623)
    ·
      refine ⟨70235142997516140339719435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46823428665010760226479623 70235142997516140339719435)
      ·
        refine ⟨105352714496274210509579153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70235142997516140339719435 105352714496274210509579153)
        ·
          refine ⟨79014535872205657882184365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105352714496274210509579153 79014535872205657882184365)
          ·
            refine ⟨29630450952077121705819137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79014535872205657882184365 29630450952077121705819137)
            ·
              refine ⟨22222838214057841279364353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29630450952077121705819137 22222838214057841279364353)
              ·
                refine ⟨16667128660543380959523265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22222838214057841279364353 16667128660543380959523265)
                ·
                  refine ⟨12500346495407535719642449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16667128660543380959523265 12500346495407535719642449)
                  ·
                    refine ⟨9375259871555651789731837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12500346495407535719642449 9375259871555651789731837)
                    ·
                      refine ⟨3515722451833369421149439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375259871555651789731837 3515722451833369421149439)
                      ·
                        rfl

theorem cell23_6846845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_6846845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846845 prefixEnd_6846845 := by exact prefixLift 6846845
  have htrace : WordTrace (prefixWord ++ tailWord_6846845) baseStart_6846845 baseEnd_6846845 := by
    simpa [prefixWord, tailWord_6846845, baseEnd_6846845] using wordTrace_append hprefix tailTrace_6846845
  have hstable : (prefixWord ++ tailWord_6846845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846845).length < 2 ^ (prefixWord ++ tailWord_6846845).sum := by decide
  have hdescent : baseEnd_6846845 < baseStart_6846845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846852 : List Nat := [2, 3, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_6846852 : Nat := 118140960795 + 6846852 * 2 ^ 59
def prefixEnd_6846852 : Nat := 4983230072969 + 3 ^ 40 * 6846852 * 2
def baseEnd_6846852 : Nat := 1171908682065983631253969

theorem tailTrace_6846852 : CollatzResearch.WordTrace tailWord_6846852 prefixEnd_6846852 1171908682065983631253969 := by
  unfold tailWord_6846852
  simp only [CollatzResearch.WordTrace]
  refine ⟨124862604095516014035031405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166483472127354685380041873 124862604095516014035031405)
  ·
    refine ⟨46823476535818505263136777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124862604095516014035031405 46823476535818505263136777)
    ·
      refine ⟨35117607401863878947352583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46823476535818505263136777 35117607401863878947352583)
      ·
        refine ⟨52676411102795818421028875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35117607401863878947352583 52676411102795818421028875)
        ·
          refine ⟨79014616654193727631543313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52676411102795818421028875 79014616654193727631543313)
          ·
            refine ⟨59260962490645295723657485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79014616654193727631543313 59260962490645295723657485)
            ·
              refine ⟨22222860933991985896371557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59260962490645295723657485 22222860933991985896371557)
              ·
                refine ⟨4166786425123497355569667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22222860933991985896371557 4166786425123497355569667)
                ·
                  refine ⟨6250179637685246033354501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166786425123497355569667 6250179637685246033354501)
                  ·
                    refine ⟨1171908682065983631253969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250179637685246033354501 1171908682065983631253969)
                    ·
                      rfl

theorem cell23_6846852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_6846852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846852 prefixEnd_6846852 := by exact prefixLift 6846852
  have htrace : WordTrace (prefixWord ++ tailWord_6846852) baseStart_6846852 baseEnd_6846852 := by
    simpa [prefixWord, tailWord_6846852, baseEnd_6846852] using wordTrace_append hprefix tailTrace_6846852
  have hstable : (prefixWord ++ tailWord_6846852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846852).length < 2 ^ (prefixWord ++ tailWord_6846852).sum := by decide
  have hdescent : baseEnd_6846852 < baseStart_6846852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846885 : List Nat := [1, 3, 1, 2, 1, 1, 5, 1, 1, 5, 2]
def baseStart_6846885 : Nat := 118140960795 + 6846885 * 2 ^ 59
def prefixEnd_6846885 : Nat := 4983230072969 + 3 ^ 40 * 6846885 * 2
def baseEnd_6846885 : Nat := 3515742991059549264649255

theorem tailTrace_6846885 : CollatzResearch.WordTrace tailWord_6846885 prefixEnd_6846885 3515742991059549264649255 := by
  unfold tailWord_6846885
  simp only [CollatzResearch.WordTrace]
  refine ⟨249726411799912474706014109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166484274533274983137342739 249726411799912474706014109)
  ·
    refine ⟨93647404424967178014755291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249726411799912474706014109 93647404424967178014755291)
    ·
      refine ⟨140471106637450767022132937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93647404424967178014755291 140471106637450767022132937)
      ·
        refine ⟨105353329978088075266599703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140471106637450767022132937 105353329978088075266599703)
        ·
          refine ⟨158029994967132112899899555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105353329978088075266599703 158029994967132112899899555)
          ·
            refine ⟨237044992450698169349849333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158029994967132112899899555 237044992450698169349849333)
            ·
              refine ⟨22222968042252953376548375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237044992450698169349849333 22222968042252953376548375)
              ·
                refine ⟨33334452063379430064822563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22222968042252953376548375 33334452063379430064822563)
                ·
                  refine ⟨50001678095069145097233845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33334452063379430064822563 50001678095069145097233845)
                  ·
                    refine ⟨4687657321412732352865673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50001678095069145097233845 4687657321412732352865673)
                    ·
                      refine ⟨3515742991059549264649255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687657321412732352865673 3515742991059549264649255)
                      ·
                        rfl

theorem cell23_6846885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_6846885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846885 prefixEnd_6846885 := by exact prefixLift 6846885
  have htrace : WordTrace (prefixWord ++ tailWord_6846885) baseStart_6846885 baseEnd_6846885 := by
    simpa [prefixWord, tailWord_6846885, baseEnd_6846885] using wordTrace_append hprefix tailTrace_6846885
  have hstable : (prefixWord ++ tailWord_6846885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846885).length < 2 ^ (prefixWord ++ tailWord_6846885).sum := by decide
  have hdescent : baseEnd_6846885 < baseStart_6846885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846909 : List Nat := [1, 4, 1, 2, 2, 2, 2, 4, 1, 1, 3]
def baseStart_6846909 : Nat := 118140960795 + 6846909 * 2 ^ 59
def prefixEnd_6846909 : Nat := 4983230072969 + 3 ^ 40 * 6846909 * 2
def baseEnd_6846909 : Nat := 3515755314595257170749145

theorem tailTrace_6846909 : CollatzResearch.WordTrace tailWord_6846909 prefixEnd_6846909 3515755314595257170749145 := by
  unfold tailWord_6846909
  simp only [CollatzResearch.WordTrace]
  refine ⟨249727287151825526804887781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166484858101217017869925187 249727287151825526804887781)
  ·
    refine ⟨46823866340967286275916459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249727287151825526804887781 46823866340967286275916459)
    ·
      refine ⟨70235799511450929413874689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46823866340967286275916459 70235799511450929413874689)
      ·
        refine ⟨52676849633588197060406017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70235799511450929413874689 52676849633588197060406017)
        ·
          refine ⟨39507637225191147795304513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52676849633588197060406017 39507637225191147795304513)
          ·
            refine ⟨29630727918893360846478385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39507637225191147795304513 29630727918893360846478385)
            ·
              refine ⟨22223045939170020634858789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29630727918893360846478385 22223045939170020634858789)
              ·
                refine ⟨4166821113594378869036023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22223045939170020634858789 4166821113594378869036023)
                ·
                  refine ⟨6250231670391568303554035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4166821113594378869036023 6250231670391568303554035)
                  ·
                    refine ⟨9375347505587352455331053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6250231670391568303554035 9375347505587352455331053)
                    ·
                      refine ⟨3515755314595257170749145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375347505587352455331053 3515755314595257170749145)
                      ·
                        rfl

theorem cell23_6846909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_6846909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846909 prefixEnd_6846909 := by exact prefixLift 6846909
  have htrace : WordTrace (prefixWord ++ tailWord_6846909) baseStart_6846909 baseEnd_6846909 := by
    simpa [prefixWord, tailWord_6846909, baseEnd_6846909] using wordTrace_append hprefix tailTrace_6846909
  have hstable : (prefixWord ++ tailWord_6846909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846909).length < 2 ^ (prefixWord ++ tailWord_6846909).sum := by decide
  have hdescent : baseEnd_6846909 < baseStart_6846909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846932 : List Nat := [2, 4, 1, 2, 2, 1, 1, 4, 1, 1, 4]
def baseStart_6846932 : Nat := 118140960795 + 6846932 * 2 ^ 59
def prefixEnd_6846932 : Nat := 4983230072969 + 3 ^ 40 * 6846932 * 2
def baseEnd_6846932 : Nat := 3515767124650310580761539

theorem tailTrace_6846932 : CollatzResearch.WordTrace tailWord_6846932 prefixEnd_6846932 3515767124650310580761539 := by
  unfold tailWord_6846932
  simp only [CollatzResearch.WordTrace]
  refine ⟨124864063015371100866487525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166485417353828134488650033 124864063015371100866487525)
  ·
    refine ⟨23412011815382081412466411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124864063015371100866487525 23412011815382081412466411)
    ·
      refine ⟨35118017723073122118699617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23412011815382081412466411 35118017723073122118699617)
      ·
        refine ⟨26338513292304841589024713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35118017723073122118699617 26338513292304841589024713)
        ·
          refine ⟨19753884969228631191768535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26338513292304841589024713 19753884969228631191768535)
          ·
            refine ⟨29630827453842946787652803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19753884969228631191768535 29630827453842946787652803)
            ·
              refine ⟨44446241180764420181479205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29630827453842946787652803 44446241180764420181479205)
              ·
                refine ⟨8333670221393328784027351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44446241180764420181479205 8333670221393328784027351)
                ·
                  refine ⟨12500505332089993176041027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8333670221393328784027351 12500505332089993176041027)
                  ·
                    refine ⟨18750757998134989764061541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12500505332089993176041027 18750757998134989764061541)
                    ·
                      refine ⟨3515767124650310580761539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18750757998134989764061541 3515767124650310580761539)
                      ·
                        rfl

theorem cell23_6846932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_6846932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846932 prefixEnd_6846932 := by exact prefixLift 6846932
  have htrace : WordTrace (prefixWord ++ tailWord_6846932) baseStart_6846932 baseEnd_6846932 := by
    simpa [prefixWord, tailWord_6846932, baseEnd_6846932] using wordTrace_append hprefix tailTrace_6846932
  have hstable : (prefixWord ++ tailWord_6846932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846932).length < 2 ^ (prefixWord ++ tailWord_6846932).sum := by decide
  have hdescent : baseEnd_6846932 < baseStart_6846932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846938 : List Nat := [3, 1, 1, 2, 3, 1, 3, 9]
def baseStart_6846938 : Nat := 118140960795 + 6846938 * 2 ^ 59
def prefixEnd_6846938 : Nat := 4983230072969 + 3 ^ 40 * 6846938 * 2
def baseEnd_6846938 : Nat := 130213711316082872492093

theorem tailTrace_6846938 : CollatzResearch.WordTrace tailWord_6846938 prefixEnd_6846938 130213711316082872492093 := by
  unfold tailWord_6846938
  simp only [CollatzResearch.WordTrace]
  refine ⟨62432086217180116189423367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166485563245813643171795645 62432086217180116189423367)
  ·
    refine ⟨93648129325770174284135051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62432086217180116189423367 93648129325770174284135051)
    ·
      refine ⟨140472193988655261426202577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93648129325770174284135051 140472193988655261426202577)
      ·
        refine ⟨105354145491491446069651933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140472193988655261426202577 105354145491491446069651933)
        ·
          refine ⟨39507804559309292276119475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105354145491491446069651933 39507804559309292276119475)
          ·
            refine ⟨59261706838963938414179213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39507804559309292276119475 59261706838963938414179213)
            ·
              refine ⟨22223140064611476905317205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59261706838963938414179213 22223140064611476905317205)
              ·
                refine ⟨130213711316082872492093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22223140064611476905317205 130213711316082872492093)
                ·
                  rfl

theorem cell23_6846938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_6846938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846938 prefixEnd_6846938 := by exact prefixLift 6846938
  have htrace : WordTrace (prefixWord ++ tailWord_6846938) baseStart_6846938 baseEnd_6846938 := by
    simpa [prefixWord, tailWord_6846938, baseEnd_6846938] using wordTrace_append hprefix tailTrace_6846938
  have hstable : (prefixWord ++ tailWord_6846938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846938).length < 2 ^ (prefixWord ++ tailWord_6846938).sum := by decide
  have hdescent : baseEnd_6846938 < baseStart_6846938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846952 : List Nat := [2, 1, 4, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_6846952 : Nat := 118140960795 + 6846952 * 2 ^ 59
def prefixEnd_6846952 : Nat := 4983230072969 + 3 ^ 40 * 6846952 * 2
def baseEnd_6846952 : Nat := 3515777394263400502511447

theorem tailTrace_6846952 : CollatzResearch.WordTrace tailWord_6846952 prefixEnd_6846952 3515777394263400502511447 := by
  unfold tailWord_6846952
  simp only [CollatzResearch.WordTrace]
  refine ⟨124864427745334872574351555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166485903660446496765802073 124864427745334872574351555)
  ·
    refine ⟨187296641618002308861527333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124864427745334872574351555 187296641618002308861527333)
    ·
      refine ⟨35118120303375432911536375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187296641618002308861527333 35118120303375432911536375)
      ·
        refine ⟨52677180455063149367304563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35118120303375432911536375 52677180455063149367304563)
        ·
          refine ⟨79015770682594724050956845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52677180455063149367304563 79015770682594724050956845)
          ·
            refine ⟨29630914005973021519108817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79015770682594724050956845 29630914005973021519108817)
            ·
              refine ⟨22223185504479766139331613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29630914005973021519108817 22223185504479766139331613)
              ·
                refine ⟨8333694564179912302249355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22223185504479766139331613 8333694564179912302249355)
                ·
                  refine ⟨12500541846269868453374033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8333694564179912302249355 12500541846269868453374033)
                  ·
                    refine ⟨9375406384702401340030525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12500541846269868453374033 9375406384702401340030525)
                    ·
                      refine ⟨3515777394263400502511447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375406384702401340030525 3515777394263400502511447)
                      ·
                        rfl

theorem cell23_6846952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_6846952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846952 prefixEnd_6846952 := by exact prefixLift 6846952
  have htrace : WordTrace (prefixWord ++ tailWord_6846952) baseStart_6846952 baseEnd_6846952 := by
    simpa [prefixWord, tailWord_6846952, baseEnd_6846952] using wordTrace_append hprefix tailTrace_6846952
  have hstable : (prefixWord ++ tailWord_6846952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846952).length < 2 ^ (prefixWord ++ tailWord_6846952).sum := by decide
  have hdescent : baseEnd_6846952 < baseStart_6846952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846968 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 2, 7]
def baseStart_6846968 : Nat := 118140960795 + 6846968 * 2 ^ 59
def prefixEnd_6846968 : Nat := 4983230072969 + 3 ^ 40 * 6846968 * 2
def baseEnd_6846968 : Nat := 1171928536651290813303791

theorem tailTrace_6846968 : CollatzResearch.WordTrace tailWord_6846968 prefixEnd_6846968 1171928536651290813303791 := by
  unfold tailWord_6846968
  simp only [CollatzResearch.WordTrace]
  refine ⟨124864719529305889940642779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166486292705741186587523705 124864719529305889940642779)
  ·
    refine ⟨187297079293958834910964169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124864719529305889940642779 187297079293958834910964169)
    ·
      refine ⟨140472809470469126183223127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187297079293958834910964169 140472809470469126183223127)
      ·
        refine ⟨210709214205703689274834691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140472809470469126183223127 210709214205703689274834691)
        ·
          refine ⟨316063821308555533912252037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210709214205703689274834691 316063821308555533912252037)
          ·
            refine ⟨59261966495354162608547257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 316063821308555533912252037 59261966495354162608547257)
            ·
              refine ⟨44446474871515621956410443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59261966495354162608547257 44446474871515621956410443)
              ·
                refine ⟨66669712307273432934615665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44446474871515621956410443 66669712307273432934615665)
                ·
                  refine ⟨50002284230455074700961749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66669712307273432934615665 50002284230455074700961749)
                  ·
                    refine ⟨1171928536651290813303791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50002284230455074700961749 1171928536651290813303791)
                    ·
                      rfl

theorem cell23_6846968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_6846968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846968 prefixEnd_6846968 := by exact prefixLift 6846968
  have htrace : WordTrace (prefixWord ++ tailWord_6846968) baseStart_6846968 baseEnd_6846968 := by
    simpa [prefixWord, tailWord_6846968, baseEnd_6846968] using wordTrace_append hprefix tailTrace_6846968
  have hstable : (prefixWord ++ tailWord_6846968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846968).length < 2 ^ (prefixWord ++ tailWord_6846968).sum := by decide
  have hdescent : baseEnd_6846968 < baseStart_6846968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6846999 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6846999 : Nat := 118140960795 + 6846999 * 2 ^ 59
def prefixEnd_6846999 : Nat := 4983230072969 + 3 ^ 40 * 6846999 * 2
def baseEnd_6846999 : Nat := 3515801527854161818623731

theorem tailTrace_6846999 : CollatzResearch.WordTrace tailWord_6846999 prefixEnd_6846999 3515801527854161818623731 := by
  unfold tailWord_6846999
  simp only [CollatzResearch.WordTrace]
  refine ⟨249730569721499472175664051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166487046480999648117109367 249730569721499472175664051)
  ·
    refine ⟨374595854582249208263496077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249730569721499472175664051 374595854582249208263496077)
    ·
      refine ⟨140473445468343453098811029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374595854582249208263496077 140473445468343453098811029)
      ·
        refine ⟨6584692756328599364006767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140473445468343453098811029 6584692756328599364006767)
        ·
          refine ⟨9877039134492899046010151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584692756328599364006767 9877039134492899046010151)
          ·
            refine ⟨14815558701739348569015227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9877039134492899046010151 14815558701739348569015227)
            ·
              refine ⟨22223338052609022853522841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14815558701739348569015227 22223338052609022853522841)
              ·
                refine ⟨16667503539456767140142131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22223338052609022853522841 16667503539456767140142131)
                ·
                  refine ⟨25001255309185150710213197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16667503539456767140142131 25001255309185150710213197)
                  ·
                    refine ⟨9375470740944431516329949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25001255309185150710213197 9375470740944431516329949)
                    ·
                      refine ⟨3515801527854161818623731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375470740944431516329949 3515801527854161818623731)
                      ·
                        rfl

theorem cell23_6846999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6846999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6846999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6846999 prefixEnd_6846999 := by exact prefixLift 6846999
  have htrace : WordTrace (prefixWord ++ tailWord_6846999) baseStart_6846999 baseEnd_6846999 := by
    simpa [prefixWord, tailWord_6846999, baseEnd_6846999] using wordTrace_append hprefix tailTrace_6846999
  have hstable : (prefixWord ++ tailWord_6846999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6846999).length < 2 ^ (prefixWord ++ tailWord_6846999).sum := by decide
  have hdescent : baseEnd_6846999 < baseStart_6846999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6846999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847016 : List Nat := [2, 1, 5, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6847016 : Nat := 118140960795 + 6847016 * 2 ^ 59
def prefixEnd_6847016 : Nat := 4983230072969 + 3 ^ 40 * 6847016 * 2
def baseEnd_6847016 : Nat := 3515810257025288252111153

theorem tailTrace_6847016 : CollatzResearch.WordTrace tailWord_6847016 prefixEnd_6847016 3515810257025288252111153 := by
  unfold tailWord_6847016
  simp only [CollatzResearch.WordTrace]
  refine ⟨124865594881218942039516451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166487459841625256052688601 124865594881218942039516451)
  ·
    refine ⟨187298392321828413059274677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124865594881218942039516451 187298392321828413059274677)
    ·
      refine ⟨17559224280171413724307001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 187298392321828413059274677 17559224280171413724307001)
      ·
        refine ⟨13169418210128560293230251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17559224280171413724307001 13169418210128560293230251)
        ·
          refine ⟨19754127315192840439845377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13169418210128560293230251 19754127315192840439845377)
          ·
            refine ⟨14815595486394630329884033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19754127315192840439845377 14815595486394630329884033)
            ·
              refine ⟨11111696614795972747413025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14815595486394630329884033 11111696614795972747413025)
              ·
                refine ⟨8333772461096979560559769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11111696614795972747413025 8333772461096979560559769)
                ·
                  refine ⟨6250329345822734670419827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8333772461096979560559769 6250329345822734670419827)
                  ·
                    refine ⟨9375494018734102005629741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6250329345822734670419827 9375494018734102005629741)
                    ·
                      refine ⟨3515810257025288252111153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375494018734102005629741 3515810257025288252111153)
                      ·
                        rfl

theorem cell23_6847016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6847016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847016 prefixEnd_6847016 := by exact prefixLift 6847016
  have htrace : WordTrace (prefixWord ++ tailWord_6847016) baseStart_6847016 baseEnd_6847016 := by
    simpa [prefixWord, tailWord_6847016, baseEnd_6847016] using wordTrace_append hprefix tailTrace_6847016
  have hstable : (prefixWord ++ tailWord_6847016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847016).length < 2 ^ (prefixWord ++ tailWord_6847016).sum := by decide
  have hdescent : baseEnd_6847016 < baseStart_6847016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847025 : List Nat := [1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_6847025 : Nat := 118140960795 + 6847025 * 2 ^ 59
def prefixEnd_6847025 : Nat := 4983230072969 + 3 ^ 40 * 6847025 * 2
def baseEnd_6847025 : Nat := 3515814878351178716898611

theorem tailTrace_6847025 : CollatzResearch.WordTrace tailWord_6847025 prefixEnd_6847025 3515814878351178716898611 := by
  unfold tailWord_6847025
  simp only [CollatzResearch.WordTrace]
  refine ⟨249731518019405278616110529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166487678679603519077407019 249731518019405278616110529)
  ·
    refine ⟨187298638514553958962082897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249731518019405278616110529 187298638514553958962082897)
    ·
      refine ⟨140473978885915469221562173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187298638514553958962082897 140473978885915469221562173)
      ·
        refine ⟨52677742082218300958085815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140473978885915469221562173 52677742082218300958085815)
        ·
          refine ⟨79016613123327451437128723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52677742082218300958085815 79016613123327451437128723)
          ·
            refine ⟨118524919684991177155693085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79016613123327451437128723 118524919684991177155693085)
            ·
              refine ⟨44446844881871691433384907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118524919684991177155693085 44446844881871691433384907)
              ·
                refine ⟨66670267322807537150077361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44446844881871691433384907 66670267322807537150077361)
                ·
                  refine ⟨50002700492105652862558021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66670267322807537150077361 50002700492105652862558021)
                  ·
                    refine ⟨9375506342269809911729629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50002700492105652862558021 9375506342269809911729629)
                    ·
                      refine ⟨3515814878351178716898611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375506342269809911729629 3515814878351178716898611)
                      ·
                        rfl

theorem cell23_6847025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_6847025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847025 prefixEnd_6847025 := by exact prefixLift 6847025
  have htrace : WordTrace (prefixWord ++ tailWord_6847025) baseStart_6847025 baseEnd_6847025 := by
    simpa [prefixWord, tailWord_6847025, baseEnd_6847025] using wordTrace_append hprefix tailTrace_6847025
  have hstable : (prefixWord ++ tailWord_6847025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847025).length < 2 ^ (prefixWord ++ tailWord_6847025).sum := by decide
  have hdescent : baseEnd_6847025 < baseStart_6847025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847039 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 2, 2, 2]
def baseStart_6847039 : Nat := 118140960795 + 6847039 * 2 ^ 59
def prefixEnd_6847039 : Nat := 4983230072969 + 3 ^ 40 * 6847039 * 2
def baseEnd_6847039 : Nat := 3515822067080341662123547

theorem tailTrace_6847039 : CollatzResearch.WordTrace tailWord_6847039 prefixEnd_6847039 3515822067080341662123547 := by
  unfold tailWord_6847039
  simp only [CollatzResearch.WordTrace]
  refine ⟨249732028641354559007120171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166488019094236372671413447 249732028641354559007120171)
  ·
    refine ⟨374598042962031838510680257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249732028641354559007120171 374598042962031838510680257)
    ·
      refine ⟨280948532221523878883010193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 374598042962031838510680257 280948532221523878883010193)
      ·
        refine ⟨210711399166142909162257645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280948532221523878883010193 210711399166142909162257645)
        ·
          refine ⟨79016774687303590935846617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210711399166142909162257645 79016774687303590935846617)
          ·
            refine ⟨59262581015477693201884963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79016774687303590935846617 59262581015477693201884963)
            ·
              refine ⟨88893871523216539802827445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59262581015477693201884963 88893871523216539802827445)
              ·
                refine ⟨8333800455301550606515073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88893871523216539802827445 8333800455301550606515073)
                ·
                  refine ⟨6250350341476162954886305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8333800455301550606515073 6250350341476162954886305)
                  ·
                    refine ⟨4687762756107122216164729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6250350341476162954886305 4687762756107122216164729)
                    ·
                      refine ⟨3515822067080341662123547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687762756107122216164729 3515822067080341662123547)
                      ·
                        rfl

theorem cell23_6847039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_6847039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847039 prefixEnd_6847039 := by exact prefixLift 6847039
  have htrace : WordTrace (prefixWord ++ tailWord_6847039) baseStart_6847039 baseEnd_6847039 := by
    simpa [prefixWord, tailWord_6847039, baseEnd_6847039] using wordTrace_append hprefix tailTrace_6847039
  have hstable : (prefixWord ++ tailWord_6847039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847039).length < 2 ^ (prefixWord ++ tailWord_6847039).sum := by decide
  have hdescent : baseEnd_6847039 < baseStart_6847039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847045 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 7]
def baseStart_6847045 : Nat := 118140960795 + 6847045 * 2 ^ 59
def prefixEnd_6847045 : Nat := 4983230072969 + 3 ^ 40 * 6847045 * 2
def baseEnd_6847045 : Nat := 390647238662696515405391

theorem tailTrace_6847045 : CollatzResearch.WordTrace tailWord_6847045 prefixEnd_6847045 390647238662696515405391 := by
  unfold tailWord_6847045
  simp only [CollatzResearch.WordTrace]
  refine ⟨249732247479332822031838589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166488164986221881354559059 249732247479332822031838589)
  ·
    refine ⟨93649592804749808261939471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249732247479332822031838589 93649592804749808261939471)
    ·
      refine ⟨140474389207124712392909207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93649592804749808261939471 140474389207124712392909207)
      ·
        refine ⟨210711583810687068589363811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140474389207124712392909207 210711583810687068589363811)
        ·
          refine ⟨316067375716030602884045717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210711583810687068589363811 316067375716030602884045717)
          ·
            refine ⟨14815658236688934510189643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 316067375716030602884045717 14815658236688934510189643)
            ·
              refine ⟨22223487355033401765284465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14815658236688934510189643 22223487355033401765284465)
              ·
                refine ⟨16667615516275051323963349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22223487355033401765284465 16667615516275051323963349)
                ·
                  refine ⟨390647238662696515405391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16667615516275051323963349 390647238662696515405391)
                  ·
                    rfl

theorem cell23_6847045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_6847045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847045 prefixEnd_6847045 := by exact prefixLift 6847045
  have htrace : WordTrace (prefixWord ++ tailWord_6847045) baseStart_6847045 baseEnd_6847045 := by
    simpa [prefixWord, tailWord_6847045, baseEnd_6847045] using wordTrace_append hprefix tailTrace_6847045
  have hstable : (prefixWord ++ tailWord_6847045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847045).length < 2 ^ (prefixWord ++ tailWord_6847045).sum := by decide
  have hdescent : baseEnd_6847045 < baseStart_6847045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847075 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 4, 5]
def baseStart_6847075 : Nat := 118140960795 + 6847075 * 2 ^ 59
def prefixEnd_6847075 : Nat := 4983230072969 + 3 ^ 40 * 6847075 * 2
def baseEnd_6847075 : Nat := 1171946850794634507091127

theorem tailTrace_6847075 : CollatzResearch.WordTrace tailWord_6847075 prefixEnd_6847075 1171946850794634507091127 := by
  unfold tailWord_6847075
  simp only [CollatzResearch.WordTrace]
  refine ⟨249733341669224137155430679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166488894446149424770287119 249733341669224137155430679)
  ·
    refine ⟨374600012503836205733146019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249733341669224137155430679 374600012503836205733146019)
    ·
      refine ⟨561900018755754308599719029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374600012503836205733146019 561900018755754308599719029)
      ·
        refine ⟨52678126758351966431223659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 561900018755754308599719029 52678126758351966431223659)
        ·
          refine ⟨79017190137527949646835489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52678126758351966431223659 79017190137527949646835489)
          ·
            refine ⟨59262892603145962235126617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79017190137527949646835489 59262892603145962235126617)
            ·
              refine ⟨44447169452359471676344963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59262892603145962235126617 44447169452359471676344963)
              ·
                refine ⟨66670754178539207514517445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44447169452359471676344963 66670754178539207514517445)
                ·
                  refine ⟨12500766408476101408972021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66670754178539207514517445 12500766408476101408972021)
                  ·
                    refine ⟨1171946850794634507091127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12500766408476101408972021 1171946850794634507091127)
                    ·
                      rfl

theorem cell23_6847075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 5].length) (baseStart_6847075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847075 prefixEnd_6847075 := by exact prefixLift 6847075
  have htrace : WordTrace (prefixWord ++ tailWord_6847075) baseStart_6847075 baseEnd_6847075 := by
    simpa [prefixWord, tailWord_6847075, baseEnd_6847075] using wordTrace_append hprefix tailTrace_6847075
  have hstable : (prefixWord ++ tailWord_6847075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847075).length < 2 ^ (prefixWord ++ tailWord_6847075).sum := by decide
  have hdescent : baseEnd_6847075 < baseStart_6847075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847095 : List Nat := [1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_6847095 : Nat := 118140960795 + 6847095 * 2 ^ 59
def prefixEnd_6847095 : Nat := 4983230072969 + 3 ^ 40 * 6847095 * 2
def baseEnd_6847095 : Nat := 3515850821996993443023289

theorem tailTrace_6847095 : CollatzResearch.WordTrace tailWord_6847095 prefixEnd_6847095 3515850821996993443023289 := by
  unfold tailWord_6847095
  simp only [CollatzResearch.WordTrace]
  refine ⟨249734071129151680571158739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166489380752767787047439159 249734071129151680571158739)
  ·
    refine ⟨374601106693727520856738109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249734071129151680571158739 374601106693727520856738109)
    ·
      refine ⟨140475415010147820321276791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 374601106693727520856738109 140475415010147820321276791)
      ·
        refine ⟨210713122515221730481915187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140475415010147820321276791 210713122515221730481915187)
        ·
          refine ⟨316069683772832595722872781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210713122515221730481915187 316069683772832595722872781)
          ·
            refine ⟨118526131414812223396077293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316069683772832595722872781 118526131414812223396077293)
            ·
              refine ⟨44447299280554583773528985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118526131414812223396077293 44447299280554583773528985)
              ·
                refine ⟨33335474460415937830146739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44447299280554583773528985 33335474460415937830146739)
                ·
                  refine ⟨50003211690623906745220109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33335474460415937830146739 50003211690623906745220109)
                  ·
                    refine ⟨18751204383983965029457541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50003211690623906745220109 18751204383983965029457541)
                    ·
                      refine ⟨3515850821996993443023289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18751204383983965029457541 3515850821996993443023289)
                      ·
                        rfl

theorem cell23_6847095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_6847095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847095 prefixEnd_6847095 := by exact prefixLift 6847095
  have htrace : WordTrace (prefixWord ++ tailWord_6847095) baseStart_6847095 baseEnd_6847095 := by
    simpa [prefixWord, tailWord_6847095, baseEnd_6847095] using wordTrace_append hprefix tailTrace_6847095
  have hstable : (prefixWord ++ tailWord_6847095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847095).length < 2 ^ (prefixWord ++ tailWord_6847095).sum := by decide
  have hdescent : baseEnd_6847095 < baseStart_6847095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847105 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 2, 8]
def baseStart_6847105 : Nat := 118140960795 + 6847105 * 2 ^ 59
def prefixEnd_6847105 : Nat := 4983230072969 + 3 ^ 40 * 6847105 * 2
def baseEnd_6847105 : Nat := 1171951985601179467966081

theorem tailTrace_6847105 : CollatzResearch.WordTrace tailWord_6847105 prefixEnd_6847105 1171951985601179467966081 := by
  unfold tailWord_6847105
  simp only [CollatzResearch.WordTrace]
  refine ⟨249734435859115452279022769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166489623906076968186015179 249734435859115452279022769)
  ·
    refine ⟨187300826894336589209267077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249734435859115452279022769 187300826894336589209267077)
    ·
      refine ⟨35118905042688110476737577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 187300826894336589209267077 35118905042688110476737577)
      ·
        refine ⟨26339178782016082857553183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35118905042688110476737577 26339178782016082857553183)
        ·
          refine ⟨39508768173024124286329775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26339178782016082857553183 39508768173024124286329775)
          ·
            refine ⟨59263152259536186429494663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39508768173024124286329775 59263152259536186429494663)
            ·
              refine ⟨88894728389304279644241995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59263152259536186429494663 88894728389304279644241995)
              ·
                refine ⟨133342092583956419466362993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88894728389304279644241995 133342092583956419466362993)
                ·
                  refine ⟨100006569437967314599772245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133342092583956419466362993 100006569437967314599772245)
                  ·
                    refine ⟨1171951985601179467966081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100006569437967314599772245 1171951985601179467966081)
                    ·
                      rfl

theorem cell23_6847105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_6847105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847105 prefixEnd_6847105 := by exact prefixLift 6847105
  have htrace : WordTrace (prefixWord ++ tailWord_6847105) baseStart_6847105 baseEnd_6847105 := by
    simpa [prefixWord, tailWord_6847105, baseEnd_6847105] using wordTrace_append hprefix tailTrace_6847105
  have hstable : (prefixWord ++ tailWord_6847105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847105).length < 2 ^ (prefixWord ++ tailWord_6847105).sum := by decide
  have hdescent : baseEnd_6847105 < baseStart_6847105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847175 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_6847175 : Nat := 118140960795 + 6847175 * 2 ^ 59
def prefixEnd_6847175 : Nat := 4983230072969 + 3 ^ 40 * 6847175 * 2
def baseEnd_6847175 : Nat := 3515891900449353130022921

theorem tailTrace_6847175 : CollatzResearch.WordTrace tailWord_6847175 prefixEnd_6847175 3515891900449353130022921 := by
  unfold tailWord_6847175
  simp only [CollatzResearch.WordTrace]
  refine ⟨249736988968861854234070979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166491325979241236156047319 249736988968861854234070979)
  ·
    refine ⟨374605483453292781351106469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249736988968861854234070979 374605483453292781351106469)
    ·
      refine ⟨70238528147492396503332463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 374605483453292781351106469 70238528147492396503332463)
      ·
        refine ⟨105357792221238594754998695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70238528147492396503332463 105357792221238594754998695)
        ·
          refine ⟨158036688331857892132498043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105357792221238594754998695 158036688331857892132498043)
          ·
            refine ⟨237055032497786838198747065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158036688331857892132498043 237055032497786838198747065)
            ·
              refine ⟨177791274373340128649060299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237055032497786838198747065 177791274373340128649060299)
              ·
                refine ⟨266686911560010192973590449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177791274373340128649060299 266686911560010192973590449)
                ·
                  refine ⟨200015183670007644730192837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266686911560010192973590449 200015183670007644730192837)
                  ·
                    refine ⟨37502846938126433386911157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200015183670007644730192837 37502846938126433386911157)
                    ·
                      refine ⟨3515891900449353130022921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37502846938126433386911157 3515891900449353130022921)
                      ·
                        rfl

theorem cell23_6847175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_6847175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847175 prefixEnd_6847175 := by exact prefixLift 6847175
  have htrace : WordTrace (prefixWord ++ tailWord_6847175) baseStart_6847175 baseEnd_6847175 := by
    simpa [prefixWord, tailWord_6847175, baseEnd_6847175] using wordTrace_append hprefix tailTrace_6847175
  have hstable : (prefixWord ++ tailWord_6847175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847175).length < 2 ^ (prefixWord ++ tailWord_6847175).sum := by decide
  have hdescent : baseEnd_6847175 < baseStart_6847175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847212 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_6847212 : Nat := 118140960795 + 6847212 * 2 ^ 59
def prefixEnd_6847212 : Nat := 4983230072969 + 3 ^ 40 * 6847212 * 2
def baseEnd_6847212 : Nat := 1171970299744523161753417

theorem tailTrace_6847212 : CollatzResearch.WordTrace tailWord_6847212 prefixEnd_6847212 1171970299744523161753417 := by
  unfold tailWord_6847212
  simp only [CollatzResearch.WordTrace]
  refine ⟨124869169234863904776583945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166492225646485206368778593 124869169234863904776583945)
  ·
    refine ⟨93651876926147928582437959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124869169234863904776583945 93651876926147928582437959)
    ·
      refine ⟨140477815389221892873656939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93651876926147928582437959 140477815389221892873656939)
      ·
        refine ⟨210716723083832839310485409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140477815389221892873656939 210716723083832839310485409)
        ·
          refine ⟨158037542312874629482864057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210716723083832839310485409 158037542312874629482864057)
          ·
            refine ⟨118528156734655972112148043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158037542312874629482864057 118528156734655972112148043)
            ·
              refine ⟨177792235101983958168222065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118528156734655972112148043 177792235101983958168222065)
              ·
                refine ⟨133344176326487968626166549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177792235101983958168222065 133344176326487968626166549)
                ·
                  refine ⟨6250508265304123529351557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133344176326487968626166549 6250508265304123529351557)
                  ·
                    refine ⟨1171970299744523161753417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250508265304123529351557 1171970299744523161753417)
                    ·
                      rfl

theorem cell23_6847212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_6847212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847212 prefixEnd_6847212 := by exact prefixLift 6847212
  have htrace : WordTrace (prefixWord ++ tailWord_6847212) baseStart_6847212 baseEnd_6847212 := by
    simpa [prefixWord, tailWord_6847212, baseEnd_6847212] using wordTrace_append hprefix tailTrace_6847212
  have hstable : (prefixWord ++ tailWord_6847212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847212).length < 2 ^ (prefixWord ++ tailWord_6847212).sum := by decide
  have hdescent : baseEnd_6847212 < baseStart_6847212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847225 : List Nat := [1, 2, 1, 3, 1, 1, 1, 13]
def baseStart_6847225 : Nat := 118140960795 + 6847225 * 2 ^ 59
def prefixEnd_6847225 : Nat := 4983230072969 + 3 ^ 40 * 6847225 * 2
def baseEnd_6847225 : Nat := 130219169425262145718433

theorem tailTrace_6847225 : CollatzResearch.WordTrace tailWord_6847225 prefixEnd_6847225 130219169425262145718433 := by
  unfold tailWord_6847225
  simp only [CollatzResearch.WordTrace]
  refine ⟨249738812618680712773391129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166492541745787141848927419 249738812618680712773391129)
  ·
    refine ⟨187304109464010534580043347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249738812618680712773391129 187304109464010534580043347)
    ·
      refine ⟨280956164196015801870065021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187304109464010534580043347 280956164196015801870065021)
      ·
        refine ⟨105358561573505925701274383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280956164196015801870065021 105358561573505925701274383)
        ·
          refine ⟨158037842360258888551911575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105358561573505925701274383 158037842360258888551911575)
          ·
            refine ⟨237056763540388332827867363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158037842360258888551911575 237056763540388332827867363)
            ·
              refine ⟨355585145310582499241801045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237056763540388332827867363 355585145310582499241801045)
              ·
                refine ⟨130219169425262145718433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 355585145310582499241801045 130219169425262145718433)
                ·
                  rfl

theorem cell23_6847225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 13].length) (baseStart_6847225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847225 prefixEnd_6847225 := by exact prefixLift 6847225
  have htrace : WordTrace (prefixWord ++ tailWord_6847225) baseStart_6847225 baseEnd_6847225 := by
    simpa [prefixWord, tailWord_6847225, baseEnd_6847225] using wordTrace_append hprefix tailTrace_6847225
  have hstable : (prefixWord ++ tailWord_6847225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847225).length < 2 ^ (prefixWord ++ tailWord_6847225).sum := by decide
  have hdescent : baseEnd_6847225 < baseStart_6847225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847230 : List Nat := [4, 2, 2, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6847230 : Nat := 118140960795 + 6847230 * 2 ^ 59
def prefixEnd_6847230 : Nat := 4983230072969 + 3 ^ 40 * 6847230 * 2
def baseEnd_6847230 : Nat := 3515920141885350414835169

theorem tailTrace_6847230 : CollatzResearch.WordTrace tailWord_6847230 prefixEnd_6847230 3515920141885350414835169 := by
  unfold tailWord_6847230
  simp only [CollatzResearch.WordTrace]
  refine ⟨31217374372957824828415393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166492663322441732418215429 31217374372957824828415393)
  ·
    refine ⟨23413030779718368621311545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31217374372957824828415393 23413030779718368621311545)
    ·
      refine ⟨17559773084788776465983659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23413030779718368621311545 17559773084788776465983659)
      ·
        refine ⟨26339659627183164698975489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17559773084788776465983659 26339659627183164698975489)
        ·
          refine ⟨19754744720387373524231617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26339659627183164698975489 19754744720387373524231617)
          ·
            refine ⟨14816058540290530143173713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19754744720387373524231617 14816058540290530143173713)
            ·
              refine ⟨11112043905217897607380285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14816058540290530143173713 11112043905217897607380285)
              ·
                refine ⟨4167016464456711602767607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11112043905217897607380285 4167016464456711602767607)
                ·
                  refine ⟨6250524696685067404151411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167016464456711602767607 6250524696685067404151411)
                  ·
                    refine ⟨9375787045027601106227117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6250524696685067404151411 9375787045027601106227117)
                    ·
                      refine ⟨3515920141885350414835169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9375787045027601106227117 3515920141885350414835169)
                      ·
                        rfl

theorem cell23_6847230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6847230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847230 prefixEnd_6847230 := by exact prefixLift 6847230
  have htrace : WordTrace (prefixWord ++ tailWord_6847230) baseStart_6847230 baseEnd_6847230 := by
    simpa [prefixWord, tailWord_6847230, baseEnd_6847230] using wordTrace_append hprefix tailTrace_6847230
  have hstable : (prefixWord ++ tailWord_6847230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847230).length < 2 ^ (prefixWord ++ tailWord_6847230).sum := by decide
  have hdescent : baseEnd_6847230 < baseStart_6847230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847236 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_6847236 : Nat := 118140960795 + 6847236 * 2 ^ 59
def prefixEnd_6847236 : Nat := 4983230072969 + 3 ^ 40 * 6847236 * 2
def baseEnd_6847236 : Nat := 3515923222769277391360141

theorem tailTrace_6847236 : CollatzResearch.WordTrace tailWord_6847236 prefixEnd_6847236 3515923222769277391360141 := by
  unfold tailWord_6847236
  simp only [CollatzResearch.WordTrace]
  refine ⟨124869606910820430826020781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166492809214427241101361041 124869606910820430826020781)
  ·
    refine ⟨46826102591557661559757793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124869606910820430826020781 46826102591557661559757793)
    ·
      refine ⟨35119576943668246169818345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46826102591557661559757793 35119576943668246169818345)
      ·
        refine ⟨26339682707751184627363759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35119576943668246169818345 26339682707751184627363759)
        ·
          refine ⟨39509524061626776941045639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26339682707751184627363759 39509524061626776941045639)
          ·
            refine ⟨59264286092440165411568459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39509524061626776941045639 59264286092440165411568459)
            ·
              refine ⟨88896429138660248117352689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59264286092440165411568459 88896429138660248117352689)
              ·
                refine ⟨66672321853995186088014517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88896429138660248117352689 66672321853995186088014517)
                ·
                  refine ⟨6250530173812048695751361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66672321853995186088014517 6250530173812048695751361)
                  ·
                    refine ⟨4687897630359036521813521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6250530173812048695751361 4687897630359036521813521)
                    ·
                      refine ⟨3515923222769277391360141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687897630359036521813521 3515923222769277391360141)
                      ·
                        rfl

theorem cell23_6847236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_6847236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847236 prefixEnd_6847236 := by exact prefixLift 6847236
  have htrace : WordTrace (prefixWord ++ tailWord_6847236) baseStart_6847236 baseEnd_6847236 := by
    simpa [prefixWord, tailWord_6847236, baseEnd_6847236] using wordTrace_append hprefix tailTrace_6847236
  have hstable : (prefixWord ++ tailWord_6847236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847236).length < 2 ^ (prefixWord ++ tailWord_6847236).sum := by decide
  have hdescent : baseEnd_6847236 < baseStart_6847236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847253 : List Nat := [1, 3, 2, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_6847253 : Nat := 118140960795 + 6847253 * 2 ^ 59
def prefixEnd_6847253 : Nat := 4983230072969 + 3 ^ 40 * 6847253 * 2
def baseEnd_6847253 : Nat := 3515931951940403824847563

theorem tailTrace_6847253 : CollatzResearch.WordTrace tailWord_6847253 prefixEnd_6847253 3515931951940403824847563 := by
  unfold tailWord_6847253
  simp only [CollatzResearch.WordTrace]
  refine ⟨249739833862579273555410413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166493222575052849036940275 249739833862579273555410413)
  ·
    refine ⟨93652437698467227583278905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249739833862579273555410413 93652437698467227583278905)
    ·
      refine ⟨70239328273850420687459179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93652437698467227583278905 70239328273850420687459179)
      ·
        refine ⟨105358992410775631031188769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70239328273850420687459179 105358992410775631031188769)
        ·
          refine ⟨79019244308081723273391577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105358992410775631031188769 79019244308081723273391577)
          ·
            refine ⟨59264433231061292455043683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79019244308081723273391577 59264433231061292455043683)
            ·
              refine ⟨88896649846591938682565525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59264433231061292455043683 88896649846591938682565525)
              ·
                refine ⟨4167030461558997125745259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88896649846591938682565525 4167030461558997125745259)
                ·
                  refine ⟨6250545692338495688617889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167030461558997125745259 6250545692338495688617889)
                  ·
                    refine ⟨4687909269253871766463417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6250545692338495688617889 4687909269253871766463417)
                    ·
                      refine ⟨3515931951940403824847563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4687909269253871766463417 3515931951940403824847563)
                      ·
                        rfl

theorem cell23_6847253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_6847253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847253 prefixEnd_6847253 := by exact prefixLift 6847253
  have htrace : WordTrace (prefixWord ++ tailWord_6847253) baseStart_6847253 baseEnd_6847253 := by
    simpa [prefixWord, tailWord_6847253, baseEnd_6847253] using wordTrace_append hprefix tailTrace_6847253
  have hstable : (prefixWord ++ tailWord_6847253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847253).length < 2 ^ (prefixWord ++ tailWord_6847253).sum := by decide
  have hdescent : baseEnd_6847253 < baseStart_6847253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847266 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_6847266 : Nat := 118140960795 + 6847266 * 2 ^ 59
def prefixEnd_6847266 : Nat := 4983230072969 + 3 ^ 40 * 6847266 * 2
def baseEnd_6847266 : Nat := 3515938627188912273985003

theorem tailTrace_6847266 : CollatzResearch.WordTrace tailWord_6847266 prefixEnd_6847266 3515938627188912273985003 := by
  unfold tailWord_6847266
  simp only [CollatzResearch.WordTrace]
  refine ⟨62435077002883044193908413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166493538674354784517089101 62435077002883044193908413)
  ·
    refine ⟨23413153876081141572715655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62435077002883044193908413 23413153876081141572715655)
    ·
      refine ⟨35119730814121712359073483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23413153876081141572715655 35119730814121712359073483)
      ·
        refine ⟨52679596221182568538610225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35119730814121712359073483 52679596221182568538610225)
        ·
          refine ⟨39509697165886926403957669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52679596221182568538610225 39509697165886926403957669)
          ·
            refine ⟨7408068218603798700742063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39509697165886926403957669 7408068218603798700742063)
            ·
              refine ⟨11112102327905698051113095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7408068218603798700742063 11112102327905698051113095)
              ·
                refine ⟨16668153491858547076669643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11112102327905698051113095 16668153491858547076669643)
                ·
                  refine ⟨25002230237787820615004465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16668153491858547076669643 25002230237787820615004465)
                  ·
                    refine ⟨18751672678340865461253349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25002230237787820615004465 18751672678340865461253349)
                    ·
                      refine ⟨3515938627188912273985003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18751672678340865461253349 3515938627188912273985003)
                      ·
                        rfl

theorem cell23_6847266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_6847266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847266 prefixEnd_6847266 := by exact prefixLift 6847266
  have htrace : WordTrace (prefixWord ++ tailWord_6847266) baseStart_6847266 baseEnd_6847266 := by
    simpa [prefixWord, tailWord_6847266, baseEnd_6847266] using wordTrace_append hprefix tailTrace_6847266
  have hstable : (prefixWord ++ tailWord_6847266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847266).length < 2 ^ (prefixWord ++ tailWord_6847266).sum := by decide
  have hdescent : baseEnd_6847266 < baseStart_6847266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847282 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_6847282 : Nat := 118140960795 + 6847282 * 2 ^ 59
def prefixEnd_6847282 : Nat := 4983230072969 + 3 ^ 40 * 6847282 * 2
def baseEnd_6847282 : Nat := 3515946842879384211384929

theorem tailTrace_6847282 : CollatzResearch.WordTrace tailWord_6847282 prefixEnd_6847282 3515946842879384211384929 := by
  unfold tailWord_6847282
  simp only [CollatzResearch.WordTrace]
  refine ⟨62435222894868552877054025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166493927719649474338810733 62435222894868552877054025)
  ·
    refine ⟨46826417171151414657790519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62435222894868552877054025 46826417171151414657790519)
    ·
      refine ⟨70239625756727121986685779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46826417171151414657790519 70239625756727121986685779)
      ·
        refine ⟨105359438635090682980028669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70239625756727121986685779 105359438635090682980028669)
        ·
          refine ⟨39509789488159006117510751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105359438635090682980028669 39509789488159006117510751)
          ·
            refine ⟨59264684232238509176266127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39509789488159006117510751 59264684232238509176266127)
            ·
              refine ⟨88897026348357763764399191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59264684232238509176266127 88897026348357763764399191)
              ·
                refine ⟨133345539522536645646598787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88897026348357763764399191 133345539522536645646598787)
                ·
                  refine ⟨200018309283804968469898181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133345539522536645646598787 200018309283804968469898181)
                  ·
                    refine ⟨37503432990713431588105909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 200018309283804968469898181 37503432990713431588105909)
                    ·
                      refine ⟨3515946842879384211384929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37503432990713431588105909 3515946842879384211384929)
                      ·
                        rfl

theorem cell23_6847282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_6847282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847282 prefixEnd_6847282 := by exact prefixLift 6847282
  have htrace : WordTrace (prefixWord ++ tailWord_6847282) baseStart_6847282 baseEnd_6847282 := by
    simpa [prefixWord, tailWord_6847282, baseEnd_6847282] using wordTrace_append hprefix tailTrace_6847282
  have hstable : (prefixWord ++ tailWord_6847282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847282).length < 2 ^ (prefixWord ++ tailWord_6847282).sum := by decide
  have hdescent : baseEnd_6847282 < baseStart_6847282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847292 : List Nat := [2, 2, 2, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_6847292 : Nat := 118140960795 + 6847292 * 2 ^ 59
def prefixEnd_6847292 : Nat := 4983230072969 + 3 ^ 40 * 6847292 * 2
def baseEnd_6847292 : Nat := 3515951977685929172259883

theorem tailTrace_6847292 : CollatzResearch.WordTrace tailWord_6847292 prefixEnd_6847292 3515951977685929172259883 := by
  unfold tailWord_6847292
  simp only [CollatzResearch.WordTrace]
  refine ⟨124870628154718991608040065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166494170872958655477386753 124870628154718991608040065)
  ·
    refine ⟨93652971116039243706030049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124870628154718991608040065 93652971116039243706030049)
    ·
      refine ⟨70239728337029432779522537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93652971116039243706030049 70239728337029432779522537)
      ·
        refine ⟨52679796252772074584641903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70239728337029432779522537 52679796252772074584641903)
        ·
          refine ⟨79019694379158111876962855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52679796252772074584641903 79019694379158111876962855)
          ·
            refine ⟨118529541568737167815444283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79019694379158111876962855 118529541568737167815444283)
            ·
              refine ⟨177794312353105751723166425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118529541568737167815444283 177794312353105751723166425)
              ·
                refine ⟨133345734264829313792374819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177794312353105751723166425 133345734264829313792374819)
                ·
                  refine ⟨200018601397243970688562229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133345734264829313792374819 200018601397243970688562229)
                  ·
                    refine ⟨18751743880991622252052709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 200018601397243970688562229 18751743880991622252052709)
                    ·
                      refine ⟨3515951977685929172259883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18751743880991622252052709 3515951977685929172259883)
                      ·
                        rfl

theorem cell23_6847292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_6847292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847292 prefixEnd_6847292 := by exact prefixLift 6847292
  have htrace : WordTrace (prefixWord ++ tailWord_6847292) baseStart_6847292 baseEnd_6847292 := by
    simpa [prefixWord, tailWord_6847292, baseEnd_6847292] using wordTrace_append hprefix tailTrace_6847292
  have hstable : (prefixWord ++ tailWord_6847292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847292).length < 2 ^ (prefixWord ++ tailWord_6847292).sum := by decide
  have hdescent : baseEnd_6847292 < baseStart_6847292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847416 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 2, 4, 2]
def baseStart_6847416 : Nat := 118140960795 + 6847416 * 2 ^ 59
def prefixEnd_6847416 : Nat := 4983230072969 + 3 ^ 40 * 6847416 * 2
def baseEnd_6847416 : Nat := 3516015649287086687109313

theorem tailTrace_6847416 : CollatzResearch.WordTrace tailWord_6847416 prefixEnd_6847416 3516015649287086687109313 := by
  unfold tailWord_6847416
  simp only [CollatzResearch.WordTrace]
  refine ⟨124872889480494376196797051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166497185973992501595729401 124872889480494376196797051)
  ·
    refine ⟨187309334220741564295195577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124872889480494376196797051 187309334220741564295195577)
    ·
      refine ⟨140482000665556173221396683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187309334220741564295195577 140482000665556173221396683)
      ·
        refine ⟨210723000998334259832095025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140482000665556173221396683 210723000998334259832095025)
        ·
          refine ⟨158042250748750694874071269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210723000998334259832095025 158042250748750694874071269)
          ·
            refine ⟨29632922015390755288888363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158042250748750694874071269 29632922015390755288888363)
            ·
              refine ⟨44449383023086132933332545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29632922015390755288888363 44449383023086132933332545)
              ·
                refine ⟨33337037267314599699999409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44449383023086132933332545 33337037267314599699999409)
                ·
                  refine ⟨25002777950485949774999557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33337037267314599699999409 25002777950485949774999557)
                  ·
                    refine ⟨4688020865716115582812417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25002777950485949774999557 4688020865716115582812417)
                    ·
                      refine ⟨3516015649287086687109313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4688020865716115582812417 3516015649287086687109313)
                      ·
                        rfl

theorem cell23_6847416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_6847416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847416 prefixEnd_6847416 := by exact prefixLift 6847416
  have htrace : WordTrace (prefixWord ++ tailWord_6847416) baseStart_6847416 baseEnd_6847416 := by
    simpa [prefixWord, tailWord_6847416, baseEnd_6847416] using wordTrace_append hprefix tailTrace_6847416
  have hstable : (prefixWord ++ tailWord_6847416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847416).length < 2 ^ (prefixWord ++ tailWord_6847416).sum := by decide
  have hdescent : baseEnd_6847416 < baseStart_6847416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6847477 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6847477 : Nat := 118140960795 + 6847477 * 2 ^ 59
def prefixEnd_6847477 : Nat := 4983230072969 + 3 ^ 40 * 6847477 * 2
def baseEnd_6847477 : Nat := 1172015657202336982815511

theorem tailTrace_6847477 : CollatzResearch.WordTrace tailWord_6847477 prefixEnd_6847477 1172015657202336982815511 := by
  unfold tailWord_6847477
  simp only [CollatzResearch.WordTrace]
  refine ⟨249748003813767759811564685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166498669209178506541043123 249748003813767759811564685)
  ·
    refine ⟨93655501430162909929336757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249748003813767759811564685 93655501430162909929336757)
    ·
      refine ⟨8780203259077772805875321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93655501430162909929336757 8780203259077772805875321)
      ·
        refine ⟨6585152444308329604406491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8780203259077772805875321 6585152444308329604406491)
        ·
          refine ⟨9877728666462494406609737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585152444308329604406491 9877728666462494406609737)
          ·
            refine ⟨7408296499846870804957303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9877728666462494406609737 7408296499846870804957303)
            ·
              refine ⟨11112444749770306207435955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7408296499846870804957303 11112444749770306207435955)
              ·
                refine ⟨16668667124655459311153933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11112444749770306207435955 16668667124655459311153933)
                ·
                  refine ⟨6250750171745797241682725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16668667124655459311153933 6250750171745797241682725)
                  ·
                    refine ⟨1172015657202336982815511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250750171745797241682725 1172015657202336982815511)
                    ·
                      rfl

theorem cell23_6847477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6847477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6847477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6847477 prefixEnd_6847477 := by exact prefixLift 6847477
  have htrace : WordTrace (prefixWord ++ tailWord_6847477) baseStart_6847477 baseEnd_6847477 := by
    simpa [prefixWord, tailWord_6847477, baseEnd_6847477] using wordTrace_append hprefix tailTrace_6847477
  have hstable : (prefixWord ++ tailWord_6847477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6847477).length < 2 ^ (prefixWord ++ tailWord_6847477).sum := by decide
  have hdescent : baseEnd_6847477 < baseStart_6847477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6847477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
