import V185TrunkScan20Chunk093

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_571363 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 6]
def baseStart_571363 : Nat := 118140960795 + 571363 * 2 ^ 59
def prefixEnd_571363 : Nat := 4983230072969 + 3 ^ 40 * 571363 * 2
def baseEnd_571363 : Nat := 260785641951069576297649

theorem tailTrace_571363 : CollatzResearch.WordTrace tailWord_571363 prefixEnd_571363 260785641951069576297649 := by
  unfold tailWord_571363
  simp only [CollatzResearch.WordTrace]
  refine ⟨20839320629056906876686743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13892880419371271251124495 20839320629056906876686743)
  ·
    refine ⟨31258980943585360315030115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20839320629056906876686743 31258980943585360315030115)
    ·
      refine ⟨46888471415378040472545173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31258980943585360315030115 46888471415378040472545173)
      ·
        refine ⟨2197897097595845647150555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46888471415378040472545173 2197897097595845647150555)
        ·
          refine ⟨3296845646393768470725833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197897097595845647150555 3296845646393768470725833)
          ·
            refine ⟨2472634234795326353044375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3296845646393768470725833 2472634234795326353044375)
            ·
              refine ⟨3708951352192989529566563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472634234795326353044375 3708951352192989529566563)
              ·
                refine ⟨5563427028289484294349845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708951352192989529566563 5563427028289484294349845)
                ·
                  refine ⟨260785641951069576297649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5563427028289484294349845 260785641951069576297649)
                  ·
                    rfl

theorem cell20_571363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_571363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571363 prefixEnd_571363 := by exact prefixLift 571363
  have htrace : WordTrace (prefixWord ++ tailWord_571363) baseStart_571363 baseEnd_571363 := by
    simpa [prefixWord, tailWord_571363, baseEnd_571363] using wordTrace_append hprefix tailTrace_571363
  have hstable : (prefixWord ++ tailWord_571363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571363).length < 2 ^ (prefixWord ++ tailWord_571363).sum := by decide
  have hdescent : baseEnd_571363 < baseStart_571363 := by decide
  rcases family_descends (prefixWord ++ tailWord_571363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571390 : List Nat := [4, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_571390 : Nat := 118140960795 + 571390 * 2 ^ 59
def prefixEnd_571390 : Nat := 4983230072969 + 3 ^ 40 * 571390 * 2
def baseEnd_571390 : Nat := 260797965486777482397539

theorem tailTrace_571390 : CollatzResearch.WordTrace tailWord_571390 prefixEnd_571390 260797965486777482397539 := by
  unfold tailWord_571390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605038174994886310989953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13893536933306060325279749 2605038174994886310989953)
  ·
    refine ⟨1953778631246164733242465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2605038174994886310989953 1953778631246164733242465)
    ·
      refine ⟨1465333973434623549931849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1953778631246164733242465 1465333973434623549931849)
      ·
        refine ⟨1099000480075967662448887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1465333973434623549931849 1099000480075967662448887)
        ·
          refine ⟨1648500720113951493673331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099000480075967662448887 1648500720113951493673331)
          ·
            refine ⟨2472751080170927240509997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648500720113951493673331 2472751080170927240509997)
            ·
              refine ⟨927281655064097715191249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2472751080170927240509997 927281655064097715191249)
              ·
                refine ⟨695461241298073286393437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927281655064097715191249 695461241298073286393437)
                ·
                  refine ⟨260797965486777482397539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695461241298073286393437 260797965486777482397539)
                  ·
                    rfl

theorem cell20_571390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_571390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571390 prefixEnd_571390 := by exact prefixLift 571390
  have htrace : WordTrace (prefixWord ++ tailWord_571390) baseStart_571390 baseEnd_571390 := by
    simpa [prefixWord, tailWord_571390, baseEnd_571390] using wordTrace_append hprefix tailTrace_571390
  have hstable : (prefixWord ++ tailWord_571390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571390).length < 2 ^ (prefixWord ++ tailWord_571390).sum := by decide
  have hdescent : baseEnd_571390 < baseStart_571390 := by decide
  rcases family_descends (prefixWord ++ tailWord_571390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571425 : List Nat := [1, 2, 3, 2, 4, 1, 1, 6]
def baseStart_571425 : Nat := 118140960795 + 571425 * 2 ^ 59
def prefixEnd_571425 : Nat := 4983230072969 + 3 ^ 40 * 571425 * 2
def baseEnd_571425 : Nat := 86937980146824305410243

theorem tailTrace_571425 : CollatzResearch.WordTrace tailWord_571425 prefixEnd_571425 86937980146824305410243 := by
  unfold tailWord_571425
  simp only [CollatzResearch.WordTrace]
  refine ⟨20841581954832291465443729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13894387969888194310295819 20841581954832291465443729)
  ·
    refine ⟨15631186466124218599082797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20841581954832291465443729 15631186466124218599082797)
    ·
      refine ⟨5861694924796581974656049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15631186466124218599082797 5861694924796581974656049)
      ·
        refine ⟨4396271193597436480992037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5861694924796581974656049 4396271193597436480992037)
        ·
          refine ⟨824300848799519340186007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4396271193597436480992037 824300848799519340186007)
          ·
            refine ⟨1236451273199279010279011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824300848799519340186007 1236451273199279010279011)
            ·
              refine ⟨1854676909798918515418517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236451273199279010279011 1854676909798918515418517)
              ·
                refine ⟨86937980146824305410243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1854676909798918515418517 86937980146824305410243)
                ·
                  rfl

theorem cell20_571425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_571425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571425 prefixEnd_571425 := by exact prefixLift 571425
  have htrace : WordTrace (prefixWord ++ tailWord_571425) baseStart_571425 baseEnd_571425 := by
    simpa [prefixWord, tailWord_571425, baseEnd_571425] using wordTrace_append hprefix tailTrace_571425
  have hstable : (prefixWord ++ tailWord_571425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571425).length < 2 ^ (prefixWord ++ tailWord_571425).sum := by decide
  have hdescent : baseEnd_571425 < baseStart_571425 := by decide
  rcases family_descends (prefixWord ++ tailWord_571425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571431 : List Nat := [1, 1, 7, 1, 2, 2, 1, 3, 2]
def baseStart_571431 : Nat := 118140960795 + 571431 * 2 ^ 59
def prefixEnd_571431 : Nat := 4983230072969 + 3 ^ 40 * 571431 * 2
def baseEnd_571431 : Nat := 260816679003963562030705

theorem tailTrace_571431 : CollatzResearch.WordTrace tailWord_571431 prefixEnd_571431 260816679003963562030705 := by
  unfold tailWord_571431
  simp only [CollatzResearch.WordTrace]
  refine ⟨20841800792810554490162147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13894533861873702993441431 20841800792810554490162147)
  ·
    refine ⟨31262701189215831735243221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20841800792810554490162147 31262701189215831735243221)
    ·
      refine ⟨732719559122246056294763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31262701189215831735243221 732719559122246056294763)
      ·
        refine ⟨1099079338683369084442145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 732719559122246056294763 1099079338683369084442145)
        ·
          refine ⟨824309504012526813331609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099079338683369084442145 824309504012526813331609)
          ·
            refine ⟨618232128009395109998707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 824309504012526813331609 618232128009395109998707)
            ·
              refine ⟨927348192014092664998061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618232128009395109998707 927348192014092664998061)
              ·
                refine ⟨347755572005284749374273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 927348192014092664998061 347755572005284749374273)
                ·
                  refine ⟨260816679003963562030705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347755572005284749374273 260816679003963562030705)
                  ·
                    rfl

theorem cell20_571431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 3, 2].length) (baseStart_571431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571431 prefixEnd_571431 := by exact prefixLift 571431
  have htrace : WordTrace (prefixWord ++ tailWord_571431) baseStart_571431 baseEnd_571431 := by
    simpa [prefixWord, tailWord_571431, baseEnd_571431] using wordTrace_append hprefix tailTrace_571431
  have hstable : (prefixWord ++ tailWord_571431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571431).length < 2 ^ (prefixWord ++ tailWord_571431).sum := by decide
  have hdescent : baseEnd_571431 < baseStart_571431 := by decide
  rcases family_descends (prefixWord ++ tailWord_571431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571456 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 4]
def baseStart_571456 : Nat := 118140960795 + 571456 * 2 ^ 59
def prefixEnd_571456 : Nat := 4983230072969 + 3 ^ 40 * 571456 * 2
def baseEnd_571456 : Nat := 260828089685174586197269

theorem tailTrace_571456 : CollatzResearch.WordTrace tailWord_571456 prefixEnd_571456 260828089685174586197269 := by
  unfold tailWord_571456
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421356308859991879911111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13895141745146655839881481 10421356308859991879911111)
  ·
    refine ⟨15632034463289987819866667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10421356308859991879911111 15632034463289987819866667)
    ·
      refine ⟨23448051694934981729800001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15632034463289987819866667 23448051694934981729800001)
      ·
        refine ⟨17586038771201236297350001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23448051694934981729800001 17586038771201236297350001)
        ·
          refine ⟨13189529078400927223012501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17586038771201236297350001 13189529078400927223012501)
          ·
            refine ⟨618259175550043463578711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13189529078400927223012501 618259175550043463578711)
            ·
              refine ⟨927388763325065195368067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618259175550043463578711 927388763325065195368067)
              ·
                refine ⟨1391083144987597793052101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927388763325065195368067 1391083144987597793052101)
                ·
                  refine ⟨260828089685174586197269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391083144987597793052101 260828089685174586197269)
                  ·
                    rfl

theorem cell20_571456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 4].length) (baseStart_571456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571456 prefixEnd_571456 := by exact prefixLift 571456
  have htrace : WordTrace (prefixWord ++ tailWord_571456) baseStart_571456 baseEnd_571456 := by
    simpa [prefixWord, tailWord_571456, baseEnd_571456] using wordTrace_append hprefix tailTrace_571456
  have hstable : (prefixWord ++ tailWord_571456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571456).length < 2 ^ (prefixWord ++ tailWord_571456).sum := by decide
  have hdescent : baseEnd_571456 < baseStart_571456 := by decide
  rcases family_descends (prefixWord ++ tailWord_571456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571491 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 7]
def baseStart_571491 : Nat := 118140960795 + 571491 * 2 ^ 59
def prefixEnd_571491 : Nat := 4983230072969 + 3 ^ 40 * 571491 * 2
def baseEnd_571491 : Nat := 260844064638870020030459

theorem tailTrace_571491 : CollatzResearch.WordTrace tailWord_571491 prefixEnd_571491 260844064638870020030459 := by
  unfold tailWord_571491
  simp only [CollatzResearch.WordTrace]
  refine ⟨20843989172593184737346327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13895992781728789824897551 20843989172593184737346327)
  ·
    refine ⟨31265983758889777106019491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20843989172593184737346327 31265983758889777106019491)
    ·
      refine ⟨46898975638334665659029237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31265983758889777106019491 46898975638334665659029237)
      ·
        refine ⟨4396778966093874905533991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46898975638334665659029237 4396778966093874905533991)
        ·
          refine ⟨6595168449140812358300987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4396778966093874905533991 6595168449140812358300987)
          ·
            refine ⟨9892752673711218537451481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6595168449140812358300987 9892752673711218537451481)
            ·
              refine ⟨7419564505283413903088611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9892752673711218537451481 7419564505283413903088611)
              ·
                refine ⟨11129346757925120854632917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7419564505283413903088611 11129346757925120854632917)
                ·
                  refine ⟨260844064638870020030459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11129346757925120854632917 260844064638870020030459)
                  ·
                    rfl

theorem cell20_571491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_571491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571491 prefixEnd_571491 := by exact prefixLift 571491
  have htrace : WordTrace (prefixWord ++ tailWord_571491) baseStart_571491 baseEnd_571491 := by
    simpa [prefixWord, tailWord_571491, baseEnd_571491] using wordTrace_append hprefix tailTrace_571491
  have hstable : (prefixWord ++ tailWord_571491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571491).length < 2 ^ (prefixWord ++ tailWord_571491).sum := by decide
  have hdescent : baseEnd_571491 < baseStart_571491 := by decide
  rcases family_descends (prefixWord ++ tailWord_571491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571511 : List Nat := [1, 1, 3, 1, 1, 5, 4, 2, 2]
def baseStart_571511 : Nat := 118140960795 + 571511 * 2 ^ 59
def prefixEnd_571511 : Nat := 4983230072969 + 3 ^ 40 * 571511 * 2
def baseEnd_571511 : Nat := 260853193183838839363711

theorem tailTrace_571511 : CollatzResearch.WordTrace tailWord_571511 prefixEnd_571511 260853193183838839363711 := by
  unfold tailWord_571511
  simp only [CollatzResearch.WordTrace]
  refine ⟨20844718632520728153074387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13896479088347152102049591 20844718632520728153074387)
  ·
    refine ⟨31267077948781092229611581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20844718632520728153074387 31267077948781092229611581)
    ·
      refine ⟨11725154230792909586104343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31267077948781092229611581 11725154230792909586104343)
      ·
        refine ⟨17587731346189364379156515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11725154230792909586104343 17587731346189364379156515)
        ·
          refine ⟨26381597019284046568734773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17587731346189364379156515 26381597019284046568734773)
          ·
            refine ⟨2473274720557879365818885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26381597019284046568734773 2473274720557879365818885)
            ·
              refine ⟨463739010104602381091041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2473274720557879365818885 463739010104602381091041)
              ·
                refine ⟨347804257578451785818281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463739010104602381091041 347804257578451785818281)
                ·
                  refine ⟨260853193183838839363711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347804257578451785818281 260853193183838839363711)
                  ·
                    rfl

theorem cell20_571511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 2, 2].length) (baseStart_571511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571511 prefixEnd_571511 := by exact prefixLift 571511
  have htrace : WordTrace (prefixWord ++ tailWord_571511) baseStart_571511 baseEnd_571511 := by
    simpa [prefixWord, tailWord_571511, baseEnd_571511] using wordTrace_append hprefix tailTrace_571511
  have hstable : (prefixWord ++ tailWord_571511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571511).length < 2 ^ (prefixWord ++ tailWord_571511).sum := by decide
  have hdescent : baseEnd_571511 < baseStart_571511 := by decide
  rcases family_descends (prefixWord ++ tailWord_571511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571549 : List Nat := [1, 4, 2, 1, 1, 4, 2, 3, 2]
def baseStart_571549 : Nat := 118140960795 + 571549 * 2 ^ 59
def prefixEnd_571549 : Nat := 4983230072969 + 3 ^ 40 * 571549 * 2
def baseEnd_571549 : Nat := 260870537419279596096889

theorem tailTrace_571549 : CollatzResearch.WordTrace tailWord_571549 prefixEnd_571549 260870537419279596096889 := by
  unfold tailWord_571549
  simp only [CollatzResearch.WordTrace]
  refine ⟨20846104606383060642957701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13897403070922040428638467 20846104606383060642957701)
  ·
    refine ⟨3908644613696823870554569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20846104606383060642957701 3908644613696823870554569)
    ·
      refine ⟨2931483460272617902915927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3908644613696823870554569 2931483460272617902915927)
      ·
        refine ⟨4397225190408926854373891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931483460272617902915927 4397225190408926854373891)
        ·
          refine ⟨6595837785613390281560837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397225190408926854373891 6595837785613390281560837)
          ·
            refine ⟨1236719584802510677792657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6595837785613390281560837 1236719584802510677792657)
            ·
              refine ⟨927539688601883008344493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236719584802510677792657 927539688601883008344493)
              ·
                refine ⟨347827383225706128129185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 927539688601883008344493 347827383225706128129185)
                ·
                  refine ⟨260870537419279596096889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347827383225706128129185 260870537419279596096889)
                  ·
                    rfl

theorem cell20_571549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_571549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571549 prefixEnd_571549 := by exact prefixLift 571549
  have htrace : WordTrace (prefixWord ++ tailWord_571549) baseStart_571549 baseEnd_571549 := by
    simpa [prefixWord, tailWord_571549, baseEnd_571549] using wordTrace_append hprefix tailTrace_571549
  have hstable : (prefixWord ++ tailWord_571549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571549).length < 2 ^ (prefixWord ++ tailWord_571549).sum := by decide
  have hdescent : baseEnd_571549 < baseStart_571549 := by decide
  rcases family_descends (prefixWord ++ tailWord_571549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571559 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 3]
def baseStart_571559 : Nat := 118140960795 + 571559 * 2 ^ 59
def prefixEnd_571559 : Nat := 4983230072969 + 3 ^ 40 * 571559 * 2
def baseEnd_571559 : Nat := 260875101691764005763515

theorem tailTrace_571559 : CollatzResearch.WordTrace tailWord_571559 prefixEnd_571559 260875101691764005763515 := by
  unfold tailWord_571559
  simp only [CollatzResearch.WordTrace]
  refine ⟨20846469336346832350821731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13897646224231221567214487 20846469336346832350821731)
  ·
    refine ⟨31269704004520248526232597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20846469336346832350821731 31269704004520248526232597)
    ·
      refine ⟨1465767375211886649667153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31269704004520248526232597 1465767375211886649667153)
      ·
        refine ⟨1099325531408914987250365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1465767375211886649667153 1099325531408914987250365)
        ·
          refine ⟨412247074278343120218887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1099325531408914987250365 412247074278343120218887)
          ·
            refine ⟨618370611417514680328331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412247074278343120218887 618370611417514680328331)
            ·
              refine ⟨927555917126272020492497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618370611417514680328331 927555917126272020492497)
              ·
                refine ⟨695666937844704015369373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927555917126272020492497 695666937844704015369373)
                ·
                  refine ⟨260875101691764005763515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695666937844704015369373 260875101691764005763515)
                  ·
                    rfl

theorem cell20_571559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 3].length) (baseStart_571559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571559 prefixEnd_571559 := by exact prefixLift 571559
  have htrace : WordTrace (prefixWord ++ tailWord_571559) baseStart_571559 baseEnd_571559 := by
    simpa [prefixWord, tailWord_571559, baseEnd_571559] using wordTrace_append hprefix tailTrace_571559
  have hstable : (prefixWord ++ tailWord_571559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571559).length < 2 ^ (prefixWord ++ tailWord_571559).sum := by decide
  have hdescent : baseEnd_571559 < baseStart_571559 := by decide
  rcases family_descends (prefixWord ++ tailWord_571559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571566 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_571566 : Nat := 118140960795 + 571566 * 2 ^ 59
def prefixEnd_571566 : Nat := 4983230072969 + 3 ^ 40 * 571566 * 2
def baseEnd_571566 : Nat := 260878296682503092530153

theorem tailTrace_571566 : CollatzResearch.WordTrace tailWord_571566 prefixEnd_571566 260878296682503092530153 := by
  unfold tailWord_571566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2605840580915184068290819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13897816431547648364217701 2605840580915184068290819)
  ·
    refine ⟨3908760871372776102436229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2605840580915184068290819 3908760871372776102436229)
    ·
      refine ⟨732892663382395519206793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3908760871372776102436229 732892663382395519206793)
      ·
        refine ⟨549669497536796639405095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 732892663382395519206793 549669497536796639405095)
        ·
          refine ⟨824504246305194959107643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549669497536796639405095 824504246305194959107643)
          ·
            refine ⟨1236756369457792438661465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824504246305194959107643 1236756369457792438661465)
            ·
              refine ⟨927567277093344328996099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236756369457792438661465 927567277093344328996099)
              ·
                refine ⟨1391350915640016493494149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927567277093344328996099 1391350915640016493494149)
                ·
                  refine ⟨260878296682503092530153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391350915640016493494149 260878296682503092530153)
                  ·
                    rfl

theorem cell20_571566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_571566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571566 prefixEnd_571566 := by exact prefixLift 571566
  have htrace : WordTrace (prefixWord ++ tailWord_571566) baseStart_571566 baseEnd_571566 := by
    simpa [prefixWord, tailWord_571566, baseEnd_571566] using wordTrace_append hprefix tailTrace_571566
  have hstable : (prefixWord ++ tailWord_571566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571566).length < 2 ^ (prefixWord ++ tailWord_571566).sum := by decide
  have hdescent : baseEnd_571566 < baseStart_571566 := by decide
  rcases family_descends (prefixWord ++ tailWord_571566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571570 : List Nat := [3, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_571570 : Nat := 118140960795 + 571570 * 2 ^ 59
def prefixEnd_571570 : Nat := 4983230072969 + 3 ^ 40 * 571570 * 2
def baseEnd_571570 : Nat := 260880122391496856396803

theorem tailTrace_571570 : CollatzResearch.WordTrace tailWord_571570 prefixEnd_571570 260880122391496856396803 := by
  unfold tailWord_571570
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211717634826745307368041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13897913692871320819648109 5211717634826745307368041)
  ·
    refine ⟨3908788226120058980526031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5211717634826745307368041 3908788226120058980526031)
    ·
      refine ⟨5863182339180088470789047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3908788226120058980526031 5863182339180088470789047)
      ·
        refine ⟨8794773508770132706183571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5863182339180088470789047 8794773508770132706183571)
        ·
          refine ⟨13192160263155199059275357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8794773508770132706183571 13192160263155199059275357)
          ·
            refine ⟨4947060098683199647228259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13192160263155199059275357 4947060098683199647228259)
            ·
              refine ⟨7420590148024799470842389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947060098683199647228259 7420590148024799470842389)
              ·
                refine ⟨347840163188662475195737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7420590148024799470842389 347840163188662475195737)
                ·
                  refine ⟨260880122391496856396803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347840163188662475195737 260880122391496856396803)
                  ·
                    rfl

theorem cell20_571570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_571570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571570 prefixEnd_571570 := by exact prefixLift 571570
  have htrace : WordTrace (prefixWord ++ tailWord_571570) baseStart_571570 baseEnd_571570 := by
    simpa [prefixWord, tailWord_571570, baseEnd_571570] using wordTrace_append hprefix tailTrace_571570
  have hstable : (prefixWord ++ tailWord_571570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571570).length < 2 ^ (prefixWord ++ tailWord_571570).sum := by decide
  have hdescent : baseEnd_571570 < baseStart_571570 := by decide
  rcases family_descends (prefixWord ++ tailWord_571570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571580 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 3]
def baseStart_571580 : Nat := 118140960795 + 571580 * 2 ^ 59
def prefixEnd_571580 : Nat := 4983230072969 + 3 ^ 40 * 571580 * 2
def baseEnd_571580 : Nat := 260884686663981266063429

theorem tailTrace_571580 : CollatzResearch.WordTrace tailWord_571580 prefixEnd_571580 260884686663981266063429 := by
  unfold tailWord_571580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10423617634635376468668097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13898156846180501958224129 10423617634635376468668097)
  ·
    refine ⟨7817713225976532351501073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10423617634635376468668097 7817713225976532351501073)
    ·
      refine ⟨5863284919482399263625805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7817713225976532351501073 5863284919482399263625805)
      ·
        refine ⟨2198731844805899723859677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5863284919482399263625805 2198731844805899723859677)
        ·
          refine ⟨824524441802212396447379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2198731844805899723859677 824524441802212396447379)
          ·
            refine ⟨1236786662703318594671069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824524441802212396447379 1236786662703318594671069)
            ·
              refine ⟨463794998513744473001651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1236786662703318594671069 463794998513744473001651)
              ·
                refine ⟨695692497770616709502477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 463794998513744473001651 695692497770616709502477)
                ·
                  refine ⟨260884686663981266063429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 695692497770616709502477 260884686663981266063429)
                  ·
                    rfl

theorem cell20_571580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_571580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571580 prefixEnd_571580 := by exact prefixLift 571580
  have htrace : WordTrace (prefixWord ++ tailWord_571580) baseStart_571580 baseEnd_571580 := by
    simpa [prefixWord, tailWord_571580, baseEnd_571580] using wordTrace_append hprefix tailTrace_571580
  have hstable : (prefixWord ++ tailWord_571580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571580).length < 2 ^ (prefixWord ++ tailWord_571580).sum := by decide
  have hdescent : baseEnd_571580 < baseStart_571580 := by decide
  rcases family_descends (prefixWord ++ tailWord_571580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571674 : List Nat := [3, 1, 1, 3, 4, 8]
def baseStart_571674 : Nat := 118140960795 + 571674 * 2 ^ 59
def prefixEnd_571674 : Nat := 4983230072969 + 3 ^ 40 * 571674 * 2
def baseEnd_571674 : Nat := 9663984845382767293693

theorem tailTrace_571674 : CollatzResearch.WordTrace tailWord_571674 prefixEnd_571674 9663984845382767293693 := by
  unfold tailWord_571674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212665932732551747814519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13900442487286804660838717 5212665932732551747814519)
  ·
    refine ⟨7818998899098827621721779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5212665932732551747814519 7818998899098827621721779)
    ·
      refine ⟨11728498348648241432582669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818998899098827621721779 11728498348648241432582669)
      ·
        refine ⟨4398186880743090537218501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11728498348648241432582669 4398186880743090537218501)
        ·
          refine ⟨824660040139329475728469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4398186880743090537218501 824660040139329475728469)
          ·
            refine ⟨9663984845382767293693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 824660040139329475728469 9663984845382767293693)
            ·
              rfl

theorem cell20_571674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 8].length) (baseStart_571674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571674 prefixEnd_571674 := by exact prefixLift 571674
  have htrace : WordTrace (prefixWord ++ tailWord_571674) baseStart_571674 baseEnd_571674 := by
    simpa [prefixWord, tailWord_571674, baseEnd_571674] using wordTrace_append hprefix tailTrace_571674
  have hstable : (prefixWord ++ tailWord_571674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571674).length < 2 ^ (prefixWord ++ tailWord_571674).sum := by decide
  have hdescent : baseEnd_571674 < baseStart_571674 := by decide
  rcases family_descends (prefixWord ++ tailWord_571674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571680 : List Nat := [2, 1, 1, 5, 2, 3, 2, 2, 2]
def baseStart_571680 : Nat := 118140960795 + 571680 * 2 ^ 59
def prefixEnd_571680 : Nat := 4983230072969 + 3 ^ 40 * 571680 * 2
def baseEnd_571680 : Nat := 260930329388825362729687

theorem tailTrace_571680 : CollatzResearch.WordTrace tailWord_571680 prefixEnd_571680 260930329388825362729687 := by
  unfold tailWord_571680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10425441284454235007988247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13900588379272313343984329 10425441284454235007988247)
  ·
    refine ⟨15638161926681352511982371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10425441284454235007988247 15638161926681352511982371)
    ·
      refine ⟨23457242890022028767973557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15638161926681352511982371 23457242890022028767973557)
      ·
        refine ⟨2199116520939565196997521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23457242890022028767973557 2199116520939565196997521)
        ·
          refine ⟨1649337390704673897748141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2199116520939565196997521 1649337390704673897748141)
          ·
            refine ⟨618501521514252711655553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1649337390704673897748141 618501521514252711655553)
            ·
              refine ⟨463876141135689533741665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618501521514252711655553 463876141135689533741665)
              ·
                refine ⟨347907105851767150306249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 463876141135689533741665 347907105851767150306249)
                ·
                  refine ⟨260930329388825362729687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347907105851767150306249 260930329388825362729687)
                  ·
                    rfl

theorem cell20_571680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 2, 2].length) (baseStart_571680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571680 prefixEnd_571680 := by exact prefixLift 571680
  have htrace : WordTrace (prefixWord ++ tailWord_571680) baseStart_571680 baseEnd_571680 := by
    simpa [prefixWord, tailWord_571680, baseEnd_571680] using wordTrace_append hprefix tailTrace_571680
  have hstable : (prefixWord ++ tailWord_571680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571680).length < 2 ^ (prefixWord ++ tailWord_571680).sum := by decide
  have hdescent : baseEnd_571680 < baseStart_571680 := by decide
  rcases family_descends (prefixWord ++ tailWord_571680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571681 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 5]
def baseStart_571681 : Nat := 118140960795 + 571681 * 2 ^ 59
def prefixEnd_571681 : Nat := 4983230072969 + 3 ^ 40 * 571681 * 2
def baseEnd_571681 : Nat := 260930785816073803696349

theorem tailTrace_571681 : CollatzResearch.WordTrace tailWord_571681 prefixEnd_571681 260930785816073803696349 := by
  unfold tailWord_571681
  simp only [CollatzResearch.WordTrace]
  refine ⟨20850919041904847186762897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13900612694603231457841931 20850919041904847186762897)
  ·
    refine ⟨15638189281428635390072173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20850919041904847186762897 15638189281428635390072173)
    ·
      refine ⟨5864320980535738271277065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15638189281428635390072173 5864320980535738271277065)
      ·
        refine ⟨4398240735401803703457799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5864320980535738271277065 4398240735401803703457799)
        ·
          refine ⟨6597361103102705555186699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398240735401803703457799 6597361103102705555186699)
          ·
            refine ⟨9896041654654058332780049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6597361103102705555186699 9896041654654058332780049)
            ·
              refine ⟨7422031240990543749585037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9896041654654058332780049 7422031240990543749585037)
              ·
                refine ⟨2783261715371453906094389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7422031240990543749585037 2783261715371453906094389)
                ·
                  refine ⟨260930785816073803696349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2783261715371453906094389 260930785816073803696349)
                  ·
                    rfl

theorem cell20_571681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_571681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571681 prefixEnd_571681 := by exact prefixLift 571681
  have htrace : WordTrace (prefixWord ++ tailWord_571681) baseStart_571681 baseEnd_571681 := by
    simpa [prefixWord, tailWord_571681, baseEnd_571681] using wordTrace_append hprefix tailTrace_571681
  have hstable : (prefixWord ++ tailWord_571681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571681).length < 2 ^ (prefixWord ++ tailWord_571681).sum := by decide
  have hdescent : baseEnd_571681 < baseStart_571681 := by decide
  rcases family_descends (prefixWord ++ tailWord_571681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571705 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 6]
def baseStart_571705 : Nat := 118140960795 + 571705 * 2 ^ 59
def prefixEnd_571705 : Nat := 4983230072969 + 3 ^ 40 * 571705 * 2
def baseEnd_571705 : Nat := 260941740070036386896251

theorem tailTrace_571705 : CollatzResearch.WordTrace tailWord_571705 prefixEnd_571705 260941740070036386896251 := by
  unfold tailWord_571705
  simp only [CollatzResearch.WordTrace]
  refine ⟨20851794393817899285636569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13901196262545266190424379 20851794393817899285636569)
  ·
    refine ⟨15638845795363424464227427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20851794393817899285636569 15638845795363424464227427)
    ·
      refine ⟨23458268693045136696341141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15638845795363424464227427 23458268693045136696341141)
      ·
        refine ⟨1099606344986490782640991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23458268693045136696341141 1099606344986490782640991)
        ·
          refine ⟨1649409517479736173961487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099606344986490782640991 1649409517479736173961487)
          ·
            refine ⟨2474114276219604260942231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649409517479736173961487 2474114276219604260942231)
            ·
              refine ⟨3711171414329406391413347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474114276219604260942231 3711171414329406391413347)
              ·
                refine ⟨5566757121494109587120021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3711171414329406391413347 5566757121494109587120021)
                ·
                  refine ⟨260941740070036386896251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5566757121494109587120021 260941740070036386896251)
                  ·
                    rfl

theorem cell20_571705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_571705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571705 prefixEnd_571705 := by exact prefixLift 571705
  have htrace : WordTrace (prefixWord ++ tailWord_571705) baseStart_571705 baseEnd_571705 := by
    simpa [prefixWord, tailWord_571705, baseEnd_571705] using wordTrace_append hprefix tailTrace_571705
  have hstable : (prefixWord ++ tailWord_571705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571705).length < 2 ^ (prefixWord ++ tailWord_571705).sum := by decide
  have hdescent : baseEnd_571705 < baseStart_571705 := by decide
  rcases family_descends (prefixWord ++ tailWord_571705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571719 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 5]
def baseStart_571719 : Nat := 118140960795 + 571719 * 2 ^ 59
def prefixEnd_571719 : Nat := 4983230072969 + 3 ^ 40 * 571719 * 2
def baseEnd_571719 : Nat := 260948130051514560429527

theorem tailTrace_571719 : CollatzResearch.WordTrace tailWord_571719 prefixEnd_571719 260948130051514560429527 := by
  unfold tailWord_571719
  simp only [CollatzResearch.WordTrace]
  refine ⟨20852305015767179676646211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13901536677178119784430807 20852305015767179676646211)
  ·
    refine ⟨31278457523650769514969317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20852305015767179676646211 31278457523650769514969317)
    ·
      refine ⟨5864710785684519284056747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31278457523650769514969317 5864710785684519284056747)
      ·
        refine ⟨8797066178526778926085121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5864710785684519284056747 8797066178526778926085121)
        ·
          refine ⟨6597799633895084194563841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8797066178526778926085121 6597799633895084194563841)
          ·
            refine ⟨4948349725421313145922881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6597799633895084194563841 4948349725421313145922881)
            ·
              refine ⟨3711262294065984859442161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4948349725421313145922881 3711262294065984859442161)
              ·
                refine ⟨2783446720549488644581621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711262294065984859442161 2783446720549488644581621)
                ·
                  refine ⟨260948130051514560429527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2783446720549488644581621 260948130051514560429527)
                  ·
                    rfl

theorem cell20_571719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_571719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571719 prefixEnd_571719 := by exact prefixLift 571719
  have htrace : WordTrace (prefixWord ++ tailWord_571719) baseStart_571719 baseEnd_571719 := by
    simpa [prefixWord, tailWord_571719, baseEnd_571719] using wordTrace_append hprefix tailTrace_571719
  have hstable : (prefixWord ++ tailWord_571719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571719).length < 2 ^ (prefixWord ++ tailWord_571719).sum := by decide
  have hdescent : baseEnd_571719 < baseStart_571719 := by decide
  rcases family_descends (prefixWord ++ tailWord_571719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571777 : List Nat := [1, 2, 4, 3, 1, 1, 3, 3, 2]
def baseStart_571777 : Nat := 118140960795 + 571777 * 2 ^ 59
def prefixEnd_571777 : Nat := 4983230072969 + 3 ^ 40 * 571777 * 2
def baseEnd_571777 : Nat := 260974602831924136495957

theorem tailTrace_571777 : CollatzResearch.WordTrace tailWord_571777 prefixEnd_571777 260974602831924136495957 := by
  unfold tailWord_571777
  simp only [CollatzResearch.WordTrace]
  refine ⟨20854420449557055582257585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13902946966371370388171723 20854420449557055582257585)
  ·
    refine ⟨15640815337167791686693189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20854420449557055582257585 15640815337167791686693189)
    ·
      refine ⟨2932652875718960941254973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15640815337167791686693189 2932652875718960941254973)
      ·
        refine ⟨1099744828394610352970615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2932652875718960941254973 1099744828394610352970615)
        ·
          refine ⟨1649617242591915529455923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099744828394610352970615 1649617242591915529455923)
          ·
            refine ⟨2474425863887873294183885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649617242591915529455923 2474425863887873294183885)
            ·
              refine ⟨927909698957952485318957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2474425863887873294183885 927909698957952485318957)
              ·
                refine ⟨347966137109232181994609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 927909698957952485318957 347966137109232181994609)
                ·
                  refine ⟨260974602831924136495957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 347966137109232181994609 260974602831924136495957)
                  ·
                    rfl

theorem cell20_571777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_571777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571777 prefixEnd_571777 := by exact prefixLift 571777
  have htrace : WordTrace (prefixWord ++ tailWord_571777) baseStart_571777 baseEnd_571777 := by
    simpa [prefixWord, tailWord_571777, baseEnd_571777] using wordTrace_append hprefix tailTrace_571777
  have hstable : (prefixWord ++ tailWord_571777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571777).length < 2 ^ (prefixWord ++ tailWord_571777).sum := by decide
  have hdescent : baseEnd_571777 < baseStart_571777 := by decide
  rcases family_descends (prefixWord ++ tailWord_571777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571788 : List Nat := [2, 2, 1, 2, 1, 6, 6]
def baseStart_571788 : Nat := 118140960795 + 571788 * 2 ^ 59
def prefixEnd_571788 : Nat := 4983230072969 + 3 ^ 40 * 571788 * 2
def baseEnd_571788 : Nat := 28997735947961887458805

theorem tailTrace_571788 : CollatzResearch.WordTrace tailWord_571788 prefixEnd_571788 28997735947961887458805 := by
  unfold tailWord_571788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427410826258602230454009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13903214435011469640605345 10427410826258602230454009)
  ·
    refine ⟨7820558119693951672840507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10427410826258602230454009 7820558119693951672840507)
    ·
      refine ⟨11730837179540927509260761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7820558119693951672840507 11730837179540927509260761)
      ·
        refine ⟨8798127884655695631945571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11730837179540927509260761 8798127884655695631945571)
        ·
          refine ⟨13197191826983543447918357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8798127884655695631945571 13197191826983543447918357)
          ·
            refine ⟨618618366889853599121173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13197191826983543447918357 618618366889853599121173)
            ·
              refine ⟨28997735947961887458805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 618618366889853599121173 28997735947961887458805)
              ·
                rfl

theorem cell20_571788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 6].length) (baseStart_571788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571788 prefixEnd_571788 := by exact prefixLift 571788
  have htrace : WordTrace (prefixWord ++ tailWord_571788) baseStart_571788 baseEnd_571788 := by
    simpa [prefixWord, tailWord_571788, baseEnd_571788] using wordTrace_append hprefix tailTrace_571788
  have hstable : (prefixWord ++ tailWord_571788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571788).length < 2 ^ (prefixWord ++ tailWord_571788).sum := by decide
  have hdescent : baseEnd_571788 < baseStart_571788 := by decide
  rcases family_descends (prefixWord ++ tailWord_571788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571805 : List Nat := [1, 4, 2, 1, 4, 1, 2, 5]
def baseStart_571805 : Nat := 118140960795 + 571805 * 2 ^ 59
def prefixEnd_571805 : Nat := 4983230072969 + 3 ^ 40 * 571805 * 2
def baseEnd_571805 : Nat := 86995794264960161187503

theorem tailTrace_571805 : CollatzResearch.WordTrace tailWord_571805 prefixEnd_571805 86995794264960161187503 := by
  unfold tailWord_571805
  simp only [CollatzResearch.WordTrace]
  refine ⟨20855441693455616364276869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13903627795637077576184579 20855441693455616364276869)
  ·
    refine ⟨3910395317522928068301913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20855441693455616364276869 3910395317522928068301913)
    ·
      refine ⟨2932796488142196051226435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3910395317522928068301913 2932796488142196051226435)
      ·
        refine ⟨4399194732213294076839653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2932796488142196051226435 4399194732213294076839653)
        ·
          refine ⟨824849012289992639407435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4399194732213294076839653 824849012289992639407435)
          ·
            refine ⟨1237273518434988959111153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824849012289992639407435 1237273518434988959111153)
            ·
              refine ⟨927955138826241719333365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237273518434988959111153 927955138826241719333365)
              ·
                refine ⟨86995794264960161187503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 927955138826241719333365 86995794264960161187503)
                ·
                  rfl

theorem cell20_571805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_571805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571805 prefixEnd_571805 := by exact prefixLift 571805
  have htrace : WordTrace (prefixWord ++ tailWord_571805) baseStart_571805 baseEnd_571805 := by
    simpa [prefixWord, tailWord_571805, baseEnd_571805] using wordTrace_append hprefix tailTrace_571805
  have hstable : (prefixWord ++ tailWord_571805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571805).length < 2 ^ (prefixWord ++ tailWord_571805).sum := by decide
  have hdescent : baseEnd_571805 < baseStart_571805 := by decide
  rcases family_descends (prefixWord ++ tailWord_571805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571847 : List Nat := [1, 1, 4, 1, 1, 12]
def baseStart_571847 : Nat := 118140960795 + 571847 * 2 ^ 59
def prefixEnd_571847 : Nat := 4983230072969 + 3 ^ 40 * 571847 * 2
def baseEnd_571847 : Nat := 9666909360715370524531

theorem tailTrace_571847 : CollatzResearch.WordTrace tailWord_571847 prefixEnd_571847 9666909360715370524531 := by
  unfold tailWord_571847
  simp only [CollatzResearch.WordTrace]
  refine ⟨20856973559303457537305795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13904649039535638358203863 20856973559303457537305795)
  ·
    refine ⟨31285460338955186305958693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20856973559303457537305795 31285460338955186305958693)
    ·
      refine ⟨5866023813554097432367255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31285460338955186305958693 5866023813554097432367255)
      ·
        refine ⟨8799035720331146148550883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866023813554097432367255 8799035720331146148550883)
        ·
          refine ⟨13198553580496719222826325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799035720331146148550883 13198553580496719222826325)
          ·
            refine ⟨9666909360715370524531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13198553580496719222826325 9666909360715370524531)
            ·
              rfl

theorem cell20_571847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 12].length) (baseStart_571847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571847 prefixEnd_571847 := by exact prefixLift 571847
  have htrace : WordTrace (prefixWord ++ tailWord_571847) baseStart_571847 baseEnd_571847 := by
    simpa [prefixWord, tailWord_571847, baseEnd_571847] using wordTrace_append hprefix tailTrace_571847
  have hstable : (prefixWord ++ tailWord_571847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571847).length < 2 ^ (prefixWord ++ tailWord_571847).sum := by decide
  have hdescent : baseEnd_571847 < baseStart_571847 := by decide
  rcases family_descends (prefixWord ++ tailWord_571847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571850 : List Nat := [3, 1, 2, 1, 2, 2, 4, 2, 3]
def baseStart_571850 : Nat := 118140960795 + 571850 * 2 ^ 59
def prefixEnd_571850 : Nat := 4983230072969 + 3 ^ 40 * 571850 * 2
def baseEnd_571850 : Nat := 261007922021060327062325

theorem tailTrace_571850 : CollatzResearch.WordTrace tailWord_571850 prefixEnd_571850 261007922021060327062325 := by
  unfold tailWord_571850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5214270744573147262416251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13904721985528392699776669 5214270744573147262416251)
  ·
    refine ⟨7821406116859720893624377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5214270744573147262416251 7821406116859720893624377)
    ·
      refine ⟨5866054587644790670218283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7821406116859720893624377 5866054587644790670218283)
      ·
        refine ⟨8799081881467186005327425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866054587644790670218283 8799081881467186005327425)
        ·
          refine ⟨6599311411100389503995569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8799081881467186005327425 6599311411100389503995569)
          ·
            refine ⟨4949483558325292127996677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6599311411100389503995569 4949483558325292127996677)
            ·
              refine ⟨928028167185992273999377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4949483558325292127996677 928028167185992273999377)
              ·
                refine ⟨696021125389494205499533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928028167185992273999377 696021125389494205499533)
                ·
                  refine ⟨261007922021060327062325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696021125389494205499533 261007922021060327062325)
                  ·
                    rfl

theorem cell20_571850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_571850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571850 prefixEnd_571850 := by exact prefixLift 571850
  have htrace : WordTrace (prefixWord ++ tailWord_571850) baseStart_571850 baseEnd_571850 := by
    simpa [prefixWord, tailWord_571850, baseEnd_571850] using wordTrace_append hprefix tailTrace_571850
  have hstable : (prefixWord ++ tailWord_571850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571850).length < 2 ^ (prefixWord ++ tailWord_571850).sum := by decide
  have hdescent : baseEnd_571850 < baseStart_571850 := by decide
  rcases family_descends (prefixWord ++ tailWord_571850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571905 : List Nat := [1, 2, 4, 1, 3, 3, 1, 2, 3]
def baseStart_571905 : Nat := 118140960795 + 571905 * 2 ^ 59
def prefixEnd_571905 : Nat := 4983230072969 + 3 ^ 40 * 571905 * 2
def baseEnd_571905 : Nat := 261033025519724580228767

theorem tailTrace_571905 : CollatzResearch.WordTrace tailWord_571905 prefixEnd_571905 261033025519724580228767 := by
  unfold tailWord_571905
  simp only [CollatzResearch.WordTrace]
  refine ⟨20859088993093333442917169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13906059328728888961944779 20859088993093333442917169)
  ·
    refine ⟨15644316744820000082187877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20859088993093333442917169 15644316744820000082187877)
    ·
      refine ⟨2933309389653750015410227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15644316744820000082187877 2933309389653750015410227)
      ·
        refine ⟨4399964084480625023115341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2933309389653750015410227 4399964084480625023115341)
        ·
          refine ⟨1649986531680234383668253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4399964084480625023115341 1649986531680234383668253)
          ·
            refine ⟨618744949380087893875595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1649986531680234383668253 618744949380087893875595)
            ·
              refine ⟨928117424070131840813393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 618744949380087893875595 928117424070131840813393)
              ·
                refine ⟨696088068052598880610045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928117424070131840813393 696088068052598880610045)
                ·
                  refine ⟨261033025519724580228767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696088068052598880610045 261033025519724580228767)
                  ·
                    rfl

theorem cell20_571905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 1, 2, 3].length) (baseStart_571905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571905 prefixEnd_571905 := by exact prefixLift 571905
  have htrace : WordTrace (prefixWord ++ tailWord_571905) baseStart_571905 baseEnd_571905 := by
    simpa [prefixWord, tailWord_571905, baseEnd_571905] using wordTrace_append hprefix tailTrace_571905
  have hstable : (prefixWord ++ tailWord_571905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571905).length < 2 ^ (prefixWord ++ tailWord_571905).sum := by decide
  have hdescent : baseEnd_571905 < baseStart_571905 := by decide
  rcases family_descends (prefixWord ++ tailWord_571905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571923 : List Nat := [1, 1, 1, 2, 1, 5, 2, 7]
def baseStart_571923 : Nat := 118140960795 + 571923 * 2 ^ 59
def prefixEnd_571923 : Nat := 4983230072969 + 3 ^ 40 * 571923 * 2
def baseEnd_571923 : Nat := 87013747070065505876231

theorem tailTrace_571923 : CollatzResearch.WordTrace tailWord_571923 prefixEnd_571923 87013747070065505876231 := by
  unfold tailWord_571923
  simp only [CollatzResearch.WordTrace]
  refine ⟨20859745507028122517072423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13906497004685415011381615 20859745507028122517072423)
  ·
    refine ⟨31289618260542183775608635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20859745507028122517072423 31289618260542183775608635)
    ·
      refine ⟨46934427390813275663412953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31289618260542183775608635 46934427390813275663412953)
      ·
        refine ⟨35200820543109956747559715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46934427390813275663412953 35200820543109956747559715)
        ·
          refine ⟨52801230814664935121339573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35200820543109956747559715 52801230814664935121339573)
          ·
            refine ⟨4950115388874837667625585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52801230814664935121339573 4950115388874837667625585)
            ·
              refine ⟨3712586541656128250719189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4950115388874837667625585 3712586541656128250719189)
              ·
                refine ⟨87013747070065505876231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3712586541656128250719189 87013747070065505876231)
                ·
                  rfl

theorem cell20_571923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_571923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571923 prefixEnd_571923 := by exact prefixLift 571923
  have htrace : WordTrace (prefixWord ++ tailWord_571923) baseStart_571923 baseEnd_571923 := by
    simpa [prefixWord, tailWord_571923, baseEnd_571923] using wordTrace_append hprefix tailTrace_571923
  have hstable : (prefixWord ++ tailWord_571923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571923).length < 2 ^ (prefixWord ++ tailWord_571923).sum := by decide
  have hdescent : baseEnd_571923 < baseStart_571923 := by decide
  rcases family_descends (prefixWord ++ tailWord_571923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571933 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 4]
def baseStart_571933 : Nat := 118140960795 + 571933 * 2 ^ 59
def prefixEnd_571933 : Nat := 4983230072969 + 3 ^ 40 * 571933 * 2
def baseEnd_571933 : Nat := 261045805482680927295319

theorem tailTrace_571933 : CollatzResearch.WordTrace tailWord_571933 prefixEnd_571933 261045805482680927295319 := by
  unfold tailWord_571933
  simp only [CollatzResearch.WordTrace]
  refine ⟨20860110236991894224936453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13906740157994596149957635 20860110236991894224936453)
  ·
    refine ⟨3911270669435980167175585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20860110236991894224936453 3911270669435980167175585)
    ·
      refine ⟨2933453002076985125381689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3911270669435980167175585 2933453002076985125381689)
      ·
        refine ⟨2200089751557738844036267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2933453002076985125381689 2200089751557738844036267)
        ·
          refine ⟨3300134627336608266054401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200089751557738844036267 3300134627336608266054401)
          ·
            refine ⟨2475100970502456199540801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3300134627336608266054401 2475100970502456199540801)
            ·
              refine ⟨1856325727876842149655601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475100970502456199540801 1856325727876842149655601)
              ·
                refine ⟨1392244295907631612241701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856325727876842149655601 1392244295907631612241701)
                ·
                  refine ⟨261045805482680927295319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1392244295907631612241701 261045805482680927295319)
                  ·
                    rfl

theorem cell20_571933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_571933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571933 prefixEnd_571933 := by exact prefixLift 571933
  have htrace : WordTrace (prefixWord ++ tailWord_571933) baseStart_571933 baseEnd_571933 := by
    simpa [prefixWord, tailWord_571933, baseEnd_571933] using wordTrace_append hprefix tailTrace_571933
  have hstable : (prefixWord ++ tailWord_571933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571933).length < 2 ^ (prefixWord ++ tailWord_571933).sum := by decide
  have hdescent : baseEnd_571933 < baseStart_571933 := by decide
  rcases family_descends (prefixWord ++ tailWord_571933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571936 : List Nat := [2, 1, 1, 6, 2, 2, 2, 4]
def baseStart_571936 : Nat := 118140960795 + 571936 * 2 ^ 59
def prefixEnd_571936 : Nat := 4983230072969 + 3 ^ 40 * 571936 * 2
def baseEnd_571936 : Nat := 87015724921475416731769

theorem tailTrace_571936 : CollatzResearch.WordTrace tailWord_571936 prefixEnd_571936 87015724921475416731769 := by
  unfold tailWord_571936
  simp only [CollatzResearch.WordTrace]
  refine ⟨10430109827990512868647831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13906813103987350491530441 10430109827990512868647831)
  ·
    refine ⟨15645164741985769302971747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10430109827990512868647831 15645164741985769302971747)
    ·
      refine ⟨23467747112978653954457621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15645164741985769302971747 23467747112978653954457621)
      ·
        refine ⟨1100050645920874404115201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23467747112978653954457621 1100050645920874404115201)
        ·
          refine ⟨825037984440655803086401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1100050645920874404115201 825037984440655803086401)
          ·
            refine ⟨618778488330491852314801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825037984440655803086401 618778488330491852314801)
            ·
              refine ⟨464083866247868889236101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 618778488330491852314801 464083866247868889236101)
              ·
                refine ⟨87015724921475416731769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464083866247868889236101 87015724921475416731769)
                ·
                  rfl

theorem cell20_571936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_571936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571936 prefixEnd_571936 := by exact prefixLift 571936
  have htrace : WordTrace (prefixWord ++ tailWord_571936) baseStart_571936 baseEnd_571936 := by
    simpa [prefixWord, tailWord_571936, baseEnd_571936] using wordTrace_append hprefix tailTrace_571936
  have hstable : (prefixWord ++ tailWord_571936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571936).length < 2 ^ (prefixWord ++ tailWord_571936).sum := by decide
  have hdescent : baseEnd_571936 < baseStart_571936 := by decide
  rcases family_descends (prefixWord ++ tailWord_571936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571954 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_571954 : Nat := 118140960795 + 571954 * 2 ^ 59
def prefixEnd_571954 : Nat := 4983230072969 + 3 ^ 40 * 571954 * 2
def baseEnd_571954 : Nat := 261055390454898187595233

theorem tailTrace_571954 : CollatzResearch.WordTrace tailWord_571954 prefixEnd_571954 261055390454898187595233 := by
  unfold tailWord_571954
  simp only [CollatzResearch.WordTrace]
  refine ⟨5215219042478953702862729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13907250779943876540967277 5215219042478953702862729)
  ·
    refine ⟨3911414281859215277147047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5215219042478953702862729 3911414281859215277147047)
    ·
      refine ⟨5867121422788822915720571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911414281859215277147047 5867121422788822915720571)
      ·
        refine ⟨8800682134183234373580857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867121422788822915720571 8800682134183234373580857)
        ·
          refine ⟨6600511600637425780185643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8800682134183234373580857 6600511600637425780185643)
          ·
            refine ⟨9900767400956138670278465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6600511600637425780185643 9900767400956138670278465)
            ·
              refine ⟨7425575550717104002708849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9900767400956138670278465 7425575550717104002708849)
              ·
                refine ⟨5569181663037828002031637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7425575550717104002708849 5569181663037828002031637)
                ·
                  refine ⟨261055390454898187595233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5569181663037828002031637 261055390454898187595233)
                  ·
                    rfl

theorem cell20_571954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_571954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571954 prefixEnd_571954 := by exact prefixLift 571954
  have htrace : WordTrace (prefixWord ++ tailWord_571954) baseStart_571954 baseEnd_571954 := by
    simpa [prefixWord, tailWord_571954, baseEnd_571954] using wordTrace_append hprefix tailTrace_571954
  have hstable : (prefixWord ++ tailWord_571954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571954).length < 2 ^ (prefixWord ++ tailWord_571954).sum := by decide
  have hdescent : baseEnd_571954 < baseStart_571954 := by decide
  rcases family_descends (prefixWord ++ tailWord_571954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571971 : List Nat := [1, 1, 1, 3, 1, 2, 1, 8, 2]
def baseStart_571971 : Nat := 118140960795 + 571971 * 2 ^ 59
def prefixEnd_571971 : Nat := 4983230072969 + 3 ^ 40 * 571971 * 2
def baseEnd_571971 : Nat := 261063149718121684028497

theorem tailTrace_571971 : CollatzResearch.WordTrace tailWord_571971 prefixEnd_571971 261063149718121684028497 := by
  unfold tailWord_571971
  simp only [CollatzResearch.WordTrace]
  refine ⟨20861496210854226714819767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13907664140569484476546511 20861496210854226714819767)
  ·
    refine ⟨31292244316281340072229651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20861496210854226714819767 31292244316281340072229651)
    ·
      refine ⟨46938366474422010108344477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31292244316281340072229651 46938366474422010108344477)
      ·
        refine ⟨17601887427908253790629179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46938366474422010108344477 17601887427908253790629179)
        ·
          refine ⟨26402831141862380685943769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17601887427908253790629179 26402831141862380685943769)
          ·
            refine ⟨19802123356396785514457827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26402831141862380685943769 19802123356396785514457827)
            ·
              refine ⟨29703185034595178271686741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19802123356396785514457827 29703185034595178271686741)
              ·
                refine ⟨348084199624162245371329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 29703185034595178271686741 348084199624162245371329)
                ·
                  refine ⟨261063149718121684028497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348084199624162245371329 261063149718121684028497)
                  ·
                    rfl

theorem cell20_571971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 8, 2].length) (baseStart_571971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571971 prefixEnd_571971 := by exact prefixLift 571971
  have htrace : WordTrace (prefixWord ++ tailWord_571971) baseStart_571971 baseEnd_571971 := by
    simpa [prefixWord, tailWord_571971, baseEnd_571971] using wordTrace_append hprefix tailTrace_571971
  have hstable : (prefixWord ++ tailWord_571971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571971).length < 2 ^ (prefixWord ++ tailWord_571971).sum := by decide
  have hdescent : baseEnd_571971 < baseStart_571971 := by decide
  rcases family_descends (prefixWord ++ tailWord_571971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571974 : List Nat := [6, 1, 1, 1, 2, 2, 2, 5]
def baseStart_571974 : Nat := 118140960795 + 571974 * 2 ^ 59
def prefixEnd_571974 : Nat := 4983230072969 + 3 ^ 40 * 571974 * 2
def baseEnd_571974 : Nat := 87021506333289002309495

theorem tailTrace_571974 : CollatzResearch.WordTrace tailWord_571974 prefixEnd_571974 87021506333289002309495 := by
  unfold tailWord_571974
  simp only [CollatzResearch.WordTrace]
  refine ⟨651925175932604944599343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13907737086562238818119317 651925175932604944599343)
  ·
    refine ⟨977887763898907416899015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 651925175932604944599343 977887763898907416899015)
    ·
      refine ⟨1466831645848361125348523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977887763898907416899015 1466831645848361125348523)
      ·
        refine ⟨2200247468772541688022785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466831645848361125348523 2200247468772541688022785)
        ·
          refine ⟨1650185601579406266017089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2200247468772541688022785 1650185601579406266017089)
          ·
            refine ⟨1237639201184554699512817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1650185601579406266017089 1237639201184554699512817)
            ·
              refine ⟨928229400888416024634613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237639201184554699512817 928229400888416024634613)
              ·
                refine ⟨87021506333289002309495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 928229400888416024634613 87021506333289002309495)
                ·
                  rfl

theorem cell20_571974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_571974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571974 prefixEnd_571974 := by exact prefixLift 571974
  have htrace : WordTrace (prefixWord ++ tailWord_571974) baseStart_571974 baseEnd_571974 := by
    simpa [prefixWord, tailWord_571974, baseEnd_571974] using wordTrace_append hprefix tailTrace_571974
  have hstable : (prefixWord ++ tailWord_571974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571974).length < 2 ^ (prefixWord ++ tailWord_571974).sum := by decide
  have hdescent : baseEnd_571974 < baseStart_571974 := by decide
  rcases family_descends (prefixWord ++ tailWord_571974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571978 : List Nat := [3, 1, 2, 1, 1, 5, 2, 5]
def baseStart_571978 : Nat := 118140960795 + 571978 * 2 ^ 59
def prefixEnd_571978 : Nat := 4983230072969 + 3 ^ 40 * 571978 * 2
def baseEnd_571978 : Nat := 87022114902953590265045

theorem tailTrace_571978 : CollatzResearch.WordTrace tailWord_571978 prefixEnd_571978 87022114902953590265045 := by
  unfold tailWord_571978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5215437880457216727581147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13907834347885911273549725 5215437880457216727581147)
  ·
    refine ⟨7823156820685825091371721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5215437880457216727581147 7823156820685825091371721)
    ·
      refine ⟨5867367615514368818528791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7823156820685825091371721 5867367615514368818528791)
      ·
        refine ⟨8801051423271553227793187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867367615514368818528791 8801051423271553227793187)
        ·
          refine ⟨13201577134907329841689781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8801051423271553227793187 13201577134907329841689781)
          ·
            refine ⟨1237647856397562172658417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13201577134907329841689781 1237647856397562172658417)
            ·
              refine ⟨928235892298171629493813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1237647856397562172658417 928235892298171629493813)
              ·
                refine ⟨87022114902953590265045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 928235892298171629493813 87022114902953590265045)
                ·
                  rfl

theorem cell20_571978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_571978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571978 prefixEnd_571978 := by exact prefixLift 571978
  have htrace : WordTrace (prefixWord ++ tailWord_571978) baseStart_571978 baseEnd_571978 := by
    simpa [prefixWord, tailWord_571978, baseEnd_571978] using wordTrace_append hprefix tailTrace_571978
  have hstable : (prefixWord ++ tailWord_571978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571978).length < 2 ^ (prefixWord ++ tailWord_571978).sum := by decide
  have hdescent : baseEnd_571978 < baseStart_571978 := by decide
  rcases family_descends (prefixWord ++ tailWord_571978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571981 : List Nat := [1, 6, 1, 1, 2, 2, 1, 3, 3]
def baseStart_571981 : Nat := 118140960795 + 571981 * 2 ^ 59
def prefixEnd_571981 : Nat := 4983230072969 + 3 ^ 40 * 571981 * 2
def baseEnd_571981 : Nat := 261067713990606093695123

theorem tailTrace_571981 : CollatzResearch.WordTrace tailWord_571981 prefixEnd_571981 261067713990606093695123 := by
  unfold tailWord_571981
  simp only [CollatzResearch.WordTrace]
  refine ⟨20861860940817998422683797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13907907293878665615122531 20861860940817998422683797)
  ·
    refine ⟨977899731600843676063303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20861860940817998422683797 977899731600843676063303)
    ·
      refine ⟨1466849597401265514094955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 977899731600843676063303 1466849597401265514094955)
      ·
        refine ⟨2200274396101898271142433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466849597401265514094955 2200274396101898271142433)
        ·
          refine ⟨1650205797076423703356825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2200274396101898271142433 1650205797076423703356825)
          ·
            refine ⟨1237654347807317777517619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1650205797076423703356825 1237654347807317777517619)
            ·
              refine ⟨1856481521710976666276429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237654347807317777517619 1856481521710976666276429)
              ·
                refine ⟨696180570641616249853661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1856481521710976666276429 696180570641616249853661)
                ·
                  refine ⟨261067713990606093695123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696180570641616249853661 261067713990606093695123)
                  ·
                    rfl

theorem cell20_571981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_571981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571981 prefixEnd_571981 := by exact prefixLift 571981
  have htrace : WordTrace (prefixWord ++ tailWord_571981) baseStart_571981 baseEnd_571981 := by
    simpa [prefixWord, tailWord_571981, baseEnd_571981] using wordTrace_append hprefix tailTrace_571981
  have hstable : (prefixWord ++ tailWord_571981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571981).length < 2 ^ (prefixWord ++ tailWord_571981).sum := by decide
  have hdescent : baseEnd_571981 < baseStart_571981 := by decide
  rcases family_descends (prefixWord ++ tailWord_571981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_571992 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_571992 : Nat := 118140960795 + 571992 * 2 ^ 59
def prefixEnd_571992 : Nat := 4983230072969 + 3 ^ 40 * 571992 * 2
def baseEnd_571992 : Nat := 261072734690338944328411

theorem tailTrace_571992 : CollatzResearch.WordTrace tailWord_571992 prefixEnd_571992 261072734690338944328411 := by
  unfold tailWord_571992
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431131071889073650667115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13908174762518764867556153 10431131071889073650667115)
  ·
    refine ⟨15646696607833610476000673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10431131071889073650667115 15646696607833610476000673)
    ·
      refine ⟨11735022455875207857000505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15646696607833610476000673 11735022455875207857000505)
      ·
        refine ⟨8801266841906405892750379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11735022455875207857000505 8801266841906405892750379)
        ·
          refine ⟨13201900262859608839125569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8801266841906405892750379 13201900262859608839125569)
          ·
            refine ⟨9901425197144706629344177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13201900262859608839125569 9901425197144706629344177)
            ·
              refine ⟨7426068897858529972008133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9901425197144706629344177 7426068897858529972008133)
              ·
                refine ⟨1392387918348474369751525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7426068897858529972008133 1392387918348474369751525)
                ·
                  refine ⟨261072734690338944328411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1392387918348474369751525 261072734690338944328411)
                  ·
                    rfl

theorem cell20_571992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_571992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_571992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_571992 prefixEnd_571992 := by exact prefixLift 571992
  have htrace : WordTrace (prefixWord ++ tailWord_571992) baseStart_571992 baseEnd_571992 := by
    simpa [prefixWord, tailWord_571992, baseEnd_571992] using wordTrace_append hprefix tailTrace_571992
  have hstable : (prefixWord ++ tailWord_571992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_571992).length < 2 ^ (prefixWord ++ tailWord_571992).sum := by decide
  have hdescent : baseEnd_571992 < baseStart_571992 := by decide
  rcases family_descends (prefixWord ++ tailWord_571992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572009 : List Nat := [1, 2, 1, 1, 1, 4, 1, 7, 2]
def baseStart_572009 : Nat := 118140960795 + 572009 * 2 ^ 59
def prefixEnd_572009 : Nat := 4983230072969 + 3 ^ 40 * 572009 * 2
def baseEnd_572009 : Nat := 261080493953562440761675

theorem tailTrace_572009 : CollatzResearch.WordTrace tailWord_572009 prefixEnd_572009 261080493953562440761675 := by
  unfold tailWord_572009
  simp only [CollatzResearch.WordTrace]
  refine ⟨20862882184716559204703081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13908588123144372803135387 20862882184716559204703081)
  ·
    refine ⟨15647161638537419403527311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20862882184716559204703081 15647161638537419403527311)
    ·
      refine ⟨23470742457806129105290967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15647161638537419403527311 23470742457806129105290967)
      ·
        refine ⟨35206113686709193657936451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23470742457806129105290967 35206113686709193657936451)
        ·
          refine ⟨52809170530063790486904677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35206113686709193657936451 52809170530063790486904677)
          ·
            refine ⟨9901719474386960716294627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52809170530063790486904677 9901719474386960716294627)
            ·
              refine ⟨14852579211580441074441941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9901719474386960716294627 14852579211580441074441941)
              ·
                refine ⟨348107325271416587682233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14852579211580441074441941 348107325271416587682233)
                ·
                  refine ⟨261080493953562440761675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348107325271416587682233 261080493953562440761675)
                  ·
                    rfl

theorem cell20_572009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_572009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572009 prefixEnd_572009 := by exact prefixLift 572009
  have htrace : WordTrace (prefixWord ++ tailWord_572009) baseStart_572009 baseEnd_572009 := by
    simpa [prefixWord, tailWord_572009, baseEnd_572009] using wordTrace_append hprefix tailTrace_572009
  have hstable : (prefixWord ++ tailWord_572009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572009).length < 2 ^ (prefixWord ++ tailWord_572009).sum := by decide
  have hdescent : baseEnd_572009 < baseStart_572009 := by decide
  rcases family_descends (prefixWord ++ tailWord_572009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572016 : List Nat := [2, 1, 1, 1, 8, 7]
def baseStart_572016 : Nat := 118140960795 + 572016 * 2 ^ 59
def prefixEnd_572016 : Nat := 4983230072969 + 3 ^ 40 * 572016 * 2
def baseEnd_572016 : Nat := 9669766257196352871419

theorem tailTrace_572016 : CollatzResearch.WordTrace tailWord_572016 prefixEnd_572016 9669766257196352871419 := by
  unfold tailWord_572016
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431568747845599700103951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13908758330460799600138601 10431568747845599700103951)
  ·
    refine ⟨15647353121768399550155927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10431568747845599700103951 15647353121768399550155927)
    ·
      refine ⟨23471029682652599325233891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15647353121768399550155927 23471029682652599325233891)
      ·
        refine ⟨35206544523978898987850837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23471029682652599325233891 35206544523978898987850837)
        ·
          refine ⟨412576693640377722513877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 35206544523978898987850837 412576693640377722513877)
          ·
            refine ⟨9669766257196352871419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 412576693640377722513877 9669766257196352871419)
            ·
              rfl

theorem cell20_572016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 7].length) (baseStart_572016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572016 prefixEnd_572016 := by exact prefixLift 572016
  have htrace : WordTrace (prefixWord ++ tailWord_572016) baseStart_572016 baseEnd_572016 := by
    simpa [prefixWord, tailWord_572016, baseEnd_572016] using wordTrace_append hprefix tailTrace_572016
  have hstable : (prefixWord ++ tailWord_572016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572016).length < 2 ^ (prefixWord ++ tailWord_572016).sum := by decide
  have hdescent : baseEnd_572016 < baseStart_572016 := by decide
  rcases family_descends (prefixWord ++ tailWord_572016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572023 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 3]
def baseStart_572023 : Nat := 118140960795 + 572023 * 2 ^ 59
def prefixEnd_572023 : Nat := 4983230072969 + 3 ^ 40 * 572023 * 2
def baseEnd_572023 : Nat := 261086883935040614294951

theorem tailTrace_572023 : CollatzResearch.WordTrace tailWord_572023 prefixEnd_572023 261086883935040614294951 := by
  unfold tailWord_572023
  simp only [CollatzResearch.WordTrace]
  refine ⟨20863392806665839595712723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13908928537777226397141815 20863392806665839595712723)
  ·
    refine ⟨31295089209998759393569085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20863392806665839595712723 31295089209998759393569085)
    ·
      refine ⟨11735658453749534772588407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31295089209998759393569085 11735658453749534772588407)
      ·
        refine ⟨17603487680624302158882611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11735658453749534772588407 17603487680624302158882611)
        ·
          refine ⟨26405231520936453238323917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17603487680624302158882611 26405231520936453238323917)
          ·
            refine ⟨9901961820351169964371469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26405231520936453238323917 9901961820351169964371469)
            ·
              refine ⟨3713235682631688736639301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9901961820351169964371469 3713235682631688736639301)
              ·
                refine ⟨696231690493441638119869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3713235682631688736639301 696231690493441638119869)
                ·
                  refine ⟨261086883935040614294951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696231690493441638119869 261086883935040614294951)
                  ·
                    rfl

theorem cell20_572023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3].length) (baseStart_572023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572023 prefixEnd_572023 := by exact prefixLift 572023
  have htrace : WordTrace (prefixWord ++ tailWord_572023) baseStart_572023 baseEnd_572023 := by
    simpa [prefixWord, tailWord_572023, baseEnd_572023] using wordTrace_append hprefix tailTrace_572023
  have hstable : (prefixWord ++ tailWord_572023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572023).length < 2 ^ (prefixWord ++ tailWord_572023).sum := by decide
  have hdescent : baseEnd_572023 < baseStart_572023 := by decide
  rcases family_descends (prefixWord ++ tailWord_572023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572068 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_572068 : Nat := 118140960795 + 572068 * 2 ^ 59
def prefixEnd_572068 : Nat := 4983230072969 + 3 ^ 40 * 572068 * 2
def baseEnd_572068 : Nat := 261107423161220457794767

theorem tailTrace_572068 : CollatzResearch.WordTrace tailWord_572068 prefixEnd_572068 261107423161220457794767 := by
  unfold tailWord_572068
  simp only [CollatzResearch.WordTrace]
  refine ⟨10432517045751406140550429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13910022727668541520733905 10432517045751406140550429)
  ·
    refine ⟨3912193892156777302706411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10432517045751406140550429 3912193892156777302706411)
    ·
      refine ⟨5868290838235165954059617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3912193892156777302706411 5868290838235165954059617)
      ·
        refine ⟨4401218128676374465544713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5868290838235165954059617 4401218128676374465544713)
        ·
          refine ⟨3300913596507280849158535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4401218128676374465544713 3300913596507280849158535)
          ·
            refine ⟨4951370394760921273737803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300913596507280849158535 4951370394760921273737803)
            ·
              refine ⟨7427055592141381910606705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951370394760921273737803 7427055592141381910606705)
              ·
                refine ⟨5570291694106036432955029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7427055592141381910606705 5570291694106036432955029)
                ·
                  refine ⟨261107423161220457794767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5570291694106036432955029 261107423161220457794767)
                  ·
                    rfl

theorem cell20_572068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_572068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572068 prefixEnd_572068 := by exact prefixLift 572068
  have htrace : WordTrace (prefixWord ++ tailWord_572068) baseStart_572068 baseEnd_572068 := by
    simpa [prefixWord, tailWord_572068, baseEnd_572068] using wordTrace_append hprefix tailTrace_572068
  have hstable : (prefixWord ++ tailWord_572068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572068).length < 2 ^ (prefixWord ++ tailWord_572068).sum := by decide
  have hdescent : baseEnd_572068 < baseStart_572068 := by decide
  rcases family_descends (prefixWord ++ tailWord_572068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572071 : List Nat := [1, 1, 6, 3, 1, 1, 7]
def baseStart_572071 : Nat := 118140960795 + 572071 * 2 ^ 59
def prefixEnd_572071 : Nat := 4983230072969 + 3 ^ 40 * 572071 * 2
def baseEnd_572071 : Nat := 29012088049218420077195

theorem tailTrace_572071 : CollatzResearch.WordTrace tailWord_572071 prefixEnd_572071 29012088049218420077195 := by
  unfold tailWord_572071
  simp only [CollatzResearch.WordTrace]
  refine ⟨20865143510491943793460067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13910095673661295862306711 20865143510491943793460067)
  ·
    refine ⟨31297715265737915690190101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20865143510491943793460067 31297715265737915690190101)
    ·
      refine ⟨1467080403081464797977661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31297715265737915690190101 1467080403081464797977661)
      ·
        refine ⟨550155151155549299241623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1467080403081464797977661 550155151155549299241623)
        ·
          refine ⟨825232726733323948862435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550155151155549299241623 825232726733323948862435)
          ·
            refine ⟨1237849090099985923293653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825232726733323948862435 1237849090099985923293653)
            ·
              refine ⟨29012088049218420077195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1237849090099985923293653 29012088049218420077195)
              ·
                rfl

theorem cell20_572071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 7].length) (baseStart_572071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572071 prefixEnd_572071 := by exact prefixLift 572071
  have htrace : WordTrace (prefixWord ++ tailWord_572071) baseStart_572071 baseEnd_572071 := by
    simpa [prefixWord, tailWord_572071, baseEnd_572071] using wordTrace_append hprefix tailTrace_572071
  have hstable : (prefixWord ++ tailWord_572071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572071).length < 2 ^ (prefixWord ++ tailWord_572071).sum := by decide
  have hdescent : baseEnd_572071 < baseStart_572071 := by decide
  rcases family_descends (prefixWord ++ tailWord_572071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572085 : List Nat := [1, 3, 3, 3, 1, 1, 1, 3, 4]
def baseStart_572085 : Nat := 118140960795 + 572085 * 2 ^ 59
def prefixEnd_572085 : Nat := 4983230072969 + 3 ^ 40 * 572085 * 2
def baseEnd_572085 : Nat := 261115182424443954228031

theorem tailTrace_572085 : CollatzResearch.WordTrace tailWord_572085 prefixEnd_572085 261115182424443954228031 := by
  unfold tailWord_572085
  simp only [CollatzResearch.WordTrace]
  refine ⟨20865654132441224184469709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13910436088294149456313139 20865654132441224184469709)
  ·
    refine ⟨7824620299665459069176141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20865654132441224184469709 7824620299665459069176141)
    ·
      refine ⟨2934232612374547150941053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7824620299665459069176141 2934232612374547150941053)
      ·
        refine ⟨1100337229640455181602895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2934232612374547150941053 1100337229640455181602895)
        ·
          refine ⟨1650505844460682772404343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100337229640455181602895 1650505844460682772404343)
          ·
            refine ⟨2475758766691024158606515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650505844460682772404343 2475758766691024158606515)
            ·
              refine ⟨3713638150036536237909773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2475758766691024158606515 3713638150036536237909773)
              ·
                refine ⟨1392614306263701089216165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3713638150036536237909773 1392614306263701089216165)
                ·
                  refine ⟨261115182424443954228031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1392614306263701089216165 261115182424443954228031)
                  ·
                    rfl

theorem cell20_572085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_572085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572085 prefixEnd_572085 := by exact prefixLift 572085
  have htrace : WordTrace (prefixWord ++ tailWord_572085) baseStart_572085 baseEnd_572085 := by
    simpa [prefixWord, tailWord_572085, baseEnd_572085] using wordTrace_append hprefix tailTrace_572085
  have hstable : (prefixWord ++ tailWord_572085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572085).length < 2 ^ (prefixWord ++ tailWord_572085).sum := by decide
  have hdescent : baseEnd_572085 < baseStart_572085 := by decide
  rcases family_descends (prefixWord ++ tailWord_572085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572113 : List Nat := [1, 2, 2, 1, 2, 3, 3, 6]
def baseStart_572113 : Nat := 118140960795 + 572113 * 2 ^ 59
def prefixEnd_572113 : Nat := 4983230072969 + 3 ^ 40 * 572113 * 2
def baseEnd_572113 : Nat := 87042654129133433764861

theorem tailTrace_572113 : CollatzResearch.WordTrace tailWord_572113 prefixEnd_572113 87042654129133433764861 := by
  unfold tailWord_572113
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866675376339784966488993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13911116917559856644325995 20866675376339784966488993)
  ·
    refine ⟨15650006532254838724866745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20866675376339784966488993 15650006532254838724866745)
    ·
      refine ⟨11737504899191129043650059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15650006532254838724866745 11737504899191129043650059)
      ·
        refine ⟨17606257348786693565475089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11737504899191129043650059 17606257348786693565475089)
        ·
          refine ⟨13204693011590020174106317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17606257348786693565475089 13204693011590020174106317)
          ·
            refine ⟨4951759879346257565289869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13204693011590020174106317 4951759879346257565289869)
            ·
              refine ⟨1856909954754846586983701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4951759879346257565289869 1856909954754846586983701)
              ·
                refine ⟨87042654129133433764861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1856909954754846586983701 87042654129133433764861)
                ·
                  rfl

theorem cell20_572113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_572113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572113 prefixEnd_572113 := by exact prefixLift 572113
  have htrace : WordTrace (prefixWord ++ tailWord_572113) baseStart_572113 baseEnd_572113 := by
    simpa [prefixWord, tailWord_572113, baseEnd_572113] using wordTrace_append hprefix tailTrace_572113
  have hstable : (prefixWord ++ tailWord_572113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572113).length < 2 ^ (prefixWord ++ tailWord_572113).sum := by decide
  have hdescent : baseEnd_572113 < baseStart_572113 := by decide
  rcases family_descends (prefixWord ++ tailWord_572113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572154 : List Nat := [3, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_572154 : Nat := 118140960795 + 572154 * 2 ^ 59
def prefixEnd_572154 : Nat := 4983230072969 + 3 ^ 40 * 572154 * 2
def baseEnd_572154 : Nat := 261146675904586380927749

theorem tailTrace_572154 : CollatzResearch.WordTrace tailWord_572154 prefixEnd_572154 261146675904586380927749 := by
  unfold tailWord_572154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5217042692297812242182879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13912113846127499312487677 5217042692297812242182879)
  ·
    refine ⟨7825564038446718363274319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5217042692297812242182879 7825564038446718363274319)
    ·
      refine ⟨11738346057670077544911479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7825564038446718363274319 11738346057670077544911479)
      ·
        refine ⟨17607519086505116317367219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11738346057670077544911479 17607519086505116317367219)
        ·
          refine ⟨26411278629757674476050829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17607519086505116317367219 26411278629757674476050829)
          ·
            refine ⟨9904229486159127928519061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26411278629757674476050829 9904229486159127928519061)
            ·
              refine ⟨464260757163709121649331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9904229486159127928519061 464260757163709121649331)
              ·
                refine ⟨696391135745563682473997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464260757163709121649331 696391135745563682473997)
                ·
                  refine ⟨261146675904586380927749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696391135745563682473997 261146675904586380927749)
                  ·
                    rfl

theorem cell20_572154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_572154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572154 prefixEnd_572154 := by exact prefixLift 572154
  have htrace : WordTrace (prefixWord ++ tailWord_572154) baseStart_572154 baseEnd_572154 := by
    simpa [prefixWord, tailWord_572154, baseEnd_572154] using wordTrace_append hprefix tailTrace_572154
  have hstable : (prefixWord ++ tailWord_572154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572154).length < 2 ^ (prefixWord ++ tailWord_572154).sum := by decide
  have hdescent : baseEnd_572154 < baseStart_572154 := by decide
  rcases family_descends (prefixWord ++ tailWord_572154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572192 : List Nat := [2, 1, 1, 5, 1, 3, 2, 2, 3]
def baseStart_572192 : Nat := 118140960795 + 572192 * 2 ^ 59
def prefixEnd_572192 : Nat := 4983230072969 + 3 ^ 40 * 572192 * 2
def baseEnd_572192 : Nat := 261164020140027137660927

theorem tailTrace_572192 : CollatzResearch.WordTrace tailWord_572192 prefixEnd_572192 261164020140027137660927 := by
  unfold tailWord_572192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10434778371526790729307415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13913037828702387639076553 10434778371526790729307415)
  ·
    refine ⟨15652167557290186093961123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10434778371526790729307415 15652167557290186093961123)
    ·
      refine ⟨23478251335935279140941685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15652167557290186093961123 23478251335935279140941685)
      ·
        refine ⟨2201086062743932419463283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23478251335935279140941685 2201086062743932419463283)
        ·
          refine ⟨3301629094115898629194925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201086062743932419463283 3301629094115898629194925)
          ·
            refine ⟨1238110910293461985948097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3301629094115898629194925 1238110910293461985948097)
            ·
              refine ⟨928583182720096489461073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1238110910293461985948097 928583182720096489461073)
              ·
                refine ⟨696437387040072367095805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 928583182720096489461073 696437387040072367095805)
                ·
                  refine ⟨261164020140027137660927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696437387040072367095805 261164020140027137660927)
                  ·
                    rfl

theorem cell20_572192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_572192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572192 prefixEnd_572192 := by exact prefixLift 572192
  have htrace : WordTrace (prefixWord ++ tailWord_572192) baseStart_572192 baseEnd_572192 := by
    simpa [prefixWord, tailWord_572192, baseEnd_572192] using wordTrace_append hprefix tailTrace_572192
  have hstable : (prefixWord ++ tailWord_572192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572192).length < 2 ^ (prefixWord ++ tailWord_572192).sum := by decide
  have hdescent : baseEnd_572192 < baseStart_572192 := by decide
  rcases family_descends (prefixWord ++ tailWord_572192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572202 : List Nat := [3, 1, 4, 3, 1, 2, 1, 5]
def baseStart_572202 : Nat := 118140960795 + 572202 * 2 ^ 59
def prefixEnd_572202 : Nat := 4983230072969 + 3 ^ 40 * 572202 * 2
def baseEnd_572202 : Nat := 87056194804170515775851

theorem tailTrace_572202 : CollatzResearch.WordTrace tailWord_572202 prefixEnd_572202 87056194804170515775851 := by
  unfold tailWord_572202
  simp only [CollatzResearch.WordTrace]
  refine ⟨5217480368254338291619715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13913280982011568777652573 5217480368254338291619715)
  ·
    refine ⟨7826220552381507437429573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5217480368254338291619715 7826220552381507437429573)
    ·
      refine ⟨1467416353571532644518045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7826220552381507437429573 1467416353571532644518045)
      ·
        refine ⟨550281132589324741694267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1467416353571532644518045 550281132589324741694267)
        ·
          refine ⟨825421698883987112541401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550281132589324741694267 825421698883987112541401)
          ·
            refine ⟨619066274162990334406051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825421698883987112541401 619066274162990334406051)
            ·
              refine ⟨928599411244485501609077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619066274162990334406051 928599411244485501609077)
              ·
                refine ⟨87056194804170515775851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 928599411244485501609077 87056194804170515775851)
                ·
                  rfl

theorem cell20_572202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_572202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572202 prefixEnd_572202 := by exact prefixLift 572202
  have htrace : WordTrace (prefixWord ++ tailWord_572202) baseStart_572202 baseEnd_572202 := by
    simpa [prefixWord, tailWord_572202, baseEnd_572202] using wordTrace_append hprefix tailTrace_572202
  have hstable : (prefixWord ++ tailWord_572202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572202).length < 2 ^ (prefixWord ++ tailWord_572202).sum := by decide
  have hdescent : baseEnd_572202 < baseStart_572202 := by decide
  rcases family_descends (prefixWord ++ tailWord_572202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572244 : List Nat := [2, 4, 1, 1, 4, 1, 7]
def baseStart_572244 : Nat := 118140960795 + 572244 * 2 ^ 59
def prefixEnd_572244 : Nat := 4983230072969 + 3 ^ 40 * 572244 * 2
def baseEnd_572244 : Nat := 29020861595216229769709

theorem tailTrace_572244 : CollatzResearch.WordTrace tailWord_572244 prefixEnd_572244 29020861595216229769709 := by
  unfold tailWord_572244
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435726669432597169753893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13914302225910129559671857 10435726669432597169753893)
  ·
    refine ⟨1956698750518611969328855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10435726669432597169753893 1956698750518611969328855)
    ·
      refine ⟨2935048125777917953993283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1956698750518611969328855 2935048125777917953993283)
      ·
        refine ⟨4402572188666876930989925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935048125777917953993283 4402572188666876930989925)
        ·
          refine ⟨825482285375039424560611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4402572188666876930989925 825482285375039424560611)
          ·
            refine ⟨1238223428062559136840917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825482285375039424560611 1238223428062559136840917)
            ·
              refine ⟨29020861595216229769709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1238223428062559136840917 29020861595216229769709)
              ·
                rfl

theorem cell20_572244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 7].length) (baseStart_572244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572244 prefixEnd_572244 := by exact prefixLift 572244
  have htrace : WordTrace (prefixWord ++ tailWord_572244) baseStart_572244 baseEnd_572244 := by
    simpa [prefixWord, tailWord_572244, baseEnd_572244] using wordTrace_append hprefix tailTrace_572244
  have hstable : (prefixWord ++ tailWord_572244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572244).length < 2 ^ (prefixWord ++ tailWord_572244).sum := by decide
  have hdescent : baseEnd_572244 < baseStart_572244 := by decide
  rcases family_descends (prefixWord ++ tailWord_572244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572268 : List Nat := [2, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_572268 : Nat := 118140960795 + 572268 * 2 ^ 59
def prefixEnd_572268 : Nat := 4983230072969 + 3 ^ 40 * 572268 * 2
def baseEnd_572268 : Nat := 261198708610908651127283

theorem tailTrace_572268 : CollatzResearch.WordTrace tailWord_572268 prefixEnd_572268 261198708610908651127283 := by
  unfold tailWord_572268
  simp only [CollatzResearch.WordTrace]
  refine ⟨10436164345389123219190729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13914885793852164292254305 10436164345389123219190729)
  ·
    refine ⟨7827123259041842414393047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10436164345389123219190729 7827123259041842414393047)
    ·
      refine ⟨11740684888562763621589571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7827123259041842414393047 11740684888562763621589571)
      ·
        refine ⟨17611027332844145432384357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11740684888562763621589571 17611027332844145432384357)
        ·
          refine ⟨3302067624908277268572067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17611027332844145432384357 3302067624908277268572067)
          ·
            refine ⟨4953101437362415902858101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302067624908277268572067 4953101437362415902858101)
            ·
              refine ⟨464353259752726490892947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4953101437362415902858101 464353259752726490892947)
              ·
                refine ⟨696529889629089736339421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464353259752726490892947 696529889629089736339421)
                ·
                  refine ⟨261198708610908651127283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696529889629089736339421 261198708610908651127283)
                  ·
                    rfl

theorem cell20_572268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_572268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572268 prefixEnd_572268 := by exact prefixLift 572268
  have htrace : WordTrace (prefixWord ++ tailWord_572268) baseStart_572268 baseEnd_572268 := by
    simpa [prefixWord, tailWord_572268, baseEnd_572268] using wordTrace_append hprefix tailTrace_572268
  have hstable : (prefixWord ++ tailWord_572268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572268).length < 2 ^ (prefixWord ++ tailWord_572268).sum := by decide
  have hdescent : baseEnd_572268 < baseStart_572268 := by decide
  rcases family_descends (prefixWord ++ tailWord_572268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572278 : List Nat := [5, 1, 1, 3, 1, 3, 2, 4]
def baseStart_572278 : Nat := 118140960795 + 572278 * 2 ^ 59
def prefixEnd_572278 : Nat := 4983230072969 + 3 ^ 40 * 572278 * 2
def baseEnd_572278 : Nat := 87067757627797686931303

theorem tailTrace_572278 : CollatzResearch.WordTrace tailWord_572278 prefixEnd_572278 87067757627797686931303 := by
  unfold tailWord_572278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304543338796376134140343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13915128947161345430830325 1304543338796376134140343)
  ·
    refine ⟨1956815008194564201210515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1304543338796376134140343 1956815008194564201210515)
    ·
      refine ⟨2935222512291846301815773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1956815008194564201210515 2935222512291846301815773)
      ·
        refine ⟨1100708442109442363180915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2935222512291846301815773 1100708442109442363180915)
        ·
          refine ⟨1651062663164163544771373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100708442109442363180915 1651062663164163544771373)
          ·
            refine ⟨619148498686561329289265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1651062663164163544771373 619148498686561329289265)
            ·
              refine ⟨464361374014920996966949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619148498686561329289265 464361374014920996966949)
              ·
                refine ⟨87067757627797686931303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464361374014920996966949 87067757627797686931303)
                ·
                  rfl

theorem cell20_572278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_572278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572278 prefixEnd_572278 := by exact prefixLift 572278
  have htrace : WordTrace (prefixWord ++ tailWord_572278) baseStart_572278 baseEnd_572278 := by
    simpa [prefixWord, tailWord_572278, baseEnd_572278] using wordTrace_append hprefix tailTrace_572278
  have hstable : (prefixWord ++ tailWord_572278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572278).length < 2 ^ (prefixWord ++ tailWord_572278).sum := by decide
  have hdescent : baseEnd_572278 < baseStart_572278 := by decide
  rcases family_descends (prefixWord ++ tailWord_572278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572341 : List Nat := [1, 3, 3, 2, 1, 1, 1, 8]
def baseStart_572341 : Nat := 118140960795 + 572341 * 2 ^ 59
def prefixEnd_572341 : Nat := 4983230072969 + 3 ^ 40 * 572341 * 2
def baseEnd_572341 : Nat := 87077342600014947231217

theorem tailTrace_572341 : CollatzResearch.WordTrace tailWord_572341 prefixEnd_572341 87077342600014947231217 := by
  unfold tailWord_572341
  simp only [CollatzResearch.WordTrace]
  refine ⟨20874991219513779905788877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13916660813009186603859251 20874991219513779905788877)
  ·
    refine ⟨7828121707317667464670829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20874991219513779905788877 7828121707317667464670829)
    ·
      refine ⟨2935545640244125299251561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7828121707317667464670829 2935545640244125299251561)
      ·
        refine ⟨2201659230183093974438671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935545640244125299251561 2201659230183093974438671)
        ·
          refine ⟨3302488845274640961658007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201659230183093974438671 3302488845274640961658007)
          ·
            refine ⟨4953733267911961442487011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302488845274640961658007 4953733267911961442487011)
            ·
              refine ⟨7430599901867942163730517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953733267911961442487011 7430599901867942163730517)
              ·
                refine ⟨87077342600014947231217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7430599901867942163730517 87077342600014947231217)
                ·
                  rfl

theorem cell20_572341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_572341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572341 prefixEnd_572341 := by exact prefixLift 572341
  have htrace : WordTrace (prefixWord ++ tailWord_572341) baseStart_572341 baseEnd_572341 := by
    simpa [prefixWord, tailWord_572341, baseEnd_572341] using wordTrace_append hprefix tailTrace_572341
  have hstable : (prefixWord ++ tailWord_572341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572341).length < 2 ^ (prefixWord ++ tailWord_572341).sum := by decide
  have hdescent : baseEnd_572341 < baseStart_572341 := by decide
  rcases family_descends (prefixWord ++ tailWord_572341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572355 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 6]
def baseStart_572355 : Nat := 118140960795 + 572355 * 2 ^ 59
def prefixEnd_572355 : Nat := 4983230072969 + 3 ^ 40 * 572355 * 2
def baseEnd_572355 : Nat := 261238417781523015226927

theorem tailTrace_572355 : CollatzResearch.WordTrace tailWord_572355 prefixEnd_572355 261238417781523015226927 := by
  unfold tailWord_572355
  simp only [CollatzResearch.WordTrace]
  refine ⟨20875501841463060296798519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13917001227642040197865679 20875501841463060296798519)
  ·
    refine ⟨31313252762194590445197779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20875501841463060296798519 31313252762194590445197779)
    ·
      refine ⟨46969879143291885667796669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31313252762194590445197779 46969879143291885667796669)
      ·
        refine ⟨17613704678734457125423751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46969879143291885667796669 17613704678734457125423751)
        ·
          refine ⟨26420557018101685688135627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17613704678734457125423751 26420557018101685688135627)
          ·
            refine ⟨39630835527152528532203441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26420557018101685688135627 39630835527152528532203441)
            ·
              refine ⟨29723126645364396399152581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39630835527152528532203441 29723126645364396399152581)
              ·
                refine ⟨5573086246005824324841109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29723126645364396399152581 5573086246005824324841109)
                ·
                  refine ⟨261238417781523015226927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5573086246005824324841109 261238417781523015226927)
                  ·
                    rfl

theorem cell20_572355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_572355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572355 prefixEnd_572355 := by exact prefixLift 572355
  have htrace : WordTrace (prefixWord ++ tailWord_572355) baseStart_572355 baseEnd_572355 := by
    simpa [prefixWord, tailWord_572355, baseEnd_572355] using wordTrace_append hprefix tailTrace_572355
  have hstable : (prefixWord ++ tailWord_572355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572355).length < 2 ^ (prefixWord ++ tailWord_572355).sum := by decide
  have hdescent : baseEnd_572355 < baseStart_572355 := by decide
  rcases family_descends (prefixWord ++ tailWord_572355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572406 : List Nat := [5, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_572406 : Nat := 118140960795 + 572406 * 2 ^ 59
def prefixEnd_572406 : Nat := 4983230072969 + 3 ^ 40 * 572406 * 2
def baseEnd_572406 : Nat := 261261695571193504526719

theorem tailTrace_572406 : CollatzResearch.WordTrace tailWord_572406 prefixEnd_572406 261261695571193504526719 := by
  unfold tailWord_572406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304835122767393500431567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13918241309518864004603381 1304835122767393500431567)
  ·
    refine ⟨1957252684151090250647351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1304835122767393500431567 1957252684151090250647351)
    ·
      refine ⟨2935879026226635375971027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957252684151090250647351 2935879026226635375971027)
      ·
        refine ⟨4403818539339953063956541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935879026226635375971027 4403818539339953063956541)
        ·
          refine ⟨1651431952252482398983703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4403818539339953063956541 1651431952252482398983703)
          ·
            refine ⟨2477147928378723598475555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651431952252482398983703 2477147928378723598475555)
            ·
              refine ⟨3715721892568085397713333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477147928378723598475555 3715721892568085397713333)
              ·
                refine ⟨348348927428258006035625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3715721892568085397713333 348348927428258006035625)
                ·
                  refine ⟨261261695571193504526719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348348927428258006035625 261261695571193504526719)
                  ·
                    rfl

theorem cell20_572406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_572406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572406 prefixEnd_572406 := by exact prefixLift 572406
  have htrace : WordTrace (prefixWord ++ tailWord_572406) baseStart_572406 baseEnd_572406 := by
    simpa [prefixWord, tailWord_572406, baseEnd_572406] using wordTrace_append hprefix tailTrace_572406
  have hstable : (prefixWord ++ tailWord_572406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572406).length < 2 ^ (prefixWord ++ tailWord_572406).sum := by decide
  have hdescent : baseEnd_572406 < baseStart_572406 := by decide
  rcases family_descends (prefixWord ++ tailWord_572406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572417 : List Nat := [1, 2, 4, 1, 2, 3, 7]
def baseStart_572417 : Nat := 118140960795 + 572417 * 2 ^ 59
def prefixEnd_572417 : Nat := 4983230072969 + 3 ^ 40 * 572417 * 2
def baseEnd_572417 : Nat := 29029635141214039462223

theorem tailTrace_572417 : CollatzResearch.WordTrace tailWord_572417 prefixEnd_572417 29029635141214039462223 := by
  unfold tailWord_572417
  simp only [CollatzResearch.WordTrace]
  refine ⟨20877763167238444885555505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13918508778158963257037003 20877763167238444885555505)
  ·
    refine ⟨15658322375428833664166629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20877763167238444885555505 15658322375428833664166629)
    ·
      refine ⟨2935935445392906312031243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15658322375428833664166629 2935935445392906312031243)
      ·
        refine ⟨4403903168089359468046865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935935445392906312031243 4403903168089359468046865)
        ·
          refine ⟨3302927376067019601035149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4403903168089359468046865 3302927376067019601035149)
          ·
            refine ⟨1238597766025132350388181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3302927376067019601035149 1238597766025132350388181)
            ·
              refine ⟨29029635141214039462223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1238597766025132350388181 29029635141214039462223)
              ·
                rfl

theorem cell20_572417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_572417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572417 prefixEnd_572417 := by exact prefixLift 572417
  have htrace : WordTrace (prefixWord ++ tailWord_572417) baseStart_572417 baseEnd_572417 := by
    simpa [prefixWord, tailWord_572417, baseEnd_572417] using wordTrace_append hprefix tailTrace_572417
  have hstable : (prefixWord ++ tailWord_572417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572417).length < 2 ^ (prefixWord ++ tailWord_572417).sum := by decide
  have hdescent : baseEnd_572417 < baseStart_572417 := by decide
  rcases family_descends (prefixWord ++ tailWord_572417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572427 : List Nat := [1, 1, 1, 1, 6, 2, 2, 4, 2]
def baseStart_572427 : Nat := 118140960795 + 572427 * 2 ^ 59
def prefixEnd_572427 : Nat := 4983230072969 + 3 ^ 40 * 572427 * 2
def baseEnd_572427 : Nat := 261271280543410764826633

theorem tailTrace_572427 : CollatzResearch.WordTrace tailWord_572427 prefixEnd_572427 261271280543410764826633 := by
  unfold tailWord_572427
  simp only [CollatzResearch.WordTrace]
  refine ⟨20878127897202216593419535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13918751931468144395613023 20878127897202216593419535)
  ·
    refine ⟨31317191845803324890129303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20878127897202216593419535 31317191845803324890129303)
    ·
      refine ⟨46975787768704987335193955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31317191845803324890129303 46975787768704987335193955)
      ·
        refine ⟨70463681653057481002790933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46975787768704987335193955 70463681653057481002790933)
        ·
          refine ⟨3302985077487069422005825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70463681653057481002790933 3302985077487069422005825)
          ·
            refine ⟨2477238808115302066504369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3302985077487069422005825 2477238808115302066504369)
            ·
              refine ⟨1857929106086476549878277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477238808115302066504369 1857929106086476549878277)
              ·
                refine ⟨348361707391214353102177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1857929106086476549878277 348361707391214353102177)
                ·
                  refine ⟨261271280543410764826633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348361707391214353102177 261271280543410764826633)
                  ·
                    rfl

theorem cell20_572427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 4, 2].length) (baseStart_572427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572427 prefixEnd_572427 := by exact prefixLift 572427
  have htrace : WordTrace (prefixWord ++ tailWord_572427) baseStart_572427 baseEnd_572427 := by
    simpa [prefixWord, tailWord_572427, baseEnd_572427] using wordTrace_append hprefix tailTrace_572427
  have hstable : (prefixWord ++ tailWord_572427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572427).length < 2 ^ (prefixWord ++ tailWord_572427).sum := by decide
  have hdescent : baseEnd_572427 < baseStart_572427 := by decide
  rcases family_descends (prefixWord ++ tailWord_572427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572533 : List Nat := [1, 3, 4, 3, 2, 1, 2, 2, 2]
def baseStart_572533 : Nat := 118140960795 + 572533 * 2 ^ 59
def prefixEnd_572533 : Nat := 4983230072969 + 3 ^ 40 * 572533 * 2
def baseEnd_572533 : Nat := 261319661831745507292867

theorem tailTrace_572533 : CollatzResearch.WordTrace tailWord_572533 prefixEnd_572533 261319661831745507292867 := by
  unfold tailWord_572533
  simp only [CollatzResearch.WordTrace]
  refine ⟨20881994034818196696778253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13921329356545464464518835 20881994034818196696778253)
  ·
    refine ⟨7830747763056823761291845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20881994034818196696778253 7830747763056823761291845)
    ·
      refine ⟨1468265205573154455242221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7830747763056823761291845 1468265205573154455242221)
      ·
        refine ⟨550599452089932920715833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1468265205573154455242221 550599452089932920715833)
        ·
          refine ⟨412949589067449690536875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 550599452089932920715833 412949589067449690536875)
          ·
            refine ⟨619424383601174535805313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412949589067449690536875 619424383601174535805313)
            ·
              refine ⟨464568287700880901853985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619424383601174535805313 464568287700880901853985)
              ·
                refine ⟨348426215775660676390489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464568287700880901853985 348426215775660676390489)
                ·
                  refine ⟨261319661831745507292867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348426215775660676390489 261319661831745507292867)
                  ·
                    rfl

theorem cell20_572533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_572533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572533 prefixEnd_572533 := by exact prefixLift 572533
  have htrace : WordTrace (prefixWord ++ tailWord_572533) baseStart_572533 baseEnd_572533 := by
    simpa [prefixWord, tailWord_572533, baseEnd_572533] using wordTrace_append hprefix tailTrace_572533
  have hstable : (prefixWord ++ tailWord_572533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572533).length < 2 ^ (prefixWord ++ tailWord_572533).sum := by decide
  have hdescent : baseEnd_572533 < baseStart_572533 := by decide
  rcases family_descends (prefixWord ++ tailWord_572533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572534 : List Nat := [5, 1, 1, 2, 1, 1, 4, 2, 3]
def baseStart_572534 : Nat := 118140960795 + 572534 * 2 ^ 59
def prefixEnd_572534 : Nat := 4983230072969 + 3 ^ 40 * 572534 * 2
def baseEnd_572534 : Nat := 261320118258993948259529

theorem tailTrace_572534 : CollatzResearch.WordTrace tailWord_572534 prefixEnd_572534 261320118258993948259529 := by
  unfold tailWord_572534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305126906738410866722791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13921353671876382578376437 1305126906738410866722791)
  ·
    refine ⟨1957690360107616300084187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305126906738410866722791 1957690360107616300084187)
    ·
      refine ⟨2936535540161424450126281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1957690360107616300084187 2936535540161424450126281)
      ·
        refine ⟨2202401655121068337594711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2936535540161424450126281 2202401655121068337594711)
        ·
          refine ⟨3303602482681602506392067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202401655121068337594711 3303602482681602506392067)
          ·
            refine ⟨4955403724022403759588101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303602482681602506392067 4955403724022403759588101)
            ·
              refine ⟨929138198254200704922769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4955403724022403759588101 929138198254200704922769)
              ·
                refine ⟨696853648690650528692077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929138198254200704922769 696853648690650528692077)
                ·
                  refine ⟨261320118258993948259529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696853648690650528692077 261320118258993948259529)
                  ·
                    rfl

theorem cell20_572534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_572534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572534 prefixEnd_572534 := by exact prefixLift 572534
  have htrace : WordTrace (prefixWord ++ tailWord_572534) baseStart_572534 baseEnd_572534 := by
    simpa [prefixWord, tailWord_572534, baseEnd_572534] using wordTrace_append hprefix tailTrace_572534
  have hstable : (prefixWord ++ tailWord_572534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572534).length < 2 ^ (prefixWord ++ tailWord_572534).sum := by decide
  have hdescent : baseEnd_572534 < baseStart_572534 := by decide
  rcases family_descends (prefixWord ++ tailWord_572534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572537 : List Nat := [1, 2, 1, 3, 5, 2, 2, 2, 2]
def baseStart_572537 : Nat := 118140960795 + 572537 * 2 ^ 59
def prefixEnd_572537 : Nat := 4983230072969 + 3 ^ 40 * 572537 * 2
def baseEnd_572537 : Nat := 261321487540739271159517

theorem tailTrace_572537 : CollatzResearch.WordTrace tailWord_572537 prefixEnd_572537 261321487540739271159517 := by
  unfold tailWord_572537
  simp only [CollatzResearch.WordTrace]
  refine ⟨20882139926803705379923865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13921426617869136919949243 20882139926803705379923865)
  ·
    refine ⟨15661604945102779034942899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20882139926803705379923865 15661604945102779034942899)
    ·
      refine ⟨23492407417654168552414349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15661604945102779034942899 23492407417654168552414349)
      ·
        refine ⟨8809652781620313207155381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23492407417654168552414349 8809652781620313207155381)
        ·
          refine ⟨825904948276904363170817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8809652781620313207155381 825904948276904363170817)
          ·
            refine ⟨619428711207678272378113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825904948276904363170817 619428711207678272378113)
            ·
              refine ⟨464571533405758704283585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619428711207678272378113 464571533405758704283585)
              ·
                refine ⟨348428650054319028212689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464571533405758704283585 348428650054319028212689)
                ·
                  refine ⟨261321487540739271159517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348428650054319028212689 261321487540739271159517)
                  ·
                    rfl

theorem cell20_572537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_572537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572537 prefixEnd_572537 := by exact prefixLift 572537
  have htrace : WordTrace (prefixWord ++ tailWord_572537) baseStart_572537 baseEnd_572537 := by
    simpa [prefixWord, tailWord_572537, baseEnd_572537] using wordTrace_append hprefix tailTrace_572537
  have hstable : (prefixWord ++ tailWord_572537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572537).length < 2 ^ (prefixWord ++ tailWord_572537).sum := by decide
  have hdescent : baseEnd_572537 < baseStart_572537 := by decide
  rcases family_descends (prefixWord ++ tailWord_572537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572541 : List Nat := [1, 4, 1, 1, 3, 1, 3, 4, 2]
def baseStart_572541 : Nat := 118140960795 + 572541 * 2 ^ 59
def prefixEnd_572541 : Nat := 4983230072969 + 3 ^ 40 * 572541 * 2
def baseEnd_572541 : Nat := 261323313249733035026167

theorem tailTrace_572541 : CollatzResearch.WordTrace tailWord_572541 prefixEnd_572541 261323313249733035026167 := by
  unfold tailWord_572541
  simp only [CollatzResearch.WordTrace]
  refine ⟨20882285818789214063069477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13921523879192809375379651 20882285818789214063069477)
  ·
    refine ⟨3915428591022977636825527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20882285818789214063069477 3915428591022977636825527)
    ·
      refine ⟨5873142886534466455238291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3915428591022977636825527 5873142886534466455238291)
      ·
        refine ⟨8809714329801699682857437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873142886534466455238291 8809714329801699682857437)
        ·
          refine ⟨3303642873675637381071539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8809714329801699682857437 3303642873675637381071539)
          ·
            refine ⟨4955464310513456071607309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303642873675637381071539 4955464310513456071607309)
            ·
              refine ⟨1858299116442546026852741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4955464310513456071607309 1858299116442546026852741)
              ·
                refine ⟨348431084332977380034889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1858299116442546026852741 348431084332977380034889)
                ·
                  refine ⟨261323313249733035026167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348431084332977380034889 261323313249733035026167)
                  ·
                    rfl

theorem cell20_572541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_572541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572541 prefixEnd_572541 := by exact prefixLift 572541
  have htrace : WordTrace (prefixWord ++ tailWord_572541) baseStart_572541 baseEnd_572541 := by
    simpa [prefixWord, tailWord_572541, baseEnd_572541] using wordTrace_append hprefix tailTrace_572541
  have hstable : (prefixWord ++ tailWord_572541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572541).length < 2 ^ (prefixWord ++ tailWord_572541).sum := by decide
  have hdescent : baseEnd_572541 < baseStart_572541 := by decide
  rcases family_descends (prefixWord ++ tailWord_572541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572548 : List Nat := [2, 3, 2, 1, 2, 4, 1, 5]
def baseStart_572548 : Nat := 118140960795 + 572548 * 2 ^ 59
def prefixEnd_572548 : Nat := 4983230072969 + 3 ^ 40 * 572548 * 2
def baseEnd_572548 : Nat := 87108836080157373930935

theorem tailTrace_572548 : CollatzResearch.WordTrace tailWord_572548 prefixEnd_572548 87108836080157373930935 := by
  unfold tailWord_572548
  simp only [CollatzResearch.WordTrace]
  refine ⟨10441270564881927129287149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13921694086509236172382865 10441270564881927129287149)
  ·
    refine ⟨3915476461830722673482681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10441270564881927129287149 3915476461830722673482681)
    ·
      refine ⟨2936607346373042005112011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3915476461830722673482681 2936607346373042005112011)
      ·
        refine ⟨4404911019559563007668017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936607346373042005112011 4404911019559563007668017)
        ·
          refine ⟨3303683264669672255751013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4404911019559563007668017 3303683264669672255751013)
          ·
            refine ⟨619440612125563547953315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3303683264669672255751013 619440612125563547953315)
            ·
              refine ⟨929160918188345321929973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619440612125563547953315 929160918188345321929973)
              ·
                refine ⟨87108836080157373930935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 929160918188345321929973 87108836080157373930935)
                ·
                  rfl

theorem cell20_572548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_572548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572548 prefixEnd_572548 := by exact prefixLift 572548
  have htrace : WordTrace (prefixWord ++ tailWord_572548) baseStart_572548 baseEnd_572548 := by
    simpa [prefixWord, tailWord_572548, baseEnd_572548] using wordTrace_append hprefix tailTrace_572548
  have hstable : (prefixWord ++ tailWord_572548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572548).length < 2 ^ (prefixWord ++ tailWord_572548).sum := by decide
  have hdescent : baseEnd_572548 < baseStart_572548 := by decide
  rcases family_descends (prefixWord ++ tailWord_572548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572562 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_572562 : Nat := 118140960795 + 572562 * 2 ^ 59
def prefixEnd_572562 : Nat := 4983230072969 + 3 ^ 40 * 572562 * 2
def baseEnd_572562 : Nat := 261332898221950295326081

theorem tailTrace_572562 : CollatzResearch.WordTrace tailWord_572562 prefixEnd_572562 261332898221950295326081 := by
  unfold tailWord_572562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5220762937928283662395985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13922034501142089766389293 5220762937928283662395985)
  ·
    refine ⟨3915572203446212746796989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5220762937928283662395985 3915572203446212746796989)
    ·
      refine ⟨1468339576292329780048871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3915572203446212746796989 1468339576292329780048871)
      ·
        refine ⟨2202509364438494670073307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468339576292329780048871 2202509364438494670073307)
        ·
          refine ⟨3303764046657742005109961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202509364438494670073307 3303764046657742005109961)
          ·
            refine ⟨2477823034993306503832471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3303764046657742005109961 2477823034993306503832471)
            ·
              refine ⟨3716734552489959755748707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477823034993306503832471 3716734552489959755748707)
              ·
                refine ⟨5575101828734939633623061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716734552489959755748707 5575101828734939633623061)
                ·
                  refine ⟨261332898221950295326081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5575101828734939633623061 261332898221950295326081)
                  ·
                    rfl

theorem cell20_572562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_572562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572562 prefixEnd_572562 := by exact prefixLift 572562
  have htrace : WordTrace (prefixWord ++ tailWord_572562) baseStart_572562 baseEnd_572562 := by
    simpa [prefixWord, tailWord_572562, baseEnd_572562] using wordTrace_append hprefix tailTrace_572562
  have hstable : (prefixWord ++ tailWord_572562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572562).length < 2 ^ (prefixWord ++ tailWord_572562).sum := by decide
  have hdescent : baseEnd_572562 < baseStart_572562 := by decide
  rcases family_descends (prefixWord ++ tailWord_572562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572576 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 5]
def baseStart_572576 : Nat := 118140960795 + 572576 * 2 ^ 59
def prefixEnd_572576 : Nat := 4983230072969 + 3 ^ 40 * 572576 * 2
def baseEnd_572576 : Nat := 261339288203428468859357

theorem tailTrace_572576 : CollatzResearch.WordTrace tailWord_572576 prefixEnd_572576 261339288203428468859357 := by
  unfold tailWord_572576
  simp only [CollatzResearch.WordTrace]
  refine ⟨10441781186831207520296791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13922374915774943360395721 10441781186831207520296791)
  ·
    refine ⟨15662671780246811280445187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10441781186831207520296791 15662671780246811280445187)
    ·
      refine ⟨23494007670370216920667781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15662671780246811280445187 23494007670370216920667781)
      ·
        refine ⟨4405126438194415672625209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23494007670370216920667781 4405126438194415672625209)
        ·
          refine ⟨3303844828645811754468907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4405126438194415672625209 3303844828645811754468907)
          ·
            refine ⟨4955767242968717631703361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303844828645811754468907 4955767242968717631703361)
            ·
              refine ⟨3716825432226538223777521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4955767242968717631703361 3716825432226538223777521)
              ·
                refine ⟨2787619074169903667833141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3716825432226538223777521 2787619074169903667833141)
                ·
                  refine ⟨261339288203428468859357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2787619074169903667833141 261339288203428468859357)
                  ·
                    rfl

theorem cell20_572576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_572576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572576 prefixEnd_572576 := by exact prefixLift 572576
  have htrace : WordTrace (prefixWord ++ tailWord_572576) baseStart_572576 baseEnd_572576 := by
    simpa [prefixWord, tailWord_572576, baseEnd_572576] using wordTrace_append hprefix tailTrace_572576
  have hstable : (prefixWord ++ tailWord_572576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572576).length < 2 ^ (prefixWord ++ tailWord_572576).sum := by decide
  have hdescent : baseEnd_572576 < baseStart_572576 := by decide
  rcases family_descends (prefixWord ++ tailWord_572576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572586 : List Nat := [3, 1, 5, 1, 1, 2, 7]
def baseStart_572586 : Nat := 118140960795 + 572586 * 2 ^ 59
def prefixEnd_572586 : Nat := 4983230072969 + 3 ^ 40 * 572586 * 2
def baseEnd_572586 : Nat := 29038205830656986502887

theorem tailTrace_572586 : CollatzResearch.WordTrace tailWord_572586 prefixEnd_572586 29038205830656986502887 := by
  unfold tailWord_572586
  simp only [CollatzResearch.WordTrace]
  refine ⟨5220981775906546687114403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13922618069084124498971741 5220981775906546687114403)
  ·
    refine ⟨7831472663859820030671605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5220981775906546687114403 7831472663859820030671605)
    ·
      refine ⟨734200562236858127875463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7831472663859820030671605 734200562236858127875463)
      ·
        refine ⟨1101300843355287191813195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734200562236858127875463 1101300843355287191813195)
        ·
          refine ⟨1651951265032930787719793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101300843355287191813195 1651951265032930787719793)
          ·
            refine ⟨1238963448774698090789845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1651951265032930787719793 1238963448774698090789845)
            ·
              refine ⟨29038205830656986502887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1238963448774698090789845 29038205830656986502887)
              ·
                rfl

theorem cell20_572586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 7].length) (baseStart_572586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572586 prefixEnd_572586 := by exact prefixLift 572586
  have htrace : WordTrace (prefixWord ++ tailWord_572586) baseStart_572586 baseEnd_572586 := by
    simpa [prefixWord, tailWord_572586, baseEnd_572586] using wordTrace_append hprefix tailTrace_572586
  have hstable : (prefixWord ++ tailWord_572586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572586).length < 2 ^ (prefixWord ++ tailWord_572586).sum := by decide
  have hdescent : baseEnd_572586 < baseStart_572586 := by decide
  rcases family_descends (prefixWord ++ tailWord_572586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572589 : List Nat := [1, 5, 2, 1, 3, 2, 1, 2, 3]
def baseStart_572589 : Nat := 118140960795 + 572589 * 2 ^ 59
def prefixEnd_572589 : Nat := 4983230072969 + 3 ^ 40 * 572589 * 2
def baseEnd_572589 : Nat := 261345221757658201425971

theorem tailTrace_572589 : CollatzResearch.WordTrace tailWord_572589 prefixEnd_572589 261345221757658201425971 := by
  unfold tailWord_572589
  simp only [CollatzResearch.WordTrace]
  refine ⟨20884036522615318260816821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13922691015076878840544547 20884036522615318260816821)
  ·
    refine ⟨1957878423995186086951577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20884036522615318260816821 1957878423995186086951577)
    ·
      refine ⟨1468408817996389565213683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1957878423995186086951577 1468408817996389565213683)
      ·
        refine ⟨2202613226994584347820525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468408817996389565213683 2202613226994584347820525)
        ·
          refine ⟨825979960122969130432697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2202613226994584347820525 825979960122969130432697)
          ·
            refine ⟨619484970092226847824523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825979960122969130432697 619484970092226847824523)
            ·
              refine ⟨929227455138340271736785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619484970092226847824523 929227455138340271736785)
              ·
                refine ⟨696920591353755203802589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929227455138340271736785 696920591353755203802589)
                ·
                  refine ⟨261345221757658201425971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 696920591353755203802589 261345221757658201425971)
                  ·
                    rfl

theorem cell20_572589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_572589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572589 prefixEnd_572589 := by exact prefixLift 572589
  have htrace : WordTrace (prefixWord ++ tailWord_572589) baseStart_572589 baseEnd_572589 := by
    simpa [prefixWord, tailWord_572589, baseEnd_572589] using wordTrace_append hprefix tailTrace_572589
  have hstable : (prefixWord ++ tailWord_572589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572589).length < 2 ^ (prefixWord ++ tailWord_572589).sum := by decide
  have hdescent : baseEnd_572589 < baseStart_572589 := by decide
  rcases family_descends (prefixWord ++ tailWord_572589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572593 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_572593 : Nat := 118140960795 + 572593 * 2 ^ 59
def prefixEnd_572593 : Nat := 4983230072969 + 3 ^ 40 * 572593 * 2
def baseEnd_572593 : Nat := 261347047466651965292621

theorem tailTrace_572593 : CollatzResearch.WordTrace tailWord_572593 prefixEnd_572593 261347047466651965292621 := by
  unfold tailWord_572593
  simp only [CollatzResearch.WordTrace]
  refine ⟨20884182414600826943962433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13922788276400551295974955 20884182414600826943962433)
  ·
    refine ⟨15663136810950620207971825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20884182414600826943962433 15663136810950620207971825)
    ·
      refine ⟨11747352608212965155978869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15663136810950620207971825 11747352608212965155978869)
      ·
        refine ⟨1101314307019965483373019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11747352608212965155978869 1101314307019965483373019)
        ·
          refine ⟨1651971460529948225059529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101314307019965483373019 1651971460529948225059529)
          ·
            refine ⟨1238978595397461168794647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1651971460529948225059529 1238978595397461168794647)
            ·
              refine ⟨1858467893096191753191971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238978595397461168794647 1858467893096191753191971)
              ·
                refine ⟨2787701839644287629787957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858467893096191753191971 2787701839644287629787957)
                ·
                  refine ⟨261347047466651965292621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2787701839644287629787957 261347047466651965292621)
                  ·
                    rfl

theorem cell20_572593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_572593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572593 prefixEnd_572593 := by exact prefixLift 572593
  have htrace : WordTrace (prefixWord ++ tailWord_572593) baseStart_572593 baseEnd_572593 := by
    simpa [prefixWord, tailWord_572593, baseEnd_572593] using wordTrace_append hprefix tailTrace_572593
  have hstable : (prefixWord ++ tailWord_572593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572593).length < 2 ^ (prefixWord ++ tailWord_572593).sum := by decide
  have hdescent : baseEnd_572593 < baseStart_572593 := by decide
  rcases family_descends (prefixWord ++ tailWord_572593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572630 : List Nat := [5, 2, 1, 2, 2, 2, 1, 3, 2]
def baseStart_572630 : Nat := 118140960795 + 572630 * 2 ^ 59
def prefixEnd_572630 : Nat := 4983230072969 + 3 ^ 40 * 572630 * 2
def baseEnd_572630 : Nat := 261363935274844281059137

theorem tailTrace_572630 : CollatzResearch.WordTrace tailWord_572630 prefixEnd_572630 261363935274844281059137 := by
  unfold tailWord_572630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305345744716673891441209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13923687943644521508706229 1305345744716673891441209)
  ·
    refine ⟨979009308537505418580907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1305345744716673891441209 979009308537505418580907)
    ·
      refine ⟨1468513962806258127871361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 979009308537505418580907 1468513962806258127871361)
      ·
        refine ⟨1101385472104693595903521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1468513962806258127871361 1101385472104693595903521)
        ·
          refine ⟨826039104078520196927641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1101385472104693595903521 826039104078520196927641)
          ·
            refine ⟨619529328058890147695731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826039104078520196927641 619529328058890147695731)
            ·
              refine ⟨929293992088335221543597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619529328058890147695731 929293992088335221543597)
              ·
                refine ⟨348485247033125708078849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 929293992088335221543597 348485247033125708078849)
                ·
                  refine ⟨261363935274844281059137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348485247033125708078849 261363935274844281059137)
                  ·
                    rfl

theorem cell20_572630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_572630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572630 prefixEnd_572630 := by exact prefixLift 572630
  have htrace : WordTrace (prefixWord ++ tailWord_572630) baseStart_572630 baseEnd_572630 := by
    simpa [prefixWord, tailWord_572630, baseEnd_572630] using wordTrace_append hprefix tailTrace_572630
  have hstable : (prefixWord ++ tailWord_572630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572630).length < 2 ^ (prefixWord ++ tailWord_572630).sum := by decide
  have hdescent : baseEnd_572630 < baseStart_572630 := by decide
  rcases family_descends (prefixWord ++ tailWord_572630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572652 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 5]
def baseStart_572652 : Nat := 118140960795 + 572652 * 2 ^ 59
def prefixEnd_572652 : Nat := 4983230072969 + 3 ^ 40 * 572652 * 2
def baseEnd_572652 : Nat := 261373976674309982325713

theorem tailTrace_572652 : CollatzResearch.WordTrace tailWord_572652 prefixEnd_572652 261373976674309982325713 := by
  unfold tailWord_572652
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443167160693540010180105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13924222880924720013573473 10443167160693540010180105)
  ·
    refine ⟨7832375370520155007635079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10443167160693540010180105 7832375370520155007635079)
    ·
      refine ⟨11748563055780232511452619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7832375370520155007635079 11748563055780232511452619)
      ·
        refine ⟨17622844583670348767178929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11748563055780232511452619 17622844583670348767178929)
        ·
          refine ⟨13217133437752761575384197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17622844583670348767178929 13217133437752761575384197)
          ·
            refine ⟨2478212519578642795384537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13217133437752761575384197 2478212519578642795384537)
            ·
              refine ⟨1858659389683982096538403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2478212519578642795384537 1858659389683982096538403)
              ·
                refine ⟨2787989084525973144807605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858659389683982096538403 2787989084525973144807605)
                ·
                  refine ⟨261373976674309982325713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2787989084525973144807605 261373976674309982325713)
                  ·
                    rfl

theorem cell20_572652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_572652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572652 prefixEnd_572652 := by exact prefixLift 572652
  have htrace : WordTrace (prefixWord ++ tailWord_572652) baseStart_572652 baseEnd_572652 := by
    simpa [prefixWord, tailWord_572652, baseEnd_572652] using wordTrace_append hprefix tailTrace_572652
  have hstable : (prefixWord ++ tailWord_572652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572652).length < 2 ^ (prefixWord ++ tailWord_572652).sum := by decide
  have hdescent : baseEnd_572652 < baseStart_572652 := by decide
  rcases family_descends (prefixWord ++ tailWord_572652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572655 : List Nat := [1, 1, 2, 1, 7, 2, 1, 1, 4]
def baseStart_572655 : Nat := 118140960795 + 572655 * 2 ^ 59
def prefixEnd_572655 : Nat := 4983230072969 + 3 ^ 40 * 572655 * 2
def baseEnd_572655 : Nat := 261375345956055305225701

theorem tailTrace_572655 : CollatzResearch.WordTrace tailWord_572655 prefixEnd_572655 261375345956055305225701 := by
  unfold tailWord_572655
  simp only [CollatzResearch.WordTrace]
  refine ⟨20886443740376211532719419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13924295826917474355146279 20886443740376211532719419)
  ·
    refine ⟨31329665610564317299079129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20886443740376211532719419 31329665610564317299079129)
    ·
      refine ⟨23497249207923237974309347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31329665610564317299079129 23497249207923237974309347)
      ·
        refine ⟨35245873811884856961464021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23497249207923237974309347 35245873811884856961464021)
        ·
          refine ⟨826075167466051335034313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 35245873811884856961464021 826075167466051335034313)
          ·
            refine ⟨619556375599538501275735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826075167466051335034313 619556375599538501275735)
            ·
              refine ⟨929334563399307751913603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619556375599538501275735 929334563399307751913603)
              ·
                refine ⟨1394001845098961627870405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929334563399307751913603 1394001845098961627870405)
                ·
                  refine ⟨261375345956055305225701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394001845098961627870405 261375345956055305225701)
                  ·
                    rfl

theorem cell20_572655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 1, 4].length) (baseStart_572655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572655 prefixEnd_572655 := by exact prefixLift 572655
  have htrace : WordTrace (prefixWord ++ tailWord_572655) baseStart_572655 baseEnd_572655 := by
    simpa [prefixWord, tailWord_572655, baseEnd_572655] using wordTrace_append hprefix tailTrace_572655
  have hstable : (prefixWord ++ tailWord_572655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572655).length < 2 ^ (prefixWord ++ tailWord_572655).sum := by decide
  have hdescent : baseEnd_572655 < baseStart_572655 := by decide
  rcases family_descends (prefixWord ++ tailWord_572655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572704 : List Nat := [2, 1, 1, 5, 11]
def baseStart_572704 : Nat := 118140960795 + 572704 * 2 ^ 59
def prefixEnd_572704 : Nat := 4983230072969 + 3 ^ 40 * 572704 * 2
def baseEnd_572704 : Nat := 3227132233225048303607

theorem tailTrace_572704 : CollatzResearch.WordTrace tailWord_572704 prefixEnd_572704 3227132233225048303607 := by
  unfold tailWord_572704
  simp only [CollatzResearch.WordTrace]
  refine ⟨10444115458599346450626583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13925487278132461934168777 10444115458599346450626583)
  ·
    refine ⟨15666173187899019675939875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10444115458599346450626583 15666173187899019675939875)
    ·
      refine ⟨23499259781848529513909813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15666173187899019675939875 23499259781848529513909813)
      ·
        refine ⟨2203055604548299641929045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23499259781848529513909813 2203055604548299641929045)
        ·
          refine ⟨3227132233225048303607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2203055604548299641929045 3227132233225048303607)
          ·
            rfl

theorem cell20_572704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 11].length) (baseStart_572704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572704 prefixEnd_572704 := by exact prefixLift 572704
  have htrace : WordTrace (prefixWord ++ tailWord_572704) baseStart_572704 baseEnd_572704 := by
    simpa [prefixWord, tailWord_572704, baseEnd_572704] using wordTrace_append hprefix tailTrace_572704
  have hstable : (prefixWord ++ tailWord_572704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572704).length < 2 ^ (prefixWord ++ tailWord_572704).sum := by decide
  have hdescent : baseEnd_572704 < baseStart_572704 := by decide
  rcases family_descends (prefixWord ++ tailWord_572704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572706 : List Nat := [3, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_572706 : Nat := 118140960795 + 572706 * 2 ^ 59
def prefixEnd_572706 : Nat := 4983230072969 + 3 ^ 40 * 572706 * 2
def baseEnd_572706 : Nat := 261398623745725794525493

theorem tailTrace_572706 : CollatzResearch.WordTrace tailWord_572706 prefixEnd_572706 261398623745725794525493 := by
  unfold tailWord_572706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222075965797861810706493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13925535908794298161883981 5222075965797861810706493)
  ·
    refine ⟨1958278487174198179014935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5222075965797861810706493 1958278487174198179014935)
    ·
      refine ⟨2937417730761297268522403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958278487174198179014935 2937417730761297268522403)
      ·
        refine ⟨4406126596141945902783605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937417730761297268522403 4406126596141945902783605)
        ·
          refine ⟨413074368388307428385963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4406126596141945902783605 413074368388307428385963)
          ·
            refine ⟨619611552582461142578945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413074368388307428385963 619611552582461142578945)
            ·
              refine ⟨464708664436845856934209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619611552582461142578945 464708664436845856934209)
              ·
                refine ⟨348531498327634392700657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464708664436845856934209 348531498327634392700657)
                ·
                  refine ⟨261398623745725794525493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348531498327634392700657 261398623745725794525493)
                  ·
                    rfl

theorem cell20_572706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_572706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572706 prefixEnd_572706 := by exact prefixLift 572706
  have htrace : WordTrace (prefixWord ++ tailWord_572706) baseStart_572706 baseEnd_572706 := by
    simpa [prefixWord, tailWord_572706, baseEnd_572706] using wordTrace_append hprefix tailTrace_572706
  have hstable : (prefixWord ++ tailWord_572706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572706).length < 2 ^ (prefixWord ++ tailWord_572706).sum := by decide
  have hdescent : baseEnd_572706 < baseStart_572706 := by decide
  rcases family_descends (prefixWord ++ tailWord_572706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572707 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 3]
def baseStart_572707 : Nat := 118140960795 + 572707 * 2 ^ 59
def prefixEnd_572707 : Nat := 4983230072969 + 3 ^ 40 * 572707 * 2
def baseEnd_572707 : Nat := 261399080172974235492155

theorem tailTrace_572707 : CollatzResearch.WordTrace tailWord_572707 prefixEnd_572707 261399080172974235492155 := by
  unfold tailWord_572707
  simp only [CollatzResearch.WordTrace]
  refine ⟨20888340336187824413612375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13925560224125216275741583 20888340336187824413612375)
  ·
    refine ⟨31332510504281736620418563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20888340336187824413612375 31332510504281736620418563)
    ·
      refine ⟨46998765756422604930627845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31332510504281736620418563 46998765756422604930627845)
      ·
        refine ⟨8812268579329238424492721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46998765756422604930627845 8812268579329238424492721)
        ·
          refine ⟨6609201434496928818369541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8812268579329238424492721 6609201434496928818369541)
          ·
            refine ⟨1239225268968174153444289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6609201434496928818369541 1239225268968174153444289)
            ·
              refine ⟨929418951726130615083217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1239225268968174153444289 929418951726130615083217)
              ·
                refine ⟨697064213794597961312413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929418951726130615083217 697064213794597961312413)
                ·
                  refine ⟨261399080172974235492155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697064213794597961312413 261399080172974235492155)
                  ·
                    rfl

theorem cell20_572707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 3].length) (baseStart_572707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572707 prefixEnd_572707 := by exact prefixLift 572707
  have htrace : WordTrace (prefixWord ++ tailWord_572707) baseStart_572707 baseEnd_572707 := by
    simpa [prefixWord, tailWord_572707, baseEnd_572707] using wordTrace_append hprefix tailTrace_572707
  have hstable : (prefixWord ++ tailWord_572707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572707).length < 2 ^ (prefixWord ++ tailWord_572707).sum := by decide
  have hdescent : baseEnd_572707 < baseStart_572707 := by decide
  rcases family_descends (prefixWord ++ tailWord_572707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572717 : List Nat := [1, 5, 3, 1, 1, 3, 1, 5]
def baseStart_572717 : Nat := 118140960795 + 572717 * 2 ^ 59
def prefixEnd_572717 : Nat := 4983230072969 + 3 ^ 40 * 572717 * 2
def baseEnd_572717 : Nat := 87134548148486215052927

theorem tailTrace_572717 : CollatzResearch.WordTrace tailWord_572717 prefixEnd_572717 87134548148486215052927 := by
  unfold tailWord_572717
  simp only [CollatzResearch.WordTrace]
  refine ⟨20888705066151596121476405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13925803377434397414317603 20888705066151596121476405)
  ·
    refine ⟨1958316099951712136388413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20888705066151596121476405 1958316099951712136388413)
    ·
      refine ⟨734368537481892051145655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1958316099951712136388413 734368537481892051145655)
      ·
        refine ⟨1101552806222838076718483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734368537481892051145655 1101552806222838076718483)
        ·
          refine ⟨1652329209334257115077725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101552806222838076718483 1652329209334257115077725)
          ·
            refine ⟨619623453500346418154147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1652329209334257115077725 619623453500346418154147)
            ·
              refine ⟨929435180250519627231221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619623453500346418154147 929435180250519627231221)
              ·
                refine ⟨87134548148486215052927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 929435180250519627231221 87134548148486215052927)
                ·
                  rfl

theorem cell20_572717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_572717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572717 prefixEnd_572717 := by exact prefixLift 572717
  have htrace : WordTrace (prefixWord ++ tailWord_572717) baseStart_572717 baseEnd_572717 := by
    simpa [prefixWord, tailWord_572717, baseEnd_572717] using wordTrace_append hprefix tailTrace_572717
  have hstable : (prefixWord ++ tailWord_572717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572717).length < 2 ^ (prefixWord ++ tailWord_572717).sum := by decide
  have hdescent : baseEnd_572717 < baseStart_572717 := by decide
  rcases family_descends (prefixWord ++ tailWord_572717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572721 : List Nat := [1, 2, 2, 3, 3, 1, 3, 5]
def baseStart_572721 : Nat := 118140960795 + 572721 * 2 ^ 59
def prefixEnd_572721 : Nat := 4983230072969 + 3 ^ 40 * 572721 * 2
def baseEnd_572721 : Nat := 87135156718150803008477

theorem tailTrace_572721 : CollatzResearch.WordTrace tailWord_572721 prefixEnd_572721 87135156718150803008477 := by
  unfold tailWord_572721
  simp only [CollatzResearch.WordTrace]
  refine ⟨20888850958137104804622017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13925900638758069869748011 20888850958137104804622017)
  ·
    refine ⟨15666638218602828603466513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20888850958137104804622017 15666638218602828603466513)
    ·
      refine ⟨11749978663952121452599885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15666638218602828603466513 11749978663952121452599885)
      ·
        refine ⟨4406241998982045544724957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11749978663952121452599885 4406241998982045544724957)
        ·
          refine ⟨1652340749618267079271859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4406241998982045544724957 1652340749618267079271859)
          ·
            refine ⟨2478511124427400618907789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652340749618267079271859 2478511124427400618907789)
            ·
              refine ⟨929441671660275232090421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2478511124427400618907789 929441671660275232090421)
              ·
                refine ⟨87135156718150803008477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 929441671660275232090421 87135156718150803008477)
                ·
                  rfl

theorem cell20_572721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_572721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572721 prefixEnd_572721 := by exact prefixLift 572721
  have htrace : WordTrace (prefixWord ++ tailWord_572721) baseStart_572721 baseEnd_572721 := by
    simpa [prefixWord, tailWord_572721, baseEnd_572721] using wordTrace_append hprefix tailTrace_572721
  have hstable : (prefixWord ++ tailWord_572721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572721).length < 2 ^ (prefixWord ++ tailWord_572721).sum := by decide
  have hdescent : baseEnd_572721 < baseStart_572721 := by decide
  rcases family_descends (prefixWord ++ tailWord_572721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572735 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_572735 : Nat := 118140960795 + 572735 * 2 ^ 59
def prefixEnd_572735 : Nat := 4983230072969 + 3 ^ 40 * 572735 * 2
def baseEnd_572735 : Nat := 261411860135930582558707

theorem tailTrace_572735 : CollatzResearch.WordTrace tailWord_572735 prefixEnd_572735 261411860135930582558707 := by
  unfold tailWord_572735
  simp only [CollatzResearch.WordTrace]
  refine ⟨20889361580086385195631659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13926241053390923463754439 20889361580086385195631659)
  ·
    refine ⟨31334042370129577793447489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20889361580086385195631659 31334042370129577793447489)
    ·
      refine ⟨23500531777597183345085617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31334042370129577793447489 23500531777597183345085617)
      ·
        refine ⟨17625398833197887508814213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23500531777597183345085617 17625398833197887508814213)
        ·
          refine ⟨3304762281224603907902665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17625398833197887508814213 3304762281224603907902665)
          ·
            refine ⟨2478571710918452930926999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3304762281224603907902665 2478571710918452930926999)
            ·
              refine ⟨3717857566377679396390499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478571710918452930926999 3717857566377679396390499)
              ·
                refine ⟨5576786349566519094585749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717857566377679396390499 5576786349566519094585749)
                ·
                  refine ⟨261411860135930582558707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5576786349566519094585749 261411860135930582558707)
                  ·
                    rfl

theorem cell20_572735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_572735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572735 prefixEnd_572735 := by exact prefixLift 572735
  have htrace : WordTrace (prefixWord ++ tailWord_572735) baseStart_572735 baseEnd_572735 := by
    simpa [prefixWord, tailWord_572735, baseEnd_572735] using wordTrace_append hprefix tailTrace_572735
  have hstable : (prefixWord ++ tailWord_572735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572735).length < 2 ^ (prefixWord ++ tailWord_572735).sum := by decide
  have hdescent : baseEnd_572735 < baseStart_572735 := by decide
  rcases family_descends (prefixWord ++ tailWord_572735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572758 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_572758 : Nat := 118140960795 + 572758 * 2 ^ 59
def prefixEnd_572758 : Nat := 4983230072969 + 3 ^ 40 * 572758 * 2
def baseEnd_572758 : Nat := 261422357962644724791947

theorem tailTrace_572758 : CollatzResearch.WordTrace tailWord_572758 prefixEnd_572758 261422357962644724791947 := by
  unfold tailWord_572758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305637528687691257732433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13926800306002040082479285 1305637528687691257732433)
  ·
    refine ⟨979228146515768443299325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1305637528687691257732433 979228146515768443299325)
    ·
      refine ⟨367210554943413166237247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 979228146515768443299325 367210554943413166237247)
      ·
        refine ⟨550815832415119749355871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367210554943413166237247 550815832415119749355871)
        ·
          refine ⟨826223748622679624033807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550815832415119749355871 826223748622679624033807)
          ·
            refine ⟨1239335622934019436050711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826223748622679624033807 1239335622934019436050711)
            ·
              refine ⟨1859003434401029154076067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239335622934019436050711 1859003434401029154076067)
              ·
                refine ⟨2788505151601543731114101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859003434401029154076067 2788505151601543731114101)
                ·
                  refine ⟨261422357962644724791947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2788505151601543731114101 261422357962644724791947)
                  ·
                    rfl

theorem cell20_572758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_572758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572758 prefixEnd_572758 := by exact prefixLift 572758
  have htrace : WordTrace (prefixWord ++ tailWord_572758) baseStart_572758 baseEnd_572758 := by
    simpa [prefixWord, tailWord_572758, baseEnd_572758] using wordTrace_append hprefix tailTrace_572758
  have hstable : (prefixWord ++ tailWord_572758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572758).length < 2 ^ (prefixWord ++ tailWord_572758).sum := by decide
  have hdescent : baseEnd_572758 < baseStart_572758 := by decide
  rcases family_descends (prefixWord ++ tailWord_572758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572765 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 4]
def baseStart_572765 : Nat := 118140960795 + 572765 * 2 ^ 59
def prefixEnd_572765 : Nat := 4983230072969 + 3 ^ 40 * 572765 * 2
def baseEnd_572765 : Nat := 261425552953383811558585

theorem tailTrace_572765 : CollatzResearch.WordTrace tailWord_572765 prefixEnd_572765 261425552953383811558585 := by
  unfold tailWord_572765
  simp only [CollatzResearch.WordTrace]
  refine ⟨20890455769977700319223749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13926970513318466879482499 20890455769977700319223749)
  ·
    refine ⟨3916960456870818809854453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20890455769977700319223749 3916960456870818809854453)
    ·
      refine ⟨367215042831639263423855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3916960456870818809854453 367215042831639263423855)
      ·
        refine ⟨550822564247458895135783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367215042831639263423855 550822564247458895135783)
        ·
          refine ⟨826233846371188342703675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550822564247458895135783 826233846371188342703675)
          ·
            refine ⟨1239350769556782514055513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826233846371188342703675 1239350769556782514055513)
            ·
              refine ⟨929513077167586885541635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1239350769556782514055513 929513077167586885541635)
              ·
                refine ⟨1394269615751380328312453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929513077167586885541635 1394269615751380328312453)
                ·
                  refine ⟨261425552953383811558585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394269615751380328312453 261425552953383811558585)
                  ·
                    rfl

theorem cell20_572765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_572765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572765 prefixEnd_572765 := by exact prefixLift 572765
  have htrace : WordTrace (prefixWord ++ tailWord_572765) baseStart_572765 baseEnd_572765 := by
    simpa [prefixWord, tailWord_572765, baseEnd_572765] using wordTrace_append hprefix tailTrace_572765
  have hstable : (prefixWord ++ tailWord_572765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572765).length < 2 ^ (prefixWord ++ tailWord_572765).sum := by decide
  have hdescent : baseEnd_572765 < baseStart_572765 := by decide
  rcases family_descends (prefixWord ++ tailWord_572765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572783 : List Nat := [1, 1, 2, 1, 3, 1, 7, 1, 3]
def baseStart_572783 : Nat := 118140960795 + 572783 * 2 ^ 59
def prefixEnd_572783 : Nat := 4983230072969 + 3 ^ 40 * 572783 * 2
def baseEnd_572783 : Nat := 261433768643855748958511

theorem tailTrace_572783 : CollatzResearch.WordTrace tailWord_572783 prefixEnd_572783 261433768643855748958511 := by
  unfold tailWord_572783
  simp only [CollatzResearch.WordTrace]
  refine ⟨20891112283912489393379003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13927408189274992928919335 20891112283912489393379003)
  ·
    refine ⟨31336668425868734090068505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20891112283912489393379003 31336668425868734090068505)
    ·
      refine ⟨23502501319401550567551379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31336668425868734090068505 23502501319401550567551379)
      ·
        refine ⟨35253751979102325851327069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23502501319401550567551379 35253751979102325851327069)
        ·
          refine ⟨13220156992163372194247651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35253751979102325851327069 13220156992163372194247651)
          ·
            refine ⟨19830235488245058291371477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13220156992163372194247651 19830235488245058291371477)
            ·
              refine ⟨464771144255743553704019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19830235488245058291371477 464771144255743553704019)
              ·
                refine ⟨697156716383615330556029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464771144255743553704019 697156716383615330556029)
                ·
                  refine ⟨261433768643855748958511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697156716383615330556029 261433768643855748958511)
                  ·
                    rfl

theorem cell20_572783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 7, 1, 3].length) (baseStart_572783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572783 prefixEnd_572783 := by exact prefixLift 572783
  have htrace : WordTrace (prefixWord ++ tailWord_572783) baseStart_572783 baseEnd_572783 := by
    simpa [prefixWord, tailWord_572783, baseEnd_572783] using wordTrace_append hprefix tailTrace_572783
  have hstable : (prefixWord ++ tailWord_572783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572783).length < 2 ^ (prefixWord ++ tailWord_572783).sum := by decide
  have hdescent : baseEnd_572783 < baseStart_572783 := by decide
  rcases family_descends (prefixWord ++ tailWord_572783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572787 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 9]
def baseStart_572787 : Nat := 118140960795 + 572787 * 2 ^ 59
def prefixEnd_572787 : Nat := 4983230072969 + 3 ^ 40 * 572787 * 2
def baseEnd_572787 : Nat := 261435594352849512825161

theorem tailTrace_572787 : CollatzResearch.WordTrace tailWord_572787 prefixEnd_572787 261435594352849512825161 := by
  unfold tailWord_572787
  simp only [CollatzResearch.WordTrace]
  refine ⟨20891258175897998076524615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13927505450598665384349743 20891258175897998076524615)
  ·
    refine ⟨31336887263846997114786923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20891258175897998076524615 31336887263846997114786923)
    ·
      refine ⟨47005330895770495672180385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31336887263846997114786923 47005330895770495672180385)
      ·
        refine ⟨35253998171827871754135289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47005330895770495672180385 35253998171827871754135289)
        ·
          refine ⟨26440498628870903815601467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35253998171827871754135289 26440498628870903815601467)
          ·
            refine ⟨39660747943306355723402201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26440498628870903815601467 39660747943306355723402201)
            ·
              refine ⟨29745560957479766792551651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39660747943306355723402201 29745560957479766792551651)
              ·
                refine ⟨44618341436219650188827477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29745560957479766792551651 44618341436219650188827477)
                ·
                  refine ⟨261435594352849512825161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44618341436219650188827477 261435594352849512825161)
                  ·
                    rfl

theorem cell20_572787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_572787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572787 prefixEnd_572787 := by exact prefixLift 572787
  have htrace : WordTrace (prefixWord ++ tailWord_572787) baseStart_572787 baseEnd_572787 := by
    simpa [prefixWord, tailWord_572787, baseEnd_572787] using wordTrace_append hprefix tailTrace_572787
  have hstable : (prefixWord ++ tailWord_572787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572787).length < 2 ^ (prefixWord ++ tailWord_572787).sum := by decide
  have hdescent : baseEnd_572787 < baseStart_572787 := by decide
  rcases family_descends (prefixWord ++ tailWord_572787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572804 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 5]
def baseStart_572804 : Nat := 118140960795 + 572804 * 2 ^ 59
def prefixEnd_572804 : Nat := 4983230072969 + 3 ^ 40 * 572804 * 2
def baseEnd_572804 : Nat := 261443353616073009258425

theorem tailTrace_572804 : CollatzResearch.WordTrace tailWord_572804 prefixEnd_572804 261443353616073009258425 := by
  unfold tailWord_572804
  simp only [CollatzResearch.WordTrace]
  refine ⟨10445939108418204989946733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13927918811224273319928977 10445939108418204989946733)
  ·
    refine ⟨3917227165656826871230025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10445939108418204989946733 3917227165656826871230025)
    ·
      refine ⟨2937920374242620153422519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3917227165656826871230025 2937920374242620153422519)
      ·
        refine ⟨4406880561363930230133779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937920374242620153422519 4406880561363930230133779)
        ·
          refine ⟨6610320842045895345200669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406880561363930230133779 6610320842045895345200669)
          ·
            refine ⟨2478870315767210754450251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6610320842045895345200669 2478870315767210754450251)
            ·
              refine ⟨3718305473650816131675377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478870315767210754450251 3718305473650816131675377)
              ·
                refine ⟨2788729105238112098756533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3718305473650816131675377 2788729105238112098756533)
                ·
                  refine ⟨261443353616073009258425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2788729105238112098756533 261443353616073009258425)
                  ·
                    rfl

theorem cell20_572804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_572804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572804 prefixEnd_572804 := by exact prefixLift 572804
  have htrace : WordTrace (prefixWord ++ tailWord_572804) baseStart_572804 baseEnd_572804 := by
    simpa [prefixWord, tailWord_572804, baseEnd_572804] using wordTrace_append hprefix tailTrace_572804
  have hstable : (prefixWord ++ tailWord_572804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572804).length < 2 ^ (prefixWord ++ tailWord_572804).sum := by decide
  have hdescent : baseEnd_572804 < baseStart_572804 := by decide
  rcases family_descends (prefixWord ++ tailWord_572804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572807 : List Nat := [1, 1, 4, 2, 2, 2, 3, 3, 2]
def baseStart_572807 : Nat := 118140960795 + 572807 * 2 ^ 59
def prefixEnd_572807 : Nat := 4983230072969 + 3 ^ 40 * 572807 * 2
def baseEnd_572807 : Nat := 261444722897818332158413

theorem tailTrace_572807 : CollatzResearch.WordTrace tailWord_572807 prefixEnd_572807 261444722897818332158413 := by
  unfold tailWord_572807
  simp only [CollatzResearch.WordTrace]
  refine ⟨20891987635825541492252675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13927991757217027661501783 20891987635825541492252675)
  ·
    refine ⟨31337981453738312238379013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20891987635825541492252675 31337981453738312238379013)
    ·
      refine ⟨5875871522575933544696065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31337981453738312238379013 5875871522575933544696065)
      ·
        refine ⟨4406903641931950158522049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5875871522575933544696065 4406903641931950158522049)
        ·
          refine ⟨3305177731448962618891537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4406903641931950158522049 3305177731448962618891537)
          ·
            refine ⟨2478883298586721964168653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3305177731448962618891537 2478883298586721964168653)
            ·
              refine ⟨929581236970020736563245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2478883298586721964168653 929581236970020736563245)
              ·
                refine ⟨348592963863757776211217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 929581236970020736563245 348592963863757776211217)
                ·
                  refine ⟨261444722897818332158413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348592963863757776211217 261444722897818332158413)
                  ·
                    rfl

theorem cell20_572807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 2].length) (baseStart_572807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572807 prefixEnd_572807 := by exact prefixLift 572807
  have htrace : WordTrace (prefixWord ++ tailWord_572807) baseStart_572807 baseEnd_572807 := by
    simpa [prefixWord, tailWord_572807, baseEnd_572807] using wordTrace_append hprefix tailTrace_572807
  have hstable : (prefixWord ++ tailWord_572807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572807).length < 2 ^ (prefixWord ++ tailWord_572807).sum := by decide
  have hdescent : baseEnd_572807 < baseStart_572807 := by decide
  rcases family_descends (prefixWord ++ tailWord_572807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572814 : List Nat := [4, 1, 1, 4, 2, 2, 6]
def baseStart_572814 : Nat := 118140960795 + 572814 * 2 ^ 59
def prefixEnd_572814 : Nat := 4983230072969 + 3 ^ 40 * 572814 * 2
def baseEnd_572814 : Nat := 29049768654284157658339

theorem tailTrace_572814 : CollatzResearch.WordTrace tailWord_572814 prefixEnd_572814 29049768654284157658339 := by
  unfold tailWord_572814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611530368350022710969687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13928161964533454458504997 2611530368350022710969687)
  ·
    refine ⟨3917295552525034066454531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2611530368350022710969687 3917295552525034066454531)
    ·
      refine ⟨5875943328787551099681797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3917295552525034066454531 5875943328787551099681797)
      ·
        refine ⟨1101739374147665831190337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5875943328787551099681797 1101739374147665831190337)
        ·
          refine ⟨826304530610749373392753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1101739374147665831190337 826304530610749373392753)
          ·
            refine ⟨619728397958062030044565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826304530610749373392753 619728397958062030044565)
            ·
              refine ⟨29049768654284157658339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 619728397958062030044565 29049768654284157658339)
              ·
                rfl

theorem cell20_572814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 6].length) (baseStart_572814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572814 prefixEnd_572814 := by exact prefixLift 572814
  have htrace : WordTrace (prefixWord ++ tailWord_572814) baseStart_572814 baseEnd_572814 := by
    simpa [prefixWord, tailWord_572814, baseEnd_572814] using wordTrace_append hprefix tailTrace_572814
  have hstable : (prefixWord ++ tailWord_572814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572814).length < 2 ^ (prefixWord ++ tailWord_572814).sum := by decide
  have hdescent : baseEnd_572814 < baseStart_572814 := by decide
  rcases family_descends (prefixWord ++ tailWord_572814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572824 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 4]
def baseStart_572824 : Nat := 118140960795 + 572824 * 2 ^ 59
def prefixEnd_572824 : Nat := 4983230072969 + 3 ^ 40 * 572824 * 2
def baseEnd_572824 : Nat := 261452482161041828591677

theorem tailTrace_572824 : CollatzResearch.WordTrace tailWord_572824 prefixEnd_572824 261452482161041828591677 := by
  unfold tailWord_572824
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446303838381976697810763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13928405117842635597081017 10446303838381976697810763)
  ·
    refine ⟨15669455757572965046716145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10446303838381976697810763 15669455757572965046716145)
    ·
      refine ⟨11752091818179723785037109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15669455757572965046716145 11752091818179723785037109)
      ·
        refine ⟨1101758607954349104847229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11752091818179723785037109 1101758607954349104847229)
        ·
          refine ⟨413159477982880914317711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1101758607954349104847229 413159477982880914317711)
          ·
            refine ⟨619739216974321371476567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413159477982880914317711 619739216974321371476567)
            ·
              refine ⟨929608825461482057214851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619739216974321371476567 929608825461482057214851)
              ·
                refine ⟨1394413238192223085822277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929608825461482057214851 1394413238192223085822277)
                ·
                  refine ⟨261452482161041828591677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394413238192223085822277 261452482161041828591677)
                  ·
                    rfl

theorem cell20_572824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_572824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572824 prefixEnd_572824 := by exact prefixLift 572824
  have htrace : WordTrace (prefixWord ++ tailWord_572824) baseStart_572824 baseEnd_572824 := by
    simpa [prefixWord, tailWord_572824, baseEnd_572824] using wordTrace_append hprefix tailTrace_572824
  have hstable : (prefixWord ++ tailWord_572824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572824).length < 2 ^ (prefixWord ++ tailWord_572824).sum := by decide
  have hdescent : baseEnd_572824 < baseStart_572824 := by decide
  rcases family_descends (prefixWord ++ tailWord_572824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572849 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 6]
def baseStart_572849 : Nat := 118140960795 + 572849 * 2 ^ 59
def prefixEnd_572849 : Nat := 4983230072969 + 3 ^ 40 * 572849 * 2
def baseEnd_572849 : Nat := 261463892842252852758241

theorem tailTrace_572849 : CollatzResearch.WordTrace tailWord_572849 prefixEnd_572849 261463892842252852758241 := by
  unfold tailWord_572849
  simp only [CollatzResearch.WordTrace]
  refine ⟨20893519501673382665281601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13929013001115588443521067 20893519501673382665281601)
  ·
    refine ⟨15670139626255036998961201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20893519501673382665281601 15670139626255036998961201)
    ·
      refine ⟨11752604719691277749220901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15670139626255036998961201 11752604719691277749220901)
      ·
        refine ⟨2203613384942114577978919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11752604719691277749220901 2203613384942114577978919)
        ·
          refine ⟨3305420077413171866968379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203613384942114577978919 3305420077413171866968379)
          ·
            refine ⟨4958130116119757800452569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305420077413171866968379 4958130116119757800452569)
            ·
              refine ⟨3718597587089818350339427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4958130116119757800452569 3718597587089818350339427)
              ·
                refine ⟨5577896380634727525509141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718597587089818350339427 5577896380634727525509141)
                ·
                  refine ⟨261463892842252852758241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5577896380634727525509141 261463892842252852758241)
                  ·
                    rfl

theorem cell20_572849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_572849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572849 prefixEnd_572849 := by exact prefixLift 572849
  have htrace : WordTrace (prefixWord ++ tailWord_572849) baseStart_572849 baseEnd_572849 := by
    simpa [prefixWord, tailWord_572849, baseEnd_572849] using wordTrace_append hprefix tailTrace_572849
  have hstable : (prefixWord ++ tailWord_572849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572849).length < 2 ^ (prefixWord ++ tailWord_572849).sum := by decide
  have hdescent : baseEnd_572849 < baseStart_572849 := by decide
  rcases family_descends (prefixWord ++ tailWord_572849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572856 : List Nat := [2, 1, 2, 1, 2, 2, 4, 6]
def baseStart_572856 : Nat := 118140960795 + 572856 * 2 ^ 59
def prefixEnd_572856 : Nat := 4983230072969 + 3 ^ 40 * 572856 * 2
def baseEnd_572856 : Nat := 87155695944330646508293

theorem tailTrace_572856 : CollatzResearch.WordTrace tailWord_572856 prefixEnd_572856 87155695944330646508293 := by
  unfold tailWord_572856
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446887406324011430393211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13929183208432015240524281 10446887406324011430393211)
  ·
    refine ⟨15670331109486017145589817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10446887406324011430393211 15670331109486017145589817)
    ·
      refine ⟨11752748332114512859192363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15670331109486017145589817 11752748332114512859192363)
      ·
        refine ⟨17629122498171769288788545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11752748332114512859192363 17629122498171769288788545)
        ·
          refine ⟨13221841873628826966591409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17629122498171769288788545 13221841873628826966591409)
          ·
            refine ⟨9916381405221620224943557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13221841873628826966591409 9916381405221620224943557)
            ·
              refine ⟨1859321513479053792176917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9916381405221620224943557 1859321513479053792176917)
              ·
                refine ⟨87155695944330646508293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1859321513479053792176917 87155695944330646508293)
                ·
                  rfl

theorem cell20_572856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_572856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572856 prefixEnd_572856 := by exact prefixLift 572856
  have htrace : WordTrace (prefixWord ++ tailWord_572856) baseStart_572856 baseEnd_572856 := by
    simpa [prefixWord, tailWord_572856, baseEnd_572856] using wordTrace_append hprefix tailTrace_572856
  have hstable : (prefixWord ++ tailWord_572856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572856).length < 2 ^ (prefixWord ++ tailWord_572856).sum := by decide
  have hdescent : baseEnd_572856 < baseStart_572856 := by decide
  rcases family_descends (prefixWord ++ tailWord_572856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572863 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_572863 : Nat := 118140960795 + 572863 * 2 ^ 59
def prefixEnd_572863 : Nat := 4983230072969 + 3 ^ 40 * 572863 * 2
def baseEnd_572863 : Nat := 261470282823731026291517

theorem tailTrace_572863 : CollatzResearch.WordTrace tailWord_572863 prefixEnd_572863 261470282823731026291517 := by
  unfold tailWord_572863
  simp only [CollatzResearch.WordTrace]
  refine ⟨20894030123622663056291243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13929353415748442037527495 20894030123622663056291243)
  ·
    refine ⟨31341045185433994584436865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20894030123622663056291243 31341045185433994584436865)
    ·
      refine ⟨23505783889075495938327649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31341045185433994584436865 23505783889075495938327649)
      ·
        refine ⟨17629337916806621953745737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23505783889075495938327649 17629337916806621953745737)
        ·
          refine ⟨13222003437604966465309303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17629337916806621953745737 13222003437604966465309303)
          ·
            refine ⟨19833005156407449697963955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13222003437604966465309303 19833005156407449697963955)
            ·
              refine ⟨29749507734611174546945933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19833005156407449697963955 29749507734611174546945933)
              ·
                refine ⟨11156065400479190455104725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29749507734611174546945933 11156065400479190455104725)
                ·
                  refine ⟨261470282823731026291517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11156065400479190455104725 261470282823731026291517)
                  ·
                    rfl

theorem cell20_572863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_572863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572863 prefixEnd_572863 := by exact prefixLift 572863
  have htrace : WordTrace (prefixWord ++ tailWord_572863) baseStart_572863 baseEnd_572863 := by
    simpa [prefixWord, tailWord_572863, baseEnd_572863] using wordTrace_append hprefix tailTrace_572863
  have hstable : (prefixWord ++ tailWord_572863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572863).length < 2 ^ (prefixWord ++ tailWord_572863).sum := by decide
  have hdescent : baseEnd_572863 < baseStart_572863 := by decide
  rcases family_descends (prefixWord ++ tailWord_572863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572935 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 3]
def baseStart_572935 : Nat := 118140960795 + 572935 * 2 ^ 59
def prefixEnd_572935 : Nat := 4983230072969 + 3 ^ 40 * 572935 * 2
def baseEnd_572935 : Nat := 261503145585618775891223

theorem tailTrace_572935 : CollatzResearch.WordTrace tailWord_572935 prefixEnd_572935 261503145585618775891223 := by
  unfold tailWord_572935
  simp only [CollatzResearch.WordTrace]
  refine ⟨20896656179361819352912259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13931104119574546235274839 20896656179361819352912259)
  ·
    refine ⟨31344984269042729029368389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20896656179361819352912259 31344984269042729029368389)
    ·
      refine ⟨5877184550445511693006573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31344984269042729029368389 5877184550445511693006573)
      ·
        refine ⟨2203944206417066884877465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5877184550445511693006573 2203944206417066884877465)
        ·
          refine ⟨1652958154812800163658099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2203944206417066884877465 1652958154812800163658099)
          ·
            refine ⟨2479437232219200245487149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652958154812800163658099 2479437232219200245487149)
            ·
              refine ⟨929788962082200092057681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2479437232219200245487149 929788962082200092057681)
              ·
                refine ⟨697341721561650069043261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929788962082200092057681 697341721561650069043261)
                ·
                  refine ⟨261503145585618775891223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697341721561650069043261 261503145585618775891223)
                  ·
                    rfl

theorem cell20_572935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3].length) (baseStart_572935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572935 prefixEnd_572935 := by exact prefixLift 572935
  have htrace : WordTrace (prefixWord ++ tailWord_572935) baseStart_572935 baseEnd_572935 := by
    simpa [prefixWord, tailWord_572935, baseEnd_572935] using wordTrace_append hprefix tailTrace_572935
  have hstable : (prefixWord ++ tailWord_572935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572935).length < 2 ^ (prefixWord ++ tailWord_572935).sum := by decide
  have hdescent : baseEnd_572935 < baseStart_572935 := by decide
  rcases family_descends (prefixWord ++ tailWord_572935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572952 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_572952 : Nat := 118140960795 + 572952 * 2 ^ 59
def prefixEnd_572952 : Nat := 4983230072969 + 3 ^ 40 * 572952 * 2
def baseEnd_572952 : Nat := 261510904848842272324487

theorem tailTrace_572952 : CollatzResearch.WordTrace tailWord_572952 prefixEnd_572952 261510904848842272324487 := by
  unfold tailWord_572952
  simp only [CollatzResearch.WordTrace]
  refine ⟨10448638110150115628140555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13931517480200154170854073 10448638110150115628140555)
  ·
    refine ⟨15672957165225173442210833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10448638110150115628140555 15672957165225173442210833)
    ·
      refine ⟨11754717873918880081658125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15672957165225173442210833 11754717873918880081658125)
      ·
        refine ⟨4408019202719580030621797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11754717873918880081658125 4408019202719580030621797)
        ·
          refine ⟨826503600509921255741587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4408019202719580030621797 826503600509921255741587)
          ·
            refine ⟨1239755400764881883612381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826503600509921255741587 1239755400764881883612381)
            ·
              refine ⟨464908275286830706354643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1239755400764881883612381 464908275286830706354643)
              ·
                refine ⟨697362412930246059531965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464908275286830706354643 697362412930246059531965)
                ·
                  refine ⟨261510904848842272324487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697362412930246059531965 261510904848842272324487)
                  ·
                    rfl

theorem cell20_572952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_572952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572952 prefixEnd_572952 := by exact prefixLift 572952
  have htrace : WordTrace (prefixWord ++ tailWord_572952) baseStart_572952 baseEnd_572952 := by
    simpa [prefixWord, tailWord_572952, baseEnd_572952] using wordTrace_append hprefix tailTrace_572952
  have hstable : (prefixWord ++ tailWord_572952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572952).length < 2 ^ (prefixWord ++ tailWord_572952).sum := by decide
  have hdescent : baseEnd_572952 < baseStart_572952 := by decide
  rcases family_descends (prefixWord ++ tailWord_572952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572958 : List Nat := [4, 3, 3, 1, 2, 1, 2, 4]
def baseStart_572958 : Nat := 118140960795 + 572958 * 2 ^ 59
def prefixEnd_572958 : Nat := 4983230072969 + 3 ^ 40 * 572958 * 2
def baseEnd_572958 : Nat := 87171214470777639374821

theorem tailTrace_572958 : CollatzResearch.WordTrace tailWord_572958 prefixEnd_572958 87171214470777639374821 := by
  unfold tailWord_572958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2612186882284811785124941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13931663372185662853999685 2612186882284811785124941)
  ·
    refine ⟨979570080856804419421853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2612186882284811785124941 979570080856804419421853)
    ·
      refine ⟨367338780321301657283195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 979570080856804419421853 367338780321301657283195)
      ·
        refine ⟨551008170481952485924793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367338780321301657283195 551008170481952485924793)
        ·
          refine ⟨413256127861464364443595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 551008170481952485924793 413256127861464364443595)
          ·
            refine ⟨619884191792196546665393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413256127861464364443595 619884191792196546665393)
            ·
              refine ⟨464913143844147409999045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619884191792196546665393 464913143844147409999045)
              ·
                refine ⟨87171214470777639374821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464913143844147409999045 87171214470777639374821)
                ·
                  rfl

theorem cell20_572958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_572958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572958 prefixEnd_572958 := by exact prefixLift 572958
  have htrace : WordTrace (prefixWord ++ tailWord_572958) baseStart_572958 baseEnd_572958 := by
    simpa [prefixWord, tailWord_572958, baseEnd_572958] using wordTrace_append hprefix tailTrace_572958
  have hstable : (prefixWord ++ tailWord_572958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572958).length < 2 ^ (prefixWord ++ tailWord_572958).sum := by decide
  have hdescent : baseEnd_572958 < baseStart_572958 := by decide
  rcases family_descends (prefixWord ++ tailWord_572958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_572997 : List Nat := [1, 3, 1, 1, 1, 4, 5, 2, 2]
def baseStart_572997 : Nat := 118140960795 + 572997 * 2 ^ 59
def prefixEnd_572997 : Nat := 4983230072969 + 3 ^ 40 * 572997 * 2
def baseEnd_572997 : Nat := 261531444075022115824303

theorem tailTrace_572997 : CollatzResearch.WordTrace tailWord_572997 prefixEnd_572997 261531444075022115824303 := by
  unfold tailWord_572997
  simp only [CollatzResearch.WordTrace]
  refine ⟨20898917505137203941669245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13932611670091469294446163 20898917505137203941669245)
  ·
    refine ⟨7837094064426451478125967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20898917505137203941669245 7837094064426451478125967)
    ·
      refine ⟨11755641096639677217188951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7837094064426451478125967 11755641096639677217188951)
      ·
        refine ⟨17633461644959515825783427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11755641096639677217188951 17633461644959515825783427)
        ·
          refine ⟨26450192467439273738675141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17633461644959515825783427 26450192467439273738675141)
          ·
            refine ⟨4959411087644863826001589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26450192467439273738675141 4959411087644863826001589)
            ·
              refine ⟨464944789466705983687649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4959411087644863826001589 464944789466705983687649)
              ·
                refine ⟨348708592100029487765737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464944789466705983687649 348708592100029487765737)
                ·
                  refine ⟨261531444075022115824303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348708592100029487765737 261531444075022115824303)
                  ·
                    rfl

theorem cell20_572997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_572997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_572997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_572997 prefixEnd_572997 := by exact prefixLift 572997
  have htrace : WordTrace (prefixWord ++ tailWord_572997) baseStart_572997 baseEnd_572997 := by
    simpa [prefixWord, tailWord_572997, baseEnd_572997] using wordTrace_append hprefix tailTrace_572997
  have hstable : (prefixWord ++ tailWord_572997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_572997).length < 2 ^ (prefixWord ++ tailWord_572997).sum := by decide
  have hdescent : baseEnd_572997 < baseStart_572997 := by decide
  rcases family_descends (prefixWord ++ tailWord_572997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573008 : List Nat := [2, 1, 1, 1, 1, 3, 6, 5]
def baseStart_573008 : Nat := 118140960795 + 573008 * 2 ^ 59
def prefixEnd_573008 : Nat := 4983230072969 + 3 ^ 40 * 573008 * 2
def baseEnd_573008 : Nat := 87178821591584988819197

theorem tailTrace_573008 : CollatzResearch.WordTrace tailWord_573008 prefixEnd_573008 87178821591584988819197 := by
  unfold tailWord_573008
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449659354048676410159839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13932879138731568546879785 10449659354048676410159839)
  ·
    refine ⟨15674489031073014615239759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449659354048676410159839 15674489031073014615239759)
    ·
      refine ⟨23511733546609521922859639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15674489031073014615239759 23511733546609521922859639)
      ·
        refine ⟨35267600319914282884289459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23511733546609521922859639 35267600319914282884289459)
        ·
          refine ⟨52901400479871424326434189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35267600319914282884289459 52901400479871424326434189)
          ·
            refine ⟨19838025179951784122412821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52901400479871424326434189 19838025179951784122412821)
            ·
              refine ⟨929907430310239880738101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19838025179951784122412821 929907430310239880738101)
              ·
                refine ⟨87178821591584988819197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 929907430310239880738101 87178821591584988819197)
                ·
                  rfl

theorem cell20_573008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_573008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573008 prefixEnd_573008 := by exact prefixLift 573008
  have htrace : WordTrace (prefixWord ++ tailWord_573008) baseStart_573008 baseEnd_573008 := by
    simpa [prefixWord, tailWord_573008, baseEnd_573008] using wordTrace_append hprefix tailTrace_573008
  have hstable : (prefixWord ++ tailWord_573008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573008).length < 2 ^ (prefixWord ++ tailWord_573008).sum := by decide
  have hdescent : baseEnd_573008 < baseStart_573008 := by decide
  rcases family_descends (prefixWord ++ tailWord_573008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573056 : List Nat := [2, 1, 1, 2, 1, 4, 3, 4, 2]
def baseStart_573056 : Nat := 118140960795 + 573056 * 2 ^ 59
def prefixEnd_573056 : Nat := 4983230072969 + 3 ^ 40 * 573056 * 2
def baseEnd_573056 : Nat := 261558373282680132857395

theorem tailTrace_573056 : CollatzResearch.WordTrace tailWord_573056 prefixEnd_573056 261558373282680132857395 := by
  unfold tailWord_573056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10450534705961728509033511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13934046274615638012044681 10450534705961728509033511)
  ·
    refine ⟨15675802058942592763550267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10450534705961728509033511 15675802058942592763550267)
    ·
      refine ⟨23513703088413889145325401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15675802058942592763550267 23513703088413889145325401)
      ·
        refine ⟨17635277316310416858994051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23513703088413889145325401 17635277316310416858994051)
        ·
          refine ⟨26452915974465625288491077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17635277316310416858994051 26452915974465625288491077)
          ·
            refine ⟨4959921745212304741592077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26452915974465625288491077 4959921745212304741592077)
            ·
              refine ⟨1859970654454614278097029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4959921745212304741592077 1859970654454614278097029)
              ·
                refine ⟨348744497710240177143193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1859970654454614278097029 348744497710240177143193)
                ·
                  refine ⟨261558373282680132857395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348744497710240177143193 261558373282680132857395)
                  ·
                    rfl

theorem cell20_573056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_573056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573056 prefixEnd_573056 := by exact prefixLift 573056
  have htrace : WordTrace (prefixWord ++ tailWord_573056) baseStart_573056 baseEnd_573056 := by
    simpa [prefixWord, tailWord_573056, baseEnd_573056] using wordTrace_append hprefix tailTrace_573056
  have hstable : (prefixWord ++ tailWord_573056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573056).length < 2 ^ (prefixWord ++ tailWord_573056).sum := by decide
  have hdescent : baseEnd_573056 < baseStart_573056 := by decide
  rcases family_descends (prefixWord ++ tailWord_573056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573063 : List Nat := [1, 1, 4, 2, 1, 5, 1, 5]
def baseStart_573063 : Nat := 118140960795 + 573063 * 2 ^ 59
def prefixEnd_573063 : Nat := 4983230072969 + 3 ^ 40 * 573063 * 2
def baseEnd_573063 : Nat := 87187189424473073208011

theorem tailTrace_573063 : CollatzResearch.WordTrace tailWord_573063 prefixEnd_573063 87187189424473073208011 := by
  unfold tailWord_573063
  simp only [CollatzResearch.WordTrace]
  refine ⟨20901324722898097213571843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13934216481932064809047895 20901324722898097213571843)
  ·
    refine ⟨31351987084347145820357765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20901324722898097213571843 31351987084347145820357765)
    ·
      refine ⟨5878497578315089841317081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31351987084347145820357765 5878497578315089841317081)
      ·
        refine ⟨4408873183736317380987811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5878497578315089841317081 4408873183736317380987811)
        ·
          refine ⟨6613309775604476071481717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4408873183736317380987811 6613309775604476071481717)
          ·
            refine ⟨619997791462919631701411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6613309775604476071481717 619997791462919631701411)
            ·
              refine ⟨929996687194379447552117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619997791462919631701411 929996687194379447552117)
              ·
                refine ⟨87187189424473073208011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 929996687194379447552117 87187189424473073208011)
                ·
                  rfl

theorem cell20_573063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_573063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573063 prefixEnd_573063 := by exact prefixLift 573063
  have htrace : WordTrace (prefixWord ++ tailWord_573063) baseStart_573063 baseEnd_573063 := by
    simpa [prefixWord, tailWord_573063, baseEnd_573063] using wordTrace_append hprefix tailTrace_573063
  have hstable : (prefixWord ++ tailWord_573063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573063).length < 2 ^ (prefixWord ++ tailWord_573063).sum := by decide
  have hdescent : baseEnd_573063 < baseStart_573063 := by decide
  rcases family_descends (prefixWord ++ tailWord_573063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573091 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_573091 : Nat := 118140960795 + 573091 * 2 ^ 59
def prefixEnd_573091 : Nat := 4983230072969 + 3 ^ 40 * 573091 * 2
def baseEnd_573091 : Nat := 261574348236375566690585

theorem tailTrace_573091 : CollatzResearch.WordTrace tailWord_573091 prefixEnd_573091 261574348236375566690585 := by
  unfold tailWord_573091
  simp only [CollatzResearch.WordTrace]
  refine ⟨20902345966796657995591127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13934897311197771997060751 20902345966796657995591127)
  ·
    refine ⟨31353518950194986993386691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20902345966796657995591127 31353518950194986993386691)
    ·
      refine ⟨47030278425292480490080037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31353518950194986993386691 47030278425292480490080037)
      ·
        refine ⟨8818177204742340091890007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47030278425292480490080037 8818177204742340091890007)
        ·
          refine ⟨13227265807113510137835011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8818177204742340091890007 13227265807113510137835011)
          ·
            refine ⟨19840898710670265206752517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13227265807113510137835011 19840898710670265206752517)
            ·
              refine ⟨3720168508250674726266097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19840898710670265206752517 3720168508250674726266097)
              ·
                refine ⟨2790126381188006044699573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3720168508250674726266097 2790126381188006044699573)
                ·
                  refine ⟨261574348236375566690585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2790126381188006044699573 261574348236375566690585)
                  ·
                    rfl

theorem cell20_573091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_573091 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573091 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573091 prefixEnd_573091 := by exact prefixLift 573091
  have htrace : WordTrace (prefixWord ++ tailWord_573091) baseStart_573091 baseEnd_573091 := by
    simpa [prefixWord, tailWord_573091, baseEnd_573091] using wordTrace_append hprefix tailTrace_573091
  have hstable : (prefixWord ++ tailWord_573091).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573091).length < 2 ^ (prefixWord ++ tailWord_573091).sum := by decide
  have hdescent : baseEnd_573091 < baseStart_573091 := by decide
  rcases family_descends (prefixWord ++ tailWord_573091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573136 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_573136 : Nat := 118140960795 + 573136 * 2 ^ 59
def prefixEnd_573136 : Nat := 4983230072969 + 3 ^ 40 * 573136 * 2
def baseEnd_573136 : Nat := 261594887462555410190401

theorem tailTrace_573136 : CollatzResearch.WordTrace tailWord_573136 prefixEnd_573136 261594887462555410190401 := by
  unfold tailWord_573136
  simp only [CollatzResearch.WordTrace]
  refine ⟨10451993625816815340489631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13935991501089087120652841 10451993625816815340489631)
  ·
    refine ⟨15677990438725223010734447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10451993625816815340489631 15677990438725223010734447)
    ·
      refine ⟨23516985658087834516101671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15677990438725223010734447 23516985658087834516101671)
      ·
        refine ⟨35275478487131751774152507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23516985658087834516101671 35275478487131751774152507)
        ·
          refine ⟨52913217730697627661228761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35275478487131751774152507 52913217730697627661228761)
          ·
            refine ⟨39684913298023220745921571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52913217730697627661228761 39684913298023220745921571)
            ·
              refine ⟨59527369947034831118882357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39684913298023220745921571 59527369947034831118882357)
              ·
                refine ⟨5580690932534515417395221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59527369947034831118882357 5580690932534515417395221)
                ·
                  refine ⟨261594887462555410190401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5580690932534515417395221 261594887462555410190401)
                  ·
                    rfl

theorem cell20_573136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_573136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573136 prefixEnd_573136 := by exact prefixLift 573136
  have htrace : WordTrace (prefixWord ++ tailWord_573136) baseStart_573136 baseEnd_573136 := by
    simpa [prefixWord, tailWord_573136, baseEnd_573136] using wordTrace_append hprefix tailTrace_573136
  have hstable : (prefixWord ++ tailWord_573136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573136).length < 2 ^ (prefixWord ++ tailWord_573136).sum := by decide
  have hdescent : baseEnd_573136 < baseStart_573136 := by decide
  rcases family_descends (prefixWord ++ tailWord_573136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573160 : List Nat := [2, 1, 4, 1, 3, 1, 8]
def baseStart_573160 : Nat := 118140960795 + 573160 * 2 ^ 59
def prefixEnd_573160 : Nat := 4983230072969 + 3 ^ 40 * 573160 * 2
def baseEnd_573160 : Nat := 29067315746279777043367

theorem tailTrace_573160 : CollatzResearch.WordTrace tailWord_573160 prefixEnd_573160 29067315746279777043367 := by
  unfold tailWord_573160
  simp only [CollatzResearch.WordTrace]
  refine ⟨10452431301773341389926467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13936575069031121853235289 10452431301773341389926467)
  ·
    refine ⟨15678646952660012084889701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10452431301773341389926467 15678646952660012084889701)
    ·
      refine ⟨2939746303623752265916819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15678646952660012084889701 2939746303623752265916819)
      ·
        refine ⟨4409619455435628398875229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2939746303623752265916819 4409619455435628398875229)
        ·
          refine ⟨1653607295788360649578211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4409619455435628398875229 1653607295788360649578211)
          ·
            refine ⟨2480410943682540974367317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1653607295788360649578211 2480410943682540974367317)
            ·
              refine ⟨29067315746279777043367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2480410943682540974367317 29067315746279777043367)
              ·
                rfl

theorem cell20_573160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 8].length) (baseStart_573160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573160 prefixEnd_573160 := by exact prefixLift 573160
  have htrace : WordTrace (prefixWord ++ tailWord_573160) baseStart_573160 baseEnd_573160 := by
    simpa [prefixWord, tailWord_573160, baseEnd_573160] using wordTrace_append hprefix tailTrace_573160
  have hstable : (prefixWord ++ tailWord_573160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573160).length < 2 ^ (prefixWord ++ tailWord_573160).sum := by decide
  have hdescent : baseEnd_573160 < baseStart_573160 := by decide
  rcases family_descends (prefixWord ++ tailWord_573160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573167 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_573167 : Nat := 118140960795 + 573167 * 2 ^ 59
def prefixEnd_573167 : Nat := 4983230072969 + 3 ^ 40 * 573167 * 2
def baseEnd_573167 : Nat := 261609036707257080156941

theorem tailTrace_573167 : CollatzResearch.WordTrace tailWord_573167 prefixEnd_573167 261609036707257080156941 := by
  unfold tailWord_573167
  simp only [CollatzResearch.WordTrace]
  refine ⟨20905117914521322975357755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13936745276347548650238503 20905117914521322975357755)
  ·
    refine ⟨31357676871781984463036633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20905117914521322975357755 31357676871781984463036633)
    ·
      refine ⟨23518257653836488347277475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31357676871781984463036633 23518257653836488347277475)
      ·
        refine ⟨35277386480754732520916213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23518257653836488347277475 35277386480754732520916213)
        ·
          refine ⟨3307254982570756173835895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35277386480754732520916213 3307254982570756173835895)
          ·
            refine ⟨4960882473856134260753843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307254982570756173835895 4960882473856134260753843)
            ·
              refine ⟨7441323710784201391130765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960882473856134260753843 7441323710784201391130765)
              ·
                refine ⟨2790496391544075521674037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7441323710784201391130765 2790496391544075521674037)
                ·
                  refine ⟨261609036707257080156941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2790496391544075521674037 261609036707257080156941)
                  ·
                    rfl

theorem cell20_573167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_573167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573167 prefixEnd_573167 := by exact prefixLift 573167
  have htrace : WordTrace (prefixWord ++ tailWord_573167) baseStart_573167 baseEnd_573167 := by
    simpa [prefixWord, tailWord_573167, baseEnd_573167] using wordTrace_append hprefix tailTrace_573167
  have hstable : (prefixWord ++ tailWord_573167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573167).length < 2 ^ (prefixWord ++ tailWord_573167).sum := by decide
  have hdescent : baseEnd_573167 < baseStart_573167 := by decide
  rcases family_descends (prefixWord ++ tailWord_573167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573198 : List Nat := [4, 1, 1, 2, 1, 1, 4, 6]
def baseStart_573198 : Nat := 118140960795 + 573198 * 2 ^ 59
def prefixEnd_573198 : Nat := 4983230072969 + 3 ^ 40 * 573198 * 2
def baseEnd_573198 : Nat := 87207728650652916707827

theorem tailTrace_573198 : CollatzResearch.WordTrace tailWord_573198 prefixEnd_573198 87207728650652916707827 := by
  unfold tailWord_573198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613281072176126908717031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13937499051606010179824165 2613281072176126908717031)
  ·
    refine ⟨3919921608264190363075547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613281072176126908717031 3919921608264190363075547)
    ·
      refine ⟨5879882412396285544613321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3919921608264190363075547 5879882412396285544613321)
      ·
        refine ⟨4409911809297214158459991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5879882412396285544613321 4409911809297214158459991)
        ·
          refine ⟨6614867713945821237689987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4409911809297214158459991 6614867713945821237689987)
          ·
            refine ⟨9922301570918731856534981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6614867713945821237689987 9922301570918731856534981)
            ·
              refine ⟨1860431544547262223100309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9922301570918731856534981 1860431544547262223100309)
              ·
                refine ⟨87207728650652916707827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1860431544547262223100309 87207728650652916707827)
                ·
                  rfl

theorem cell20_573198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_573198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573198 prefixEnd_573198 := by exact prefixLift 573198
  have htrace : WordTrace (prefixWord ++ tailWord_573198) baseStart_573198 baseEnd_573198 := by
    simpa [prefixWord, tailWord_573198, baseEnd_573198] using wordTrace_append hprefix tailTrace_573198
  have hstable : (prefixWord ++ tailWord_573198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573198).length < 2 ^ (prefixWord ++ tailWord_573198).sum := by decide
  have hdescent : baseEnd_573198 < baseStart_573198 := by decide
  rcases family_descends (prefixWord ++ tailWord_573198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573246 : List Nat := [4, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_573246 : Nat := 118140960795 + 573246 * 2 ^ 59
def prefixEnd_573246 : Nat := 4983230072969 + 3 ^ 40 * 573246 * 2
def baseEnd_573246 : Nat := 261645094459883916523285

theorem tailTrace_573246 : CollatzResearch.WordTrace tailWord_573246 prefixEnd_573246 261645094459883916523285 := by
  unfold tailWord_573246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613499910154389933435449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13938666187490079644989061 2613499910154389933435449)
  ·
    refine ⟨1960124932615792450076587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2613499910154389933435449 1960124932615792450076587)
    ·
      refine ⟨2940187398923688675114881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1960124932615792450076587 2940187398923688675114881)
      ·
        refine ⟨2205140549192766506336161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2940187398923688675114881 2205140549192766506336161)
        ·
          refine ⟨1653855411894574879752121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2205140549192766506336161 1653855411894574879752121)
          ·
            refine ⟨1240391558920931159814091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1653855411894574879752121 1240391558920931159814091)
            ·
              refine ⟨1860587338381396739721137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240391558920931159814091 1860587338381396739721137)
              ·
                refine ⟨1395440503786047554790853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860587338381396739721137 1395440503786047554790853)
                ·
                  refine ⟨261645094459883916523285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395440503786047554790853 261645094459883916523285)
                  ·
                    rfl

theorem cell20_573246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_573246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573246 prefixEnd_573246 := by exact prefixLift 573246
  have htrace : WordTrace (prefixWord ++ tailWord_573246) baseStart_573246 baseEnd_573246 := by
    simpa [prefixWord, tailWord_573246, baseEnd_573246] using wordTrace_append hprefix tailTrace_573246
  have hstable : (prefixWord ++ tailWord_573246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573246).length < 2 ^ (prefixWord ++ tailWord_573246).sum := by decide
  have hdescent : baseEnd_573246 < baseStart_573246 := by decide
  rcases family_descends (prefixWord ++ tailWord_573246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573281 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 5]
def baseStart_573281 : Nat := 118140960795 + 573281 * 2 ^ 59
def prefixEnd_573281 : Nat := 4983230072969 + 3 ^ 40 * 573281 * 2
def baseEnd_573281 : Nat := 261661069413579350356475

theorem tailTrace_573281 : CollatzResearch.WordTrace tailWord_573281 prefixEnd_573281 261661069413579350356475 := by
  unfold tailWord_573281
  simp only [CollatzResearch.WordTrace]
  refine ⟨20909275836108320445007697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13939517224072213630005131 20909275836108320445007697)
  ·
    refine ⟨15681956877081240333755773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20909275836108320445007697 15681956877081240333755773)
    ·
      refine ⟨5880733828905465125158415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15681956877081240333755773 5880733828905465125158415)
      ·
        refine ⟨8821100743358197687737623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5880733828905465125158415 8821100743358197687737623)
        ·
          refine ⟨13231651115037296531606435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8821100743358197687737623 13231651115037296531606435)
          ·
            refine ⟨19847476672555944797409653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13231651115037296531606435 19847476672555944797409653)
            ·
              refine ⟨1860700938052119824757155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19847476672555944797409653 1860700938052119824757155)
              ·
                refine ⟨2791051407078179737135733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860700938052119824757155 2791051407078179737135733)
                ·
                  refine ⟨261661069413579350356475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2791051407078179737135733 261661069413579350356475)
                  ·
                    rfl

theorem cell20_573281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_573281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573281 prefixEnd_573281 := by exact prefixLift 573281
  have htrace : WordTrace (prefixWord ++ tailWord_573281) baseStart_573281 baseEnd_573281 := by
    simpa [prefixWord, tailWord_573281, baseEnd_573281] using wordTrace_append hprefix tailTrace_573281
  have hstable : (prefixWord ++ tailWord_573281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573281).length < 2 ^ (prefixWord ++ tailWord_573281).sum := by decide
  have hdescent : baseEnd_573281 < baseStart_573281 := by decide
  rcases family_descends (prefixWord ++ tailWord_573281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573284 : List Nat := [2, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_573284 : Nat := 118140960795 + 573284 * 2 ^ 59
def prefixEnd_573284 : Nat := 4983230072969 + 3 ^ 40 * 573284 * 2
def baseEnd_573284 : Nat := 261662438695324673256463

theorem tailTrace_573284 : CollatzResearch.WordTrace tailWord_573284 prefixEnd_573284 261662438695324673256463 := by
  unfold tailWord_573284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10454692627548725978683453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13939590170064967971577937 10454692627548725978683453)
  ·
    refine ⟨3920509735330772242006295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10454692627548725978683453 3920509735330772242006295)
    ·
      refine ⟨5880764602996158363009443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3920509735330772242006295 5880764602996158363009443)
      ·
        refine ⟨8821146904494237544514165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5880764602996158363009443 8821146904494237544514165)
        ·
          refine ⟨826982522296334769798203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8821146904494237544514165 826982522296334769798203)
          ·
            refine ⟨1240473783444502154697305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826982522296334769798203 1240473783444502154697305)
            ·
              refine ⟨930355337583376616022979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240473783444502154697305 930355337583376616022979)
              ·
                refine ⟨1395533006375064924034469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930355337583376616022979 1395533006375064924034469)
                ·
                  refine ⟨261662438695324673256463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1395533006375064924034469 261662438695324673256463)
                  ·
                    rfl

theorem cell20_573284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_573284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573284 prefixEnd_573284 := by exact prefixLift 573284
  have htrace : WordTrace (prefixWord ++ tailWord_573284) baseStart_573284 baseEnd_573284 := by
    simpa [prefixWord, tailWord_573284, baseEnd_573284] using wordTrace_append hprefix tailTrace_573284
  have hstable : (prefixWord ++ tailWord_573284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573284).length < 2 ^ (prefixWord ++ tailWord_573284).sum := by decide
  have hdescent : baseEnd_573284 < baseStart_573284 := by decide
  rcases family_descends (prefixWord ++ tailWord_573284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573294 : List Nat := [4, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_573294 : Nat := 118140960795 + 573294 * 2 ^ 59
def prefixEnd_573294 : Nat := 4983230072969 + 3 ^ 40 * 573294 * 2
def baseEnd_573294 : Nat := 261667002967809082923089

theorem tailTrace_573294 : CollatzResearch.WordTrace tailWord_573294 prefixEnd_573294 261667002967809082923089 := by
  unfold tailWord_573294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613718748132652958153867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13939833323374149110153957 2613718748132652958153867)
  ·
    refine ⟨3920578122198979437230801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613718748132652958153867 3920578122198979437230801)
    ·
      refine ⟨2940433591649234577923101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3920578122198979437230801 2940433591649234577923101)
      ·
        refine ⟨1102662596868462966721163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2940433591649234577923101 1102662596868462966721163)
        ·
          refine ⟨1653993895302694450081745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102662596868462966721163 1653993895302694450081745)
          ·
            refine ⟨1240495421477020837561309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1653993895302694450081745 1240495421477020837561309)
            ·
              refine ⟨465185783053882814085491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1240495421477020837561309 465185783053882814085491)
              ·
                refine ⟨697778674580824221128237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465185783053882814085491 697778674580824221128237)
                ·
                  refine ⟨261667002967809082923089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 697778674580824221128237 261667002967809082923089)
                  ·
                    rfl

theorem cell20_573294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_573294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573294 prefixEnd_573294 := by exact prefixLift 573294
  have htrace : WordTrace (prefixWord ++ tailWord_573294) baseStart_573294 baseEnd_573294 := by
    simpa [prefixWord, tailWord_573294, baseEnd_573294] using wordTrace_append hprefix tailTrace_573294
  have hstable : (prefixWord ++ tailWord_573294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573294).length < 2 ^ (prefixWord ++ tailWord_573294).sum := by decide
  have hdescent : baseEnd_573294 < baseStart_573294 := by decide
  rcases family_descends (prefixWord ++ tailWord_573294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573436 : List Nat := [2, 2, 2, 1, 2, 2, 4, 3, 2]
def baseStart_573436 : Nat := 118140960795 + 573436 * 2 ^ 59
def prefixEnd_573436 : Nat := 4983230072969 + 3 ^ 40 * 573436 * 2
def baseEnd_573436 : Nat := 261731815637087700189175

theorem tailTrace_573436 : CollatzResearch.WordTrace tailWord_573436 prefixEnd_573436 261731815637087700189175 := by
  unfold tailWord_573436
  simp only [CollatzResearch.WordTrace]
  refine ⟨10457464575273390958450081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13943286100364521277933441 10457464575273390958450081)
  ·
    refine ⟨7843098431455043218837561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10457464575273390958450081 7843098431455043218837561)
    ·
      refine ⟨5882323823591282414128171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7843098431455043218837561 5882323823591282414128171)
      ·
        refine ⟨8823485735386923621192257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5882323823591282414128171 8823485735386923621192257)
        ·
          refine ⟨6617614301540192715894193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8823485735386923621192257 6617614301540192715894193)
          ·
            refine ⟨4963210726155144536920645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6617614301540192715894193 4963210726155144536920645)
            ·
              refine ⟨930602011154089600672621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4963210726155144536920645 930602011154089600672621)
              ·
                refine ⟨348975754182783600252233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 930602011154089600672621 348975754182783600252233)
                ·
                  refine ⟨261731815637087700189175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348975754182783600252233 261731815637087700189175)
                  ·
                    rfl

theorem cell20_573436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_573436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573436 prefixEnd_573436 := by exact prefixLift 573436
  have htrace : WordTrace (prefixWord ++ tailWord_573436) baseStart_573436 baseEnd_573436 := by
    simpa [prefixWord, tailWord_573436, baseEnd_573436] using wordTrace_append hprefix tailTrace_573436
  have hstable : (prefixWord ++ tailWord_573436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573436).length < 2 ^ (prefixWord ++ tailWord_573436).sum := by decide
  have hdescent : baseEnd_573436 < baseStart_573436 := by decide
  rcases family_descends (prefixWord ++ tailWord_573436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573450 : List Nat := [3, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_573450 : Nat := 118140960795 + 573450 * 2 ^ 59
def prefixEnd_573450 : Nat := 4983230072969 + 3 ^ 40 * 573450 * 2
def baseEnd_573450 : Nat := 261738205618565873722451

theorem tailTrace_573450 : CollatzResearch.WordTrace tailWord_573450 prefixEnd_573450 261738205618565873722451 := by
  unfold tailWord_573450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228859943124015576977451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13943626514997374871939869 5228859943124015576977451)
  ·
    refine ⟨7843289914686023365466177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5228859943124015576977451 7843289914686023365466177)
    ·
      refine ⟨5882467436014517524099633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7843289914686023365466177 5882467436014517524099633)
      ·
        refine ⟨4411850577010888143074725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5882467436014517524099633 4411850577010888143074725)
        ·
          refine ⟨827221983189541526826511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4411850577010888143074725 827221983189541526826511)
          ·
            refine ⟨1240832974784312290239767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827221983189541526826511 1240832974784312290239767)
            ·
              refine ⟨1861249462176468435359651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240832974784312290239767 1861249462176468435359651)
              ·
                refine ⟨2791874193264702653039477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861249462176468435359651 2791874193264702653039477)
                ·
                  refine ⟨261738205618565873722451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2791874193264702653039477 261738205618565873722451)
                  ·
                    rfl

theorem cell20_573450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_573450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573450 prefixEnd_573450 := by exact prefixLift 573450
  have htrace : WordTrace (prefixWord ++ tailWord_573450) baseStart_573450 baseEnd_573450 := by
    simpa [prefixWord, tailWord_573450, baseEnd_573450] using wordTrace_append hprefix tailTrace_573450
  have hstable : (prefixWord ++ tailWord_573450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573450).length < 2 ^ (prefixWord ++ tailWord_573450).sum := by decide
  have hdescent : baseEnd_573450 < baseStart_573450 := by decide
  rcases family_descends (prefixWord ++ tailWord_573450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573509 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 3]
def baseStart_573509 : Nat := 118140960795 + 573509 * 2 ^ 59
def prefixEnd_573509 : Nat := 4983230072969 + 3 ^ 40 * 573509 * 2
def baseEnd_573509 : Nat := 261765134826223890755543

theorem tailTrace_573509 : CollatzResearch.WordTrace tailWord_573509 prefixEnd_573509 261765134826223890755543 := by
  unfold tailWord_573509
  simp only [CollatzResearch.WordTrace]
  refine ⟨20917591679282315384307581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13945061119521543589538387 20917591679282315384307581)
  ·
    refine ⟨7844096879730868269115343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20917591679282315384307581 7844096879730868269115343)
    ·
      refine ⟨11766145319596302403673015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7844096879730868269115343 11766145319596302403673015)
      ·
        refine ⟨17649217979394453605509523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11766145319596302403673015 17649217979394453605509523)
        ·
          refine ⟨26473826969091680408264285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17649217979394453605509523 26473826969091680408264285)
          ·
            refine ⟨9927685113409380153099107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26473826969091680408264285 9927685113409380153099107)
            ·
              refine ⟨14891527670114070229648661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9927685113409380153099107 14891527670114070229648661)
              ·
                refine ⟨698040359536597042014781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14891527670114070229648661 698040359536597042014781)
                ·
                  refine ⟨261765134826223890755543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698040359536597042014781 261765134826223890755543)
                  ·
                    rfl

theorem cell20_573509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_573509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573509 prefixEnd_573509 := by exact prefixLift 573509
  have htrace : WordTrace (prefixWord ++ tailWord_573509) baseStart_573509 baseEnd_573509 := by
    simpa [prefixWord, tailWord_573509, baseEnd_573509] using wordTrace_append hprefix tailTrace_573509
  have hstable : (prefixWord ++ tailWord_573509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573509).length < 2 ^ (prefixWord ++ tailWord_573509).sum := by decide
  have hdescent : baseEnd_573509 < baseStart_573509 := by decide
  rcases family_descends (prefixWord ++ tailWord_573509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573522 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_573522 : Nat := 118140960795 + 573522 * 2 ^ 59
def prefixEnd_573522 : Nat := 4983230072969 + 3 ^ 40 * 573522 * 2
def baseEnd_573522 : Nat := 261771068380453623322157

theorem tailTrace_573522 : CollatzResearch.WordTrace tailWord_573522 prefixEnd_573522 261771068380453623322157 := by
  unfold tailWord_573522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229516457058804651132705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13945377218823479069687213 5229516457058804651132705)
  ·
    refine ⟨3922137342794103488349529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5229516457058804651132705 3922137342794103488349529)
    ·
      refine ⟨2941603007095577616262147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3922137342794103488349529 2941603007095577616262147)
      ·
        refine ⟨4412404510643366424393221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941603007095577616262147 4412404510643366424393221)
        ·
          refine ⟨827325845745631204573729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4412404510643366424393221 827325845745631204573729)
          ·
            refine ⟨620494384309223403430297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827325845745631204573729 620494384309223403430297)
            ·
              refine ⟨465370788231917552572723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620494384309223403430297 465370788231917552572723)
              ·
                refine ⟨698056182347876328859085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465370788231917552572723 698056182347876328859085)
                ·
                  refine ⟨261771068380453623322157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698056182347876328859085 261771068380453623322157)
                  ·
                    rfl

theorem cell20_573522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_573522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573522 prefixEnd_573522 := by exact prefixLift 573522
  have htrace : WordTrace (prefixWord ++ tailWord_573522) baseStart_573522 baseEnd_573522 := by
    simpa [prefixWord, tailWord_573522, baseEnd_573522] using wordTrace_append hprefix tailTrace_573522
  have hstable : (prefixWord ++ tailWord_573522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573522).length < 2 ^ (prefixWord ++ tailWord_573522).sum := by decide
  have hdescent : baseEnd_573522 < baseStart_573522 := by decide
  rcases family_descends (prefixWord ++ tailWord_573522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573550 : List Nat := [4, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_573550 : Nat := 118140960795 + 573550 * 2 ^ 59
def prefixEnd_573550 : Nat := 4983230072969 + 3 ^ 40 * 573550 * 2
def baseEnd_573550 : Nat := 261783848343409970388709

theorem tailTrace_573550 : CollatzResearch.WordTrace tailWord_573550 prefixEnd_573550 261783848343409970388709 := by
  unfold tailWord_573550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2614885884016722423318763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13946058048089186257700069 2614885884016722423318763)
  ·
    refine ⟨3922328826025083634978145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2614885884016722423318763 3922328826025083634978145)
    ·
      refine ⟨2941746619518812726233609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3922328826025083634978145 2941746619518812726233609)
      ·
        refine ⟨2206309964639109544675207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2941746619518812726233609 2206309964639109544675207)
        ·
          refine ⟨3309464946958664317012811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206309964639109544675207 3309464946958664317012811)
          ·
            refine ⟨4964197420437996475519217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3309464946958664317012811 4964197420437996475519217)
            ·
              refine ⟨3723148065328497356639413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4964197420437996475519217 3723148065328497356639413)
              ·
                refine ⟨349045131124546627184945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3723148065328497356639413 349045131124546627184945)
                ·
                  refine ⟨261783848343409970388709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349045131124546627184945 261783848343409970388709)
                  ·
                    rfl

theorem cell20_573550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_573550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573550 prefixEnd_573550 := by exact prefixLift 573550
  have htrace : WordTrace (prefixWord ++ tailWord_573550) baseStart_573550 baseEnd_573550 := by
    simpa [prefixWord, tailWord_573550, baseEnd_573550] using wordTrace_append hprefix tailTrace_573550
  have hstable : (prefixWord ++ tailWord_573550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573550).length < 2 ^ (prefixWord ++ tailWord_573550).sum := by decide
  have hdescent : baseEnd_573550 < baseStart_573550 := by decide
  rcases family_descends (prefixWord ++ tailWord_573550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573561 : List Nat := [1, 2, 1, 3, 4, 9]
def baseStart_573561 : Nat := 118140960795 + 573561 * 2 ^ 59
def prefixEnd_573561 : Nat := 4983230072969 + 3 ^ 40 * 573561 * 2
def baseEnd_573561 : Nat := 9695884038634919297111

theorem tailTrace_573561 : CollatzResearch.WordTrace tailWord_573561 prefixEnd_573561 9695884038634919297111 := by
  unfold tailWord_573561
  simp only [CollatzResearch.WordTrace]
  refine ⟨20919488275093928265200537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13946325516729285510133691 20919488275093928265200537)
  ·
    refine ⟨15689616206320446198900403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20919488275093928265200537 15689616206320446198900403)
    ·
      refine ⟨23534424309480669298350605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15689616206320446198900403 23534424309480669298350605)
      ·
        refine ⟨8825409116055250986881477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23534424309480669298350605 8825409116055250986881477)
        ·
          refine ⟨1654764209260359560040277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8825409116055250986881477 1654764209260359560040277)
          ·
            refine ⟨9695884038634919297111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1654764209260359560040277 9695884038634919297111)
            ·
              rfl

theorem cell20_573561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 9].length) (baseStart_573561 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573561 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573561 prefixEnd_573561 := by exact prefixLift 573561
  have htrace : WordTrace (prefixWord ++ tailWord_573561) baseStart_573561 baseEnd_573561 := by
    simpa [prefixWord, tailWord_573561, baseEnd_573561] using wordTrace_append hprefix tailTrace_573561
  have hstable : (prefixWord ++ tailWord_573561).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573561).length < 2 ^ (prefixWord ++ tailWord_573561).sum := by decide
  have hdescent : baseEnd_573561 < baseStart_573561 := by decide
  rcases family_descends (prefixWord ++ tailWord_573561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573564 : List Nat := [2, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_573564 : Nat := 118140960795 + 573564 * 2 ^ 59
def prefixEnd_573564 : Nat := 4983230072969 + 3 ^ 40 * 573564 * 2
def baseEnd_573564 : Nat := 261790238324888143921985

theorem tailTrace_573564 : CollatzResearch.WordTrace tailWord_573564 prefixEnd_573564 261790238324888143921985 := by
  unfold tailWord_573564
  simp only [CollatzResearch.WordTrace]
  refine ⟨10459798847041529888779873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13946398462722039851706497 10459798847041529888779873)
  ·
    refine ⟨7844849135281147416584905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10459798847041529888779873 7844849135281147416584905)
    ·
      refine ⟨5883636851460860562438679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7844849135281147416584905 5883636851460860562438679)
      ·
        refine ⟨8825455277191290843658019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883636851460860562438679 8825455277191290843658019)
        ·
          refine ⟨13238182915786936265487029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8825455277191290843658019 13238182915786936265487029)
          ·
            refine ⟨1241079648355025274889409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13238182915786936265487029 1241079648355025274889409)
            ·
              refine ⟨930809736266268956167057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241079648355025274889409 930809736266268956167057)
              ·
                refine ⟨698107302199701717125293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930809736266268956167057 698107302199701717125293)
                ·
                  refine ⟨261790238324888143921985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698107302199701717125293 261790238324888143921985)
                  ·
                    rfl

theorem cell20_573564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_573564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573564 prefixEnd_573564 := by exact prefixLift 573564
  have htrace : WordTrace (prefixWord ++ tailWord_573564) baseStart_573564 baseEnd_573564 := by
    simpa [prefixWord, tailWord_573564, baseEnd_573564] using wordTrace_append hprefix tailTrace_573564
  have hstable : (prefixWord ++ tailWord_573564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573564).length < 2 ^ (prefixWord ++ tailWord_573564).sum := by decide
  have hdescent : baseEnd_573564 < baseStart_573564 := by decide
  rcases family_descends (prefixWord ++ tailWord_573564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573578 : List Nat := [3, 1, 2, 3, 1, 2, 3, 5]
def baseStart_573578 : Nat := 118140960795 + 573578 * 2 ^ 59
def prefixEnd_573578 : Nat := 4983230072969 + 3 ^ 40 * 573578 * 2
def baseEnd_573578 : Nat := 87265542768788772485087

theorem tailTrace_573578 : CollatzResearch.WordTrace tailWord_573578 prefixEnd_573578 87265542768788772485087 := by
  unfold tailWord_573578
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230027079008085042142347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13946738877354893445712925 5230027079008085042142347)
  ·
    refine ⟨7845040618512127563213521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5230027079008085042142347 7845040618512127563213521)
    ·
      refine ⟨5883780463884095672410141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7845040618512127563213521 5883780463884095672410141)
      ·
        refine ⟨2206417673956535877153803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5883780463884095672410141 2206417673956535877153803)
        ·
          refine ⟨3309626510934803815730705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206417673956535877153803 3309626510934803815730705)
          ·
            refine ⟨2482219883201102861798029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3309626510934803815730705 2482219883201102861798029)
            ·
              refine ⟨930832456200413573174261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2482219883201102861798029 930832456200413573174261)
              ·
                refine ⟨87265542768788772485087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 930832456200413573174261 87265542768788772485087)
                ·
                  rfl

theorem cell20_573578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_573578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573578 prefixEnd_573578 := by exact prefixLift 573578
  have htrace : WordTrace (prefixWord ++ tailWord_573578) baseStart_573578 baseEnd_573578 := by
    simpa [prefixWord, tailWord_573578, baseEnd_573578] using wordTrace_append hprefix tailTrace_573578
  have hstable : (prefixWord ++ tailWord_573578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573578).length < 2 ^ (prefixWord ++ tailWord_573578).sum := by decide
  have hdescent : baseEnd_573578 < baseStart_573578 := by decide
  rcases family_descends (prefixWord ++ tailWord_573578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573623 : List Nat := [1, 1, 3, 1, 4, 3, 1, 1, 5]
def baseStart_573623 : Nat := 118140960795 + 573623 * 2 ^ 59
def prefixEnd_573623 : Nat := 4983230072969 + 3 ^ 40 * 573623 * 2
def baseEnd_573623 : Nat := 261817167532546160955077

theorem tailTrace_573623 : CollatzResearch.WordTrace tailWord_573623 prefixEnd_573623 261817167532546160955077 := by
  unfold tailWord_573623
  simp only [CollatzResearch.WordTrace]
  refine ⟨20921749600869312853957523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13947833067246208569305015 20921749600869312853957523)
  ·
    refine ⟨31382624401303969280936285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20921749600869312853957523 31382624401303969280936285)
    ·
      refine ⟨11768484150488988480351107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31382624401303969280936285 11768484150488988480351107)
      ·
        refine ⟨17652726225733482720526661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11768484150488988480351107 17652726225733482720526661)
        ·
          refine ⟨3309886167325028010098749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17652726225733482720526661 3309886167325028010098749)
          ·
            refine ⟨1241207312746885503787031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3309886167325028010098749 1241207312746885503787031)
            ·
              refine ⟨1861810969120328255680547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241207312746885503787031 1861810969120328255680547)
              ·
                refine ⟨2792716453680492383520821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861810969120328255680547 2792716453680492383520821)
                ·
                  refine ⟨261817167532546160955077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2792716453680492383520821 261817167532546160955077)
                  ·
                    rfl

theorem cell20_573623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_573623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573623 prefixEnd_573623 := by exact prefixLift 573623
  have htrace : WordTrace (prefixWord ++ tailWord_573623) baseStart_573623 baseEnd_573623 := by
    simpa [prefixWord, tailWord_573623, baseEnd_573623] using wordTrace_append hprefix tailTrace_573623
  have hstable : (prefixWord ++ tailWord_573623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573623).length < 2 ^ (prefixWord ++ tailWord_573623).sum := by decide
  have hdescent : baseEnd_573623 < baseStart_573623 := by decide
  rcases family_descends (prefixWord ++ tailWord_573623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573692 : List Nat := [2, 2, 2, 1, 4, 2, 2, 5]
def baseStart_573692 : Nat := 118140960795 + 573692 * 2 ^ 59
def prefixEnd_573692 : Nat := 4983230072969 + 3 ^ 40 * 573692 * 2
def baseEnd_573692 : Nat := 87282887004229529218265

theorem tailTrace_573692 : CollatzResearch.WordTrace tailWord_573692 prefixEnd_573692 87282887004229529218265 := by
  unfold tailWord_573692
  simp only [CollatzResearch.WordTrace]
  refine ⟨10462133118809668819109665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13949510825079558425479553 10462133118809668819109665)
  ·
    refine ⟨7846599839107251614332249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10462133118809668819109665 7846599839107251614332249)
    ·
      refine ⟨5884949879330438710749187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7846599839107251614332249 5884949879330438710749187)
      ·
        refine ⟨8827424818995658066123781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5884949879330438710749187 8827424818995658066123781)
        ·
          refine ⟨1655142153561685887398209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8827424818995658066123781 1655142153561685887398209)
          ·
            refine ⟨1241356615171264415548657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1655142153561685887398209 1241356615171264415548657)
            ·
              refine ⟨931017461378448311661493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241356615171264415548657 931017461378448311661493)
              ·
                refine ⟨87282887004229529218265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 931017461378448311661493 87282887004229529218265)
                ·
                  rfl

theorem cell20_573692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_573692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573692 prefixEnd_573692 := by exact prefixLift 573692
  have htrace : WordTrace (prefixWord ++ tailWord_573692) baseStart_573692 baseEnd_573692 := by
    simpa [prefixWord, tailWord_573692, baseEnd_573692] using wordTrace_append hprefix tailTrace_573692
  have hstable : (prefixWord ++ tailWord_573692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573692).length < 2 ^ (prefixWord ++ tailWord_573692).sum := by decide
  have hdescent : baseEnd_573692 < baseStart_573692 := by decide
  rcases family_descends (prefixWord ++ tailWord_573692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573699 : List Nat := [1, 1, 1, 3, 2, 3, 3, 3, 3]
def baseStart_573699 : Nat := 118140960795 + 573699 * 2 ^ 59
def prefixEnd_573699 : Nat := 4983230072969 + 3 ^ 40 * 573699 * 2
def baseEnd_573699 : Nat := 261851856003427674421433

theorem tailTrace_573699 : CollatzResearch.WordTrace tailWord_573699 prefixEnd_573699 261851856003427674421433 := by
  unfold tailWord_573699
  simp only [CollatzResearch.WordTrace]
  refine ⟨20924521548593977833724151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13949681032395985222482767 20924521548593977833724151)
  ·
    refine ⟨31386782322890966750586227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20924521548593977833724151 31386782322890966750586227)
    ·
      refine ⟨47080173484336450125879341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31386782322890966750586227 47080173484336450125879341)
      ·
        refine ⟨17655065056626168797204753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47080173484336450125879341 17655065056626168797204753)
        ·
          refine ⟨13241298792469626597903565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17655065056626168797204753 13241298792469626597903565)
          ·
            refine ⟨4965487047176109974213837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13241298792469626597903565 4965487047176109974213837)
            ·
              refine ⟨1862057642691041240330189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4965487047176109974213837 1862057642691041240330189)
              ·
                refine ⟨698271616009140465123821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1862057642691041240330189 698271616009140465123821)
                ·
                  refine ⟨261851856003427674421433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698271616009140465123821 261851856003427674421433)
                  ·
                    rfl

theorem cell20_573699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 3, 3].length) (baseStart_573699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573699 prefixEnd_573699 := by exact prefixLift 573699
  have htrace : WordTrace (prefixWord ++ tailWord_573699) baseStart_573699 baseEnd_573699 := by
    simpa [prefixWord, tailWord_573699, baseEnd_573699] using wordTrace_append hprefix tailTrace_573699
  have hstable : (prefixWord ++ tailWord_573699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573699).length < 2 ^ (prefixWord ++ tailWord_573699).sum := by decide
  have hdescent : baseEnd_573699 < baseStart_573699 := by decide
  rcases family_descends (prefixWord ++ tailWord_573699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573706 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_573706 : Nat := 118140960795 + 573706 * 2 ^ 59
def prefixEnd_573706 : Nat := 4983230072969 + 3 ^ 40 * 573706 * 2
def baseEnd_573706 : Nat := 261855050994166761188071

theorem tailTrace_573706 : CollatzResearch.WordTrace tailWord_573706 prefixEnd_573706 261855050994166761188071 := by
  unfold tailWord_573706
  simp only [CollatzResearch.WordTrace]
  refine ⟨5231194214892154507307243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13949851239712412019485981 5231194214892154507307243)
  ·
    refine ⟨7846791322338231760960865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5231194214892154507307243 7846791322338231760960865)
    ·
      refine ⟨5885093491753673820720649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7846791322338231760960865 5885093491753673820720649)
      ·
        refine ⟨4413820118815255365540487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5885093491753673820720649 4413820118815255365540487)
        ·
          refine ⟨6620730178222883048310731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413820118815255365540487 6620730178222883048310731)
          ·
            refine ⟨9931095267334324572466097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6620730178222883048310731 9931095267334324572466097)
            ·
              refine ⟨7448321450500743429349573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9931095267334324572466097 7448321450500743429349573)
              ·
                refine ⟨1396560271968889393003045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7448321450500743429349573 1396560271968889393003045)
                ·
                  refine ⟨261855050994166761188071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396560271968889393003045 261855050994166761188071)
                  ·
                    rfl

theorem cell20_573706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_573706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573706 prefixEnd_573706 := by exact prefixLift 573706
  have htrace : WordTrace (prefixWord ++ tailWord_573706) baseStart_573706 baseEnd_573706 := by
    simpa [prefixWord, tailWord_573706, baseEnd_573706] using wordTrace_append hprefix tailTrace_573706
  have hstable : (prefixWord ++ tailWord_573706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573706).length < 2 ^ (prefixWord ++ tailWord_573706).sum := by decide
  have hdescent : baseEnd_573706 < baseStart_573706 := by decide
  rcases family_descends (prefixWord ++ tailWord_573706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573713 : List Nat := [1, 2, 2, 1, 1, 5, 2, 6]
def baseStart_573713 : Nat := 118140960795 + 573713 * 2 ^ 59
def prefixEnd_573713 : Nat := 4983230072969 + 3 ^ 40 * 573713 * 2
def baseEnd_573713 : Nat := 87286081994968615984903

theorem tailTrace_573713 : CollatzResearch.WordTrace tailWord_573713 prefixEnd_573713 87286081994968615984903 := by
  unfold tailWord_573713
  simp only [CollatzResearch.WordTrace]
  refine ⟨20925032170543258224733793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13950021447028838816489195 20925032170543258224733793)
  ·
    refine ⟨15693774127907443668550345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20925032170543258224733793 15693774127907443668550345)
    ·
      refine ⟨11770330595930582751412759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15693774127907443668550345 11770330595930582751412759)
      ·
        refine ⟨17655495893895874127119139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11770330595930582751412759 17655495893895874127119139)
        ·
          refine ⟨26483243840843811190678709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17655495893895874127119139 26483243840843811190678709)
          ·
            refine ⟨2482804110079107299126129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26483243840843811190678709 2482804110079107299126129)
            ·
              refine ⟨1862103082559330474344597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2482804110079107299126129 1862103082559330474344597)
              ·
                refine ⟨87286081994968615984903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1862103082559330474344597 87286081994968615984903)
                ·
                  rfl

theorem cell20_573713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_573713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573713 prefixEnd_573713 := by exact prefixLift 573713
  have htrace : WordTrace (prefixWord ++ tailWord_573713) baseStart_573713 baseEnd_573713 := by
    simpa [prefixWord, tailWord_573713, baseEnd_573713] using wordTrace_append hprefix tailTrace_573713
  have hstable : (prefixWord ++ tailWord_573713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573713).length < 2 ^ (prefixWord ++ tailWord_573713).sum := by decide
  have hdescent : baseEnd_573713 < baseStart_573713 := by decide
  rcases family_descends (prefixWord ++ tailWord_573713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573736 : List Nat := [2, 1, 5, 1, 3, 2, 2, 2, 2]
def baseStart_573736 : Nat := 118140960795 + 573736 * 2 ^ 59
def prefixEnd_573736 : Nat := 4983230072969 + 3 ^ 40 * 573736 * 2
def baseEnd_573736 : Nat := 261868743811619990187949

theorem tailTrace_573736 : CollatzResearch.WordTrace tailWord_573736 prefixEnd_573736 261868743811619990187949 := by
  unfold tailWord_573736
  simp only [CollatzResearch.WordTrace]
  refine ⟨10462935524729966576410531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13950580699639955435214041 10462935524729966576410531)
  ·
    refine ⟨15694403287094949864615797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10462935524729966576410531 15694403287094949864615797)
    ·
      refine ⟨1471350308165151549807731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15694403287094949864615797 1471350308165151549807731)
      ·
        refine ⟨2207025462247727324711597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471350308165151549807731 2207025462247727324711597)
        ·
          refine ⟨827634548342897746766849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2207025462247727324711597 827634548342897746766849)
          ·
            refine ⟨620725911257173310075137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827634548342897746766849 620725911257173310075137)
            ·
              refine ⟨465544433442879982556353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620725911257173310075137 465544433442879982556353)
              ·
                refine ⟨349158325082159986917265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465544433442879982556353 349158325082159986917265)
                ·
                  refine ⟨261868743811619990187949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349158325082159986917265 261868743811619990187949)
                  ·
                    rfl

theorem cell20_573736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 2].length) (baseStart_573736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573736 prefixEnd_573736 := by exact prefixLift 573736
  have htrace : WordTrace (prefixWord ++ tailWord_573736) baseStart_573736 baseEnd_573736 := by
    simpa [prefixWord, tailWord_573736, baseEnd_573736] using wordTrace_append hprefix tailTrace_573736
  have hstable : (prefixWord ++ tailWord_573736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573736).length < 2 ^ (prefixWord ++ tailWord_573736).sum := by decide
  have hdescent : baseEnd_573736 < baseStart_573736 := by decide
  rcases family_descends (prefixWord ++ tailWord_573736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573740 : List Nat := [2, 2, 1, 1, 1, 3, 6, 2, 2]
def baseStart_573740 : Nat := 118140960795 + 573740 * 2 ^ 59
def prefixEnd_573740 : Nat := 4983230072969 + 3 ^ 40 * 573740 * 2
def baseEnd_573740 : Nat := 261870569520613754054599

theorem tailTrace_573740 : CollatzResearch.WordTrace tailWord_573740 prefixEnd_573740 261870569520613754054599 := by
  unfold tailWord_573740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10463008470722720917983337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13950677960963627890644449 10463008470722720917983337)
  ·
    refine ⟨7847256353042040688487503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10463008470722720917983337 7847256353042040688487503)
    ·
      refine ⟨11770884529563061032731255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7847256353042040688487503 11770884529563061032731255)
      ·
        refine ⟨17656326794344591549096883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11770884529563061032731255 17656326794344591549096883)
        ·
          refine ⟨26484490191516887323645325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17656326794344591549096883 26484490191516887323645325)
          ·
            refine ⟨9931683821818832746366997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26484490191516887323645325 9931683821818832746366997)
            ·
              refine ⟨465547679147757784985953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9931683821818832746366997 465547679147757784985953)
              ·
                refine ⟨349160759360818338739465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465547679147757784985953 349160759360818338739465)
                ·
                  refine ⟨261870569520613754054599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349160759360818338739465 261870569520613754054599)
                  ·
                    rfl

theorem cell20_573740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_573740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573740 prefixEnd_573740 := by exact prefixLift 573740
  have htrace : WordTrace (prefixWord ++ tailWord_573740) baseStart_573740 baseEnd_573740 := by
    simpa [prefixWord, tailWord_573740, baseEnd_573740] using wordTrace_append hprefix tailTrace_573740
  have hstable : (prefixWord ++ tailWord_573740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573740).length < 2 ^ (prefixWord ++ tailWord_573740).sum := by decide
  have hdescent : baseEnd_573740 < baseStart_573740 := by decide
  rcases family_descends (prefixWord ++ tailWord_573740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573764 : List Nat := [2, 3, 4, 1, 2, 1, 3, 4]
def baseStart_573764 : Nat := 118140960795 + 573764 * 2 ^ 59
def prefixEnd_573764 : Nat := 4983230072969 + 3 ^ 40 * 573764 * 2
def baseEnd_573764 : Nat := 87293841258192112418167

theorem tailTrace_573764 : CollatzResearch.WordTrace tailWord_573764 prefixEnd_573764 87293841258192112418167 := by
  unfold tailWord_573764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10463446146679246967420173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13951261528905662623226897 10463446146679246967420173)
  ·
    refine ⟨3923792305004717612782565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10463446146679246967420173 3923792305004717612782565)
    ·
      refine ⟨735711057188384552396731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3923792305004717612782565 735711057188384552396731)
      ·
        refine ⟨1103566585782576828595097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735711057188384552396731 1103566585782576828595097)
        ·
          refine ⟨827674939336932621446323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1103566585782576828595097 827674939336932621446323)
          ·
            refine ⟨1241512409005398932169485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827674939336932621446323 1241512409005398932169485)
            ·
              refine ⟨465567153377024599563557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1241512409005398932169485 465567153377024599563557)
              ·
                refine ⟨87293841258192112418167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 465567153377024599563557 87293841258192112418167)
                ·
                  rfl

theorem cell20_573764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_573764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573764 prefixEnd_573764 := by exact prefixLift 573764
  have htrace : WordTrace (prefixWord ++ tailWord_573764) baseStart_573764 baseEnd_573764 := by
    simpa [prefixWord, tailWord_573764, baseEnd_573764] using wordTrace_append hprefix tailTrace_573764
  have hstable : (prefixWord ++ tailWord_573764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573764).length < 2 ^ (prefixWord ++ tailWord_573764).sum := by decide
  have hdescent : baseEnd_573764 < baseStart_573764 := by decide
  rcases family_descends (prefixWord ++ tailWord_573764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573788 : List Nat := [2, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_573788 : Nat := 118140960795 + 573788 * 2 ^ 59
def prefixEnd_573788 : Nat := 4983230072969 + 3 ^ 40 * 573788 * 2
def baseEnd_573788 : Nat := 261892478028538920454403

theorem tailTrace_573788 : CollatzResearch.WordTrace tailWord_573788 prefixEnd_573788 261892478028538920454403 := by
  unfold tailWord_573788
  simp only [CollatzResearch.WordTrace]
  refine ⟨10463883822635773016857009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13951845096847697355809345 10463883822635773016857009)
  ·
    refine ⟨7847912866976829762642757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10463883822635773016857009 7847912866976829762642757)
    ·
      refine ⟨1471483662558155580495517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7847912866976829762642757 1471483662558155580495517)
      ·
        refine ⟨551806373459308342685819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1471483662558155580495517 551806373459308342685819)
        ·
          refine ⟨827709560188962514028729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551806373459308342685819 827709560188962514028729)
          ·
            refine ⟨620782170141721885521547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 827709560188962514028729 620782170141721885521547)
            ·
              refine ⟨931173255212582828282321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620782170141721885521547 931173255212582828282321)
              ·
                refine ⟨698379941409437121211741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931173255212582828282321 698379941409437121211741)
                ·
                  refine ⟨261892478028538920454403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698379941409437121211741 261892478028538920454403)
                  ·
                    rfl

theorem cell20_573788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_573788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573788 prefixEnd_573788 := by exact prefixLift 573788
  have htrace : WordTrace (prefixWord ++ tailWord_573788) baseStart_573788 baseEnd_573788 := by
    simpa [prefixWord, tailWord_573788, baseEnd_573788] using wordTrace_append hprefix tailTrace_573788
  have hstable : (prefixWord ++ tailWord_573788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573788).length < 2 ^ (prefixWord ++ tailWord_573788).sum := by decide
  have hdescent : baseEnd_573788 < baseStart_573788 := by decide
  rcases family_descends (prefixWord ++ tailWord_573788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573799 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_573799 : Nat := 118140960795 + 573799 * 2 ^ 59
def prefixEnd_573799 : Nat := 4983230072969 + 3 ^ 40 * 573799 * 2
def baseEnd_573799 : Nat := 261897498728271771087691

theorem tailTrace_573799 : CollatzResearch.WordTrace tailWord_573799 prefixEnd_573799 261897498728271771087691 := by
  unfold tailWord_573799
  simp only [CollatzResearch.WordTrace]
  refine ⟨20928168848231694912364451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13952112565487796608242967 20928168848231694912364451)
  ·
    refine ⟨31392253272347542368546677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20928168848231694912364451 31392253272347542368546677)
    ·
      refine ⟨2943023744282582097051251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31392253272347542368546677 2943023744282582097051251)
      ·
        refine ⟨4414535616423873145576877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943023744282582097051251 4414535616423873145576877)
        ·
          refine ⟨1655450856158952429591329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4414535616423873145576877 1655450856158952429591329)
          ·
            refine ⟨1241588142119214322193497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1655450856158952429591329 1241588142119214322193497)
            ·
              refine ⟨931191106589410741645123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241588142119214322193497 931191106589410741645123)
              ·
                refine ⟨1396786659884116112467685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931191106589410741645123 1396786659884116112467685)
                ·
                  refine ⟨261897498728271771087691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396786659884116112467685 261897498728271771087691)
                  ·
                    rfl

theorem cell20_573799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_573799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573799 prefixEnd_573799 := by exact prefixLift 573799
  have htrace : WordTrace (prefixWord ++ tailWord_573799) baseStart_573799 baseEnd_573799 := by
    simpa [prefixWord, tailWord_573799, baseEnd_573799] using wordTrace_append hprefix tailTrace_573799
  have hstable : (prefixWord ++ tailWord_573799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573799).length < 2 ^ (prefixWord ++ tailWord_573799).sum := by decide
  have hdescent : baseEnd_573799 < baseStart_573799 := by decide
  rcases family_descends (prefixWord ++ tailWord_573799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573803 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 8]
def baseStart_573803 : Nat := 118140960795 + 573803 * 2 ^ 59
def prefixEnd_573803 : Nat := 4983230072969 + 3 ^ 40 * 573803 * 2
def baseEnd_573803 : Nat := 261899324437265534954341

theorem tailTrace_573803 : CollatzResearch.WordTrace tailWord_573803 prefixEnd_573803 261899324437265534954341 := by
  unfold tailWord_573803
  simp only [CollatzResearch.WordTrace]
  refine ⟨20928314740217203595510063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13952209826811469063673375 20928314740217203595510063)
  ·
    refine ⟨31392472110325805393265095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20928314740217203595510063 31392472110325805393265095)
    ·
      refine ⟨47088708165488708089897643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31392472110325805393265095 47088708165488708089897643)
      ·
        refine ⟨70633062248233062134846465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47088708165488708089897643 70633062248233062134846465)
        ·
          refine ⟨52974796686174796601134849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70633062248233062134846465 52974796686174796601134849)
          ·
            refine ⟨39731097514631097450851137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52974796686174796601134849 39731097514631097450851137)
            ·
              refine ⟨29798323135973323088138353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39731097514631097450851137 29798323135973323088138353)
              ·
                refine ⟨22348742351979992316103765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29798323135973323088138353 22348742351979992316103765)
                ·
                  refine ⟨261899324437265534954341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22348742351979992316103765 261899324437265534954341)
                  ·
                    rfl

theorem cell20_573803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_573803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573803 prefixEnd_573803 := by exact prefixLift 573803
  have htrace : WordTrace (prefixWord ++ tailWord_573803) baseStart_573803 baseEnd_573803 := by
    simpa [prefixWord, tailWord_573803, baseEnd_573803] using wordTrace_append hprefix tailTrace_573803
  have hstable : (prefixWord ++ tailWord_573803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573803).length < 2 ^ (prefixWord ++ tailWord_573803).sum := by decide
  have hdescent : baseEnd_573803 < baseStart_573803 := by decide
  rcases family_descends (prefixWord ++ tailWord_573803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573846 : List Nat := [5, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_573846 : Nat := 118140960795 + 573846 * 2 ^ 59
def prefixEnd_573846 : Nat := 4983230072969 + 3 ^ 40 * 573846 * 2
def baseEnd_573846 : Nat := 261918950808948496520833

theorem tailTrace_573846 : CollatzResearch.WordTrace tailWord_573846 prefixEnd_573846 261918950808948496520833 := by
  unfold tailWord_573846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308117692441338871207837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13953255386040947959550261 1308117692441338871207837)
  ·
    refine ⟨490544134665502076702939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1308117692441338871207837 490544134665502076702939)
    ·
      refine ⟨735816201998253115054409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 490544134665502076702939 735816201998253115054409)
      ·
        refine ⟨551862151498689836290807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 735816201998253115054409 551862151498689836290807)
        ·
          refine ⟨827793227248034754436211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 551862151498689836290807 827793227248034754436211)
          ·
            refine ⟨1241689840872052131654317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 827793227248034754436211 1241689840872052131654317)
            ·
              refine ⟨465633690327019549370369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1241689840872052131654317 465633690327019549370369)
              ·
                refine ⟨349225267745264662027777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465633690327019549370369 349225267745264662027777)
                ·
                  refine ⟨261918950808948496520833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349225267745264662027777 261918950808948496520833)
                  ·
                    rfl

theorem cell20_573846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_573846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573846 prefixEnd_573846 := by exact prefixLift 573846
  have htrace : WordTrace (prefixWord ++ tailWord_573846) baseStart_573846 baseEnd_573846 := by
    simpa [prefixWord, tailWord_573846, baseEnd_573846] using wordTrace_append hprefix tailTrace_573846
  have hstable : (prefixWord ++ tailWord_573846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573846).length < 2 ^ (prefixWord ++ tailWord_573846).sum := by decide
  have hdescent : baseEnd_573846 < baseStart_573846 := by decide
  rcases family_descends (prefixWord ++ tailWord_573846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573854 : List Nat := [4, 3, 1, 2, 1, 1, 3, 1, 4]
def baseStart_573854 : Nat := 118140960795 + 573854 * 2 ^ 59
def prefixEnd_573854 : Nat := 4983230072969 + 3 ^ 40 * 573854 * 2
def baseEnd_573854 : Nat := 261922602226936024254133

theorem tailTrace_573854 : CollatzResearch.WordTrace tailWord_573854 prefixEnd_573854 261922602226936024254133 := by
  unfold tailWord_573854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616271857879054913202077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13953449908688292870411077 2616271857879054913202077)
  ·
    refine ⟨981101946704645592450779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2616271857879054913202077 981101946704645592450779)
    ·
      refine ⟨1471652920056968388676169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981101946704645592450779 1471652920056968388676169)
      ·
        refine ⟨1103739690042726291507127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1471652920056968388676169 1103739690042726291507127)
        ·
          refine ⟨1655609535064089437260691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103739690042726291507127 1655609535064089437260691)
          ·
            refine ⟨2483414302596134155891037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655609535064089437260691 2483414302596134155891037)
            ·
              refine ⟨931280363473550308459139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2483414302596134155891037 931280363473550308459139)
              ·
                refine ⟨1396920545210325462688709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931280363473550308459139 1396920545210325462688709)
                ·
                  refine ⟨261922602226936024254133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1396920545210325462688709 261922602226936024254133)
                  ·
                    rfl

theorem cell20_573854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_573854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573854 prefixEnd_573854 := by exact prefixLift 573854
  have htrace : WordTrace (prefixWord ++ tailWord_573854) baseStart_573854 baseEnd_573854 := by
    simpa [prefixWord, tailWord_573854, baseEnd_573854] using wordTrace_append hprefix tailTrace_573854
  have hstable : (prefixWord ++ tailWord_573854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573854).length < 2 ^ (prefixWord ++ tailWord_573854).sum := by decide
  have hdescent : baseEnd_573854 < baseStart_573854 := by decide
  rcases family_descends (prefixWord ++ tailWord_573854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573864 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_573864 : Nat := 118140960795 + 573864 * 2 ^ 59
def prefixEnd_573864 : Nat := 4983230072969 + 3 ^ 40 * 573864 * 2
def baseEnd_573864 : Nat := 261927166499420433920759

theorem tailTrace_573864 : CollatzResearch.WordTrace tailWord_573864 prefixEnd_573864 261927166499420433920759 := by
  unfold tailWord_573864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465269796498105506740323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13953693061997474008987097 10465269796498105506740323)
  ·
    refine ⟨15697904694747158260110485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10465269796498105506740323 15697904694747158260110485)
    ·
      refine ⟨735839282566273043442679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15697904694747158260110485 735839282566273043442679)
      ·
        refine ⟨1103758923849409565164019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735839282566273043442679 1103758923849409565164019)
        ·
          refine ⟨1655638385774114347746029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1103758923849409565164019 1655638385774114347746029)
          ·
            refine ⟨620864394665292880404761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1655638385774114347746029 620864394665292880404761)
            ·
              refine ⟨465648295998969660303571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620864394665292880404761 465648295998969660303571)
              ·
                refine ⟨698472443998454490455357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 465648295998969660303571 698472443998454490455357)
                ·
                  refine ⟨261927166499420433920759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698472443998454490455357 261927166499420433920759)
                  ·
                    rfl

theorem cell20_573864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_573864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573864 prefixEnd_573864 := by exact prefixLift 573864
  have htrace : WordTrace (prefixWord ++ tailWord_573864) baseStart_573864 baseEnd_573864 := by
    simpa [prefixWord, tailWord_573864, baseEnd_573864] using wordTrace_append hprefix tailTrace_573864
  have hstable : (prefixWord ++ tailWord_573864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573864).length < 2 ^ (prefixWord ++ tailWord_573864).sum := by decide
  have hdescent : baseEnd_573864 < baseStart_573864 := by decide
  rcases family_descends (prefixWord ++ tailWord_573864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573909 : List Nat := [1, 3, 2, 3, 1, 4, 2, 2, 2]
def baseStart_573909 : Nat := 118140960795 + 573909 * 2 ^ 59
def prefixEnd_573909 : Nat := 4983230072969 + 3 ^ 40 * 573909 * 2
def baseEnd_573909 : Nat := 261947705725600277420575

theorem tailTrace_573909 : CollatzResearch.WordTrace tailWord_573909 prefixEnd_573909 261947705725600277420575 := by
  unfold tailWord_573909
  simp only [CollatzResearch.WordTrace]
  refine ⟨20932180877833183698868781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13954787251888789132579187 20932180877833183698868781)
  ·
    refine ⟨7849567829187443887075793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20932180877833183698868781 7849567829187443887075793)
    ·
      refine ⟨5887175871890582915306845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7849567829187443887075793 5887175871890582915306845)
      ·
        refine ⟨2207690951958968593240067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5887175871890582915306845 2207690951958968593240067)
        ·
          refine ⟨3311536427938452889860101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207690951958968593240067 3311536427938452889860101)
          ·
            refine ⟨620913080238459916848769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3311536427938452889860101 620913080238459916848769)
            ·
              refine ⟨465684810178844937636577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 620913080238459916848769 465684810178844937636577)
              ·
                refine ⟨349263607634133703227433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 465684810178844937636577 349263607634133703227433)
                ·
                  refine ⟨261947705725600277420575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349263607634133703227433 261947705725600277420575)
                  ·
                    rfl

theorem cell20_573909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_573909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573909 prefixEnd_573909 := by exact prefixLift 573909
  have htrace : WordTrace (prefixWord ++ tailWord_573909) baseStart_573909 baseEnd_573909 := by
    simpa [prefixWord, tailWord_573909, baseEnd_573909] using wordTrace_append hprefix tailTrace_573909
  have hstable : (prefixWord ++ tailWord_573909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573909).length < 2 ^ (prefixWord ++ tailWord_573909).sum := by decide
  have hdescent : baseEnd_573909 < baseStart_573909 := by decide
  rcases family_descends (prefixWord ++ tailWord_573909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573913 : List Nat := [1, 2, 1, 2, 4, 1, 3, 4, 2]
def baseStart_573913 : Nat := 118140960795 + 573913 * 2 ^ 59
def prefixEnd_573913 : Nat := 4983230072969 + 3 ^ 40 * 573913 * 2
def baseEnd_573913 : Nat := 261949531434594041287225

theorem tailTrace_573913 : CollatzResearch.WordTrace tailWord_573913 prefixEnd_573913 261949531434594041287225 := by
  unfold tailWord_573913
  simp only [CollatzResearch.WordTrace]
  refine ⟨20932326769818692382014393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13954884513212461588009595 20932326769818692382014393)
  ·
    refine ⟨15699245077364019286510795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20932326769818692382014393 15699245077364019286510795)
    ·
      refine ⟨23548867616046028929766193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15699245077364019286510795 23548867616046028929766193)
      ·
        refine ⟨17661650712034521697324645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23548867616046028929766193 17661650712034521697324645)
        ·
          refine ⟨3311559508506472818248371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17661650712034521697324645 3311559508506472818248371)
          ·
            refine ⟨4967339262759709227372557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311559508506472818248371 4967339262759709227372557)
            ·
              refine ⟨1862752223534890960264709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4967339262759709227372557 1862752223534890960264709)
              ·
                refine ⟨349266041912792055049633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1862752223534890960264709 349266041912792055049633)
                ·
                  refine ⟨261949531434594041287225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349266041912792055049633 261949531434594041287225)
                  ·
                    rfl

theorem cell20_573913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_573913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573913 prefixEnd_573913 := by exact prefixLift 573913
  have htrace : WordTrace (prefixWord ++ tailWord_573913) baseStart_573913 baseEnd_573913 := by
    simpa [prefixWord, tailWord_573913, baseEnd_573913] using wordTrace_append hprefix tailTrace_573913
  have hstable : (prefixWord ++ tailWord_573913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573913).length < 2 ^ (prefixWord ++ tailWord_573913).sum := by decide
  have hdescent : baseEnd_573913 < baseStart_573913 := by decide
  rcases family_descends (prefixWord ++ tailWord_573913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573927 : List Nat := [1, 1, 5, 2, 1, 1, 1, 5, 3]
def baseStart_573927 : Nat := 118140960795 + 573927 * 2 ^ 59
def prefixEnd_573927 : Nat := 4983230072969 + 3 ^ 40 * 573927 * 2
def baseEnd_573927 : Nat := 261955921416072214820501

theorem tailTrace_573927 : CollatzResearch.WordTrace tailWord_573927 prefixEnd_573927 261955921416072214820501 := by
  unfold tailWord_573927
  simp only [CollatzResearch.WordTrace]
  refine ⟨20932837391767972773024035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13955224927845315182016023 20932837391767972773024035)
  ·
    refine ⟨31399256087651959159536053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20932837391767972773024035 31399256087651959159536053)
    ·
      refine ⟨2943680258217371171206505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31399256087651959159536053 2943680258217371171206505)
      ·
        refine ⟨2207760193663028378404879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2943680258217371171206505 2207760193663028378404879)
        ·
          refine ⟨3311640290494542567607319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207760193663028378404879 3311640290494542567607319)
          ·
            refine ⟨4967460435741813851410979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311640290494542567607319 4967460435741813851410979)
            ·
              refine ⟨7451190653612720777116469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967460435741813851410979 7451190653612720777116469)
              ·
                refine ⟨698549123776192572854669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7451190653612720777116469 698549123776192572854669)
                ·
                  refine ⟨261955921416072214820501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698549123776192572854669 261955921416072214820501)
                  ·
                    rfl

theorem cell20_573927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_573927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573927 prefixEnd_573927 := by exact prefixLift 573927
  have htrace : WordTrace (prefixWord ++ tailWord_573927) baseStart_573927 baseEnd_573927 := by
    simpa [prefixWord, tailWord_573927, baseEnd_573927] using wordTrace_append hprefix tailTrace_573927
  have hstable : (prefixWord ++ tailWord_573927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573927).length < 2 ^ (prefixWord ++ tailWord_573927).sum := by decide
  have hdescent : baseEnd_573927 < baseStart_573927 := by decide
  rcases family_descends (prefixWord ++ tailWord_573927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573934 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_573934 : Nat := 118140960795 + 573934 * 2 ^ 59
def prefixEnd_573934 : Nat := 4983230072969 + 3 ^ 40 * 573934 * 2
def baseEnd_573934 : Nat := 261959116406811301587139

theorem tailTrace_573934 : CollatzResearch.WordTrace tailWord_573934 prefixEnd_573934 261959116406811301587139 := by
  unfold tailWord_573934
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616636587842826621066107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13955395135161741979019237 2616636587842826621066107)
  ·
    refine ⟨3924954881764239931599161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2616636587842826621066107 3924954881764239931599161)
    ·
      refine ⟨2943716161323179948699371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3924954881764239931599161 2943716161323179948699371)
      ·
        refine ⟨4415574241984769923049057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943716161323179948699371 4415574241984769923049057)
        ·
          refine ⟨3311680681488577442286793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4415574241984769923049057 3311680681488577442286793)
          ·
            refine ⟨2483760511116433081715095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3311680681488577442286793 2483760511116433081715095)
            ·
              refine ⟨3725640766674649622572643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483760511116433081715095 3725640766674649622572643)
              ·
                refine ⟨5588461150011974433858965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725640766674649622572643 5588461150011974433858965)
                ·
                  refine ⟨261959116406811301587139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5588461150011974433858965 261959116406811301587139)
                  ·
                    rfl

theorem cell20_573934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_573934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573934 prefixEnd_573934 := by exact prefixLift 573934
  have htrace : WordTrace (prefixWord ++ tailWord_573934) baseStart_573934 baseEnd_573934 := by
    simpa [prefixWord, tailWord_573934, baseEnd_573934] using wordTrace_append hprefix tailTrace_573934
  have hstable : (prefixWord ++ tailWord_573934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573934).length < 2 ^ (prefixWord ++ tailWord_573934).sum := by decide
  have hdescent : baseEnd_573934 < baseStart_573934 := by decide
  rcases family_descends (prefixWord ++ tailWord_573934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573948 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 5]
def baseStart_573948 : Nat := 118140960795 + 573948 * 2 ^ 59
def prefixEnd_573948 : Nat := 4983230072969 + 3 ^ 40 * 573948 * 2
def baseEnd_573948 : Nat := 261965506388289475120415

theorem tailTrace_573948 : CollatzResearch.WordTrace tailWord_573948 prefixEnd_573948 261965506388289475120415 := by
  unfold tailWord_573948
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466801662345946679769249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13955735549794595573025665 10466801662345946679769249)
  ·
    refine ⟨7850101246759460009826937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10466801662345946679769249 7850101246759460009826937)
    ·
      refine ⟨5887575935069595007370203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7850101246759460009826937 5887575935069595007370203)
      ·
        refine ⟨8831363902604392511055305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5887575935069595007370203 8831363902604392511055305)
        ·
          refine ⟨6623522926953294383291479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8831363902604392511055305 6623522926953294383291479)
          ·
            refine ⟨9935284390429941574937219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623522926953294383291479 9935284390429941574937219)
            ·
              refine ⟨14902926585644912362405829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9935284390429941574937219 14902926585644912362405829)
              ·
                refine ⟨2794298734808421067951093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14902926585644912362405829 2794298734808421067951093)
                ·
                  refine ⟨261965506388289475120415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2794298734808421067951093 261965506388289475120415)
                  ·
                    rfl

theorem cell20_573948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_573948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573948 prefixEnd_573948 := by exact prefixLift 573948
  have htrace : WordTrace (prefixWord ++ tailWord_573948) baseStart_573948 baseEnd_573948 := by
    simpa [prefixWord, tailWord_573948, baseEnd_573948] using wordTrace_append hprefix tailTrace_573948
  have hstable : (prefixWord ++ tailWord_573948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573948).length < 2 ^ (prefixWord ++ tailWord_573948).sum := by decide
  have hdescent : baseEnd_573948 < baseStart_573948 := by decide
  rcases family_descends (prefixWord ++ tailWord_573948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573951 : List Nat := [1, 1, 2, 2, 1, 2, 6, 3, 2]
def baseStart_573951 : Nat := 118140960795 + 573951 * 2 ^ 59
def prefixEnd_573951 : Nat := 4983230072969 + 3 ^ 40 * 573951 * 2
def baseEnd_573951 : Nat := 261966875670034798020403

theorem tailTrace_573951 : CollatzResearch.WordTrace tailWord_573951 prefixEnd_573951 261966875670034798020403 := by
  unfold tailWord_573951
  simp only [CollatzResearch.WordTrace]
  refine ⟨20933712743681024871897707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13955808495787349914598471 20933712743681024871897707)
  ·
    refine ⟨31400569115521537307846561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20933712743681024871897707 31400569115521537307846561)
    ·
      refine ⟨23550426836641152980884921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31400569115521537307846561 23550426836641152980884921)
      ·
        refine ⟨17662820127480864735663691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23550426836641152980884921 17662820127480864735663691)
        ·
          refine ⟨26494230191221297103495537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17662820127480864735663691 26494230191221297103495537)
          ·
            refine ⟨19870672643415972827621653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26494230191221297103495537 19870672643415972827621653)
            ·
              refine ⟨931437780160123726294765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19870672643415972827621653 931437780160123726294765)
              ·
                refine ⟨349289167560046397360537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 931437780160123726294765 349289167560046397360537)
                ·
                  refine ⟨261966875670034798020403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349289167560046397360537 261966875670034798020403)
                  ·
                    rfl

theorem cell20_573951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 2].length) (baseStart_573951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573951 prefixEnd_573951 := by exact prefixLift 573951
  have htrace : WordTrace (prefixWord ++ tailWord_573951) baseStart_573951 baseEnd_573951 := by
    simpa [prefixWord, tailWord_573951, baseEnd_573951] using wordTrace_append hprefix tailTrace_573951
  have hstable : (prefixWord ++ tailWord_573951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573951).length < 2 ^ (prefixWord ++ tailWord_573951).sum := by decide
  have hdescent : baseEnd_573951 < baseStart_573951 := by decide
  rcases family_descends (prefixWord ++ tailWord_573951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_573955 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_573955 : Nat := 118140960795 + 573955 * 2 ^ 59
def prefixEnd_573955 : Nat := 4983230072969 + 3 ^ 40 * 573955 * 2
def baseEnd_573955 : Nat := 261968701379028561887053

theorem tailTrace_573955 : CollatzResearch.WordTrace tailWord_573955 prefixEnd_573955 261968701379028561887053 := by
  unfold tailWord_573955
  simp only [CollatzResearch.WordTrace]
  refine ⟨20933858635666533555043319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13955905757111022370028879 20933858635666533555043319)
  ·
    refine ⟨31400787953499800332564979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20933858635666533555043319 31400787953499800332564979)
    ·
      refine ⟨47101181930249700498847469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31400787953499800332564979 47101181930249700498847469)
      ·
        refine ⟨17662943223843637687067801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47101181930249700498847469 17662943223843637687067801)
        ·
          refine ⟨13247207417882728265300851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17662943223843637687067801 13247207417882728265300851)
          ·
            refine ⟨19870811126824092397951277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247207417882728265300851 19870811126824092397951277)
            ·
              refine ⟨7451554172559034649231729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19870811126824092397951277 7451554172559034649231729)
              ·
                refine ⟨5588665629419275986923797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7451554172559034649231729 5588665629419275986923797)
                ·
                  refine ⟨261968701379028561887053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5588665629419275986923797 261968701379028561887053)
                  ·
                    rfl

theorem cell20_573955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_573955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_573955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_573955 prefixEnd_573955 := by exact prefixLift 573955
  have htrace : WordTrace (prefixWord ++ tailWord_573955) baseStart_573955 baseEnd_573955 := by
    simpa [prefixWord, tailWord_573955, baseEnd_573955] using wordTrace_append hprefix tailTrace_573955
  have hstable : (prefixWord ++ tailWord_573955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_573955).length < 2 ^ (prefixWord ++ tailWord_573955).sum := by decide
  have hdescent : baseEnd_573955 < baseStart_573955 := by decide
  rcases family_descends (prefixWord ++ tailWord_573955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574017 : List Nat := [1, 2, 5, 1, 1, 2, 8]
def baseStart_574017 : Nat := 118140960795 + 574017 * 2 ^ 59
def prefixEnd_574017 : Nat := 4983230072969 + 3 ^ 40 * 574017 * 2
def baseEnd_574017 : Nat := 29110777763159100202237

theorem tailTrace_574017 : CollatzResearch.WordTrace tailWord_574017 prefixEnd_574017 29110777763159100202237 := by
  unfold tailWord_574017
  simp only [CollatzResearch.WordTrace]
  refine ⟨20936119961441918143800305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13957413307627945429200203 20936119961441918143800305)
  ·
    refine ⟨15702089971081438607850229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20936119961441918143800305 15702089971081438607850229)
    ·
      refine ⟨1472070934788884869485959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15702089971081438607850229 1472070934788884869485959)
      ·
        refine ⟨2208106402183327304228939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472070934788884869485959 2208106402183327304228939)
        ·
          refine ⟨3312159603274990956343409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208106402183327304228939 3312159603274990956343409)
          ·
            refine ⟨2484119702456243217257557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3312159603274990956343409 2484119702456243217257557)
            ·
              refine ⟨29110777763159100202237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2484119702456243217257557 29110777763159100202237)
              ·
                rfl

theorem cell20_574017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 8].length) (baseStart_574017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574017 prefixEnd_574017 := by exact prefixLift 574017
  have htrace : WordTrace (prefixWord ++ tailWord_574017) baseStart_574017 baseEnd_574017 := by
    simpa [prefixWord, tailWord_574017, baseEnd_574017] using wordTrace_append hprefix tailTrace_574017
  have hstable : (prefixWord ++ tailWord_574017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574017).length < 2 ^ (prefixWord ++ tailWord_574017).sum := by decide
  have hdescent : baseEnd_574017 < baseStart_574017 := by decide
  rcases family_descends (prefixWord ++ tailWord_574017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574138 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_574138 : Nat := 118140960795 + 574138 * 2 ^ 59
def prefixEnd_574138 : Nat := 4983230072969 + 3 ^ 40 * 574138 * 2
def baseEnd_574138 : Nat := 262052227565493258786305

theorem tailTrace_574138 : CollatzResearch.WordTrace tailWord_574138 prefixEnd_574138 262052227565493258786305 := by
  unfold tailWord_574138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235133298500888952238767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13960355462669037205970045 5235133298500888952238767)
  ·
    refine ⟨7852699947751333428358151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5235133298500888952238767 7852699947751333428358151)
    ·
      refine ⟨11779049921627000142537227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7852699947751333428358151 11779049921627000142537227)
      ·
        refine ⟨17668574882440500213805841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11779049921627000142537227 17668574882440500213805841)
        ·
          refine ⟨13251431161830375160354381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17668574882440500213805841 13251431161830375160354381)
          ·
            refine ⟨4969286685686390685132893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13251431161830375160354381 4969286685686390685132893)
            ·
              refine ⟨1863482507132396506924835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4969286685686390685132893 1863482507132396506924835)
              ·
                refine ⟨2795223760698594760387253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863482507132396506924835 2795223760698594760387253)
                ·
                  refine ⟨262052227565493258786305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2795223760698594760387253 262052227565493258786305)
                  ·
                    rfl

theorem cell20_574138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_574138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574138 prefixEnd_574138 := by exact prefixLift 574138
  have htrace : WordTrace (prefixWord ++ tailWord_574138) baseStart_574138 baseEnd_574138 := by
    simpa [prefixWord, tailWord_574138, baseEnd_574138] using wordTrace_append hprefix tailTrace_574138
  have hstable : (prefixWord ++ tailWord_574138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574138).length < 2 ^ (prefixWord ++ tailWord_574138).sum := by decide
  have hdescent : baseEnd_574138 < baseStart_574138 := by decide
  rcases family_descends (prefixWord ++ tailWord_574138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574141 : List Nat := [1, 4, 1, 2, 1, 3, 2, 4, 2]
def baseStart_574141 : Nat := 118140960795 + 574141 * 2 ^ 59
def prefixEnd_574141 : Nat := 4983230072969 + 3 ^ 40 * 574141 * 2
def baseEnd_574141 : Nat := 262053596847238581686293

theorem tailTrace_574141 : CollatzResearch.WordTrace tailWord_574141 prefixEnd_574141 262053596847238581686293 := by
  unfold tailWord_574141
  simp only [CollatzResearch.WordTrace]
  refine ⟨20940642612992687321314277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13960428408661791547542851 20940642612992687321314277)
  ·
    refine ⟨3926370489936128872746427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20940642612992687321314277 3926370489936128872746427)
    ·
      refine ⟨5889555734904193309119641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3926370489936128872746427 5889555734904193309119641)
      ·
        refine ⟨4417166801178144981839731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5889555734904193309119641 4417166801178144981839731)
        ·
          refine ⟨6625750201767217472759597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4417166801178144981839731 6625750201767217472759597)
          ·
            refine ⟨2484656325662706552284849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6625750201767217472759597 2484656325662706552284849)
            ·
              refine ⟨1863492244247029914213637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2484656325662706552284849 1863492244247029914213637)
              ·
                refine ⟨349404795796318108915057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1863492244247029914213637 349404795796318108915057)
                ·
                  refine ⟨262053596847238581686293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349404795796318108915057 262053596847238581686293)
                  ·
                    rfl

theorem cell20_574141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_574141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574141 prefixEnd_574141 := by exact prefixLift 574141
  have htrace : WordTrace (prefixWord ++ tailWord_574141) baseStart_574141 baseEnd_574141 := by
    simpa [prefixWord, tailWord_574141, baseEnd_574141] using wordTrace_append hprefix tailTrace_574141
  have hstable : (prefixWord ++ tailWord_574141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574141).length < 2 ^ (prefixWord ++ tailWord_574141).sum := by decide
  have hdescent : baseEnd_574141 < baseStart_574141 := by decide
  rcases family_descends (prefixWord ++ tailWord_574141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574210 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_574210 : Nat := 118140960795 + 574210 * 2 ^ 59
def prefixEnd_574210 : Nat := 4983230072969 + 3 ^ 40 * 574210 * 2
def baseEnd_574210 : Nat := 262085090327381008386011

theorem tailTrace_574210 : CollatzResearch.WordTrace tailWord_574210 prefixEnd_574210 262085090327381008386011 := by
  unfold tailWord_574210
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235789812435678026394021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13962106166495141403717389 5235789812435678026394021)
  ·
    refine ⟨981710589831689629948879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5235789812435678026394021 981710589831689629948879)
    ·
      refine ⟨1472565884747534444923319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 981710589831689629948879 1472565884747534444923319)
      ·
        refine ⟨2208848827121301667384979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472565884747534444923319 2208848827121301667384979)
        ·
          refine ⟨3313273240681952501077469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208848827121301667384979 3313273240681952501077469)
          ·
            refine ⟨1242477465255732187904051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3313273240681952501077469 1242477465255732187904051)
            ·
              refine ⟨1863716197883598281856077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242477465255732187904051 1863716197883598281856077)
              ·
                refine ⟨698893574206349355696029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1863716197883598281856077 698893574206349355696029)
                ·
                  refine ⟨262085090327381008386011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 698893574206349355696029 262085090327381008386011)
                  ·
                    rfl

theorem cell20_574210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_574210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574210 prefixEnd_574210 := by exact prefixLift 574210
  have htrace : WordTrace (prefixWord ++ tailWord_574210) baseStart_574210 baseEnd_574210 := by
    simpa [prefixWord, tailWord_574210, baseEnd_574210] using wordTrace_append hprefix tailTrace_574210
  have hstable : (prefixWord ++ tailWord_574210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574210).length < 2 ^ (prefixWord ++ tailWord_574210).sum := by decide
  have hdescent : baseEnd_574210 < baseStart_574210 := by decide
  rcases family_descends (prefixWord ++ tailWord_574210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574290 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_574290 : Nat := 118140960795 + 574290 * 2 ^ 59
def prefixEnd_574290 : Nat := 4983230072969 + 3 ^ 40 * 574290 * 2
def baseEnd_574290 : Nat := 262121604507256285719017

theorem tailTrace_574290 : CollatzResearch.WordTrace tailWord_574290 prefixEnd_574290 262121604507256285719017 := by
  unfold tailWord_574290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236519272363221442122081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13964051392968590512325549 5236519272363221442122081)
  ·
    refine ⟨3927389454272416081591561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5236519272363221442122081 3927389454272416081591561)
    ·
      refine ⟨2945542090704312061193671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3927389454272416081591561 2945542090704312061193671)
      ·
        refine ⟨4418313136056468091790507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945542090704312061193671 4418313136056468091790507)
        ·
          refine ⟨6627469704084702137685761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4418313136056468091790507 6627469704084702137685761)
          ·
            refine ⟨4970602278063526603264321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6627469704084702137685761 4970602278063526603264321)
            ·
              refine ⟨3727951708547644952448241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4970602278063526603264321 3727951708547644952448241)
              ·
                refine ⟨2795963781410733714336181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3727951708547644952448241 2795963781410733714336181)
                ·
                  refine ⟨262121604507256285719017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2795963781410733714336181 262121604507256285719017)
                  ·
                    rfl

theorem cell20_574290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_574290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574290 prefixEnd_574290 := by exact prefixLift 574290
  have htrace : WordTrace (prefixWord ++ tailWord_574290) baseStart_574290 baseEnd_574290 := by
    simpa [prefixWord, tailWord_574290, baseEnd_574290] using wordTrace_append hprefix tailTrace_574290
  have hstable : (prefixWord ++ tailWord_574290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574290).length < 2 ^ (prefixWord ++ tailWord_574290).sum := by decide
  have hdescent : baseEnd_574290 < baseStart_574290 := by decide
  rcases family_descends (prefixWord ++ tailWord_574290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574293 : List Nat := [1, 3, 2, 2, 2, 1, 4, 3, 2]
def baseStart_574293 : Nat := 118140960795 + 574293 * 2 ^ 59
def prefixEnd_574293 : Nat := 4983230072969 + 3 ^ 40 * 574293 * 2
def baseEnd_574293 : Nat := 262122973789001608619005

theorem tailTrace_574293 : CollatzResearch.WordTrace tailWord_574293 prefixEnd_574293 262122973789001608619005 := by
  unfold tailWord_574293
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946186508442017280847533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13964124338961344853898355 20946186508442017280847533)
  ·
    refine ⟨7854819940665756480317825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20946186508442017280847533 7854819940665756480317825)
    ·
      refine ⟨5891114955499317360238369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7854819940665756480317825 5891114955499317360238369)
      ·
        refine ⟨4418336216624488020178777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5891114955499317360238369 4418336216624488020178777)
        ·
          refine ⟨3313752162468366015134083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4418336216624488020178777 3313752162468366015134083)
          ·
            refine ⟨4970628243702549022701125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313752162468366015134083 4970628243702549022701125)
            ·
              refine ⟨931992795694227941756461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4970628243702549022701125 931992795694227941756461)
              ·
                refine ⟨349497298385335478158673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 931992795694227941756461 349497298385335478158673)
                ·
                  refine ⟨262122973789001608619005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349497298385335478158673 262122973789001608619005)
                  ·
                    rfl

theorem cell20_574293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_574293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574293 prefixEnd_574293 := by exact prefixLift 574293
  have htrace : WordTrace (prefixWord ++ tailWord_574293) baseStart_574293 baseEnd_574293 := by
    simpa [prefixWord, tailWord_574293, baseEnd_574293] using wordTrace_append hprefix tailTrace_574293
  have hstable : (prefixWord ++ tailWord_574293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574293).length < 2 ^ (prefixWord ++ tailWord_574293).sum := by decide
  have hdescent : baseEnd_574293 < baseStart_574293 := by decide
  rcases family_descends (prefixWord ++ tailWord_574293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574304 : List Nat := [2, 1, 1, 3, 3, 1, 9]
def baseStart_574304 : Nat := 118140960795 + 574304 * 2 ^ 59
def prefixEnd_574304 : Nat := 4983230072969 + 3 ^ 40 * 574304 * 2
def baseEnd_574304 : Nat := 29125332720970495472477

theorem tailTrace_574304 : CollatzResearch.WordTrace tailWord_574304 prefixEnd_574304 29125332720970495472477 := by
  unfold tailWord_574304
  simp only [CollatzResearch.WordTrace]
  refine ⟨10473293855701083079748983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13964391807601444106331977 10473293855701083079748983)
  ·
    refine ⟨15709940783551624619623475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10473293855701083079748983 15709940783551624619623475)
    ·
      refine ⟨23564911175327436929435213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15709940783551624619623475 23564911175327436929435213)
      ·
        refine ⟨8836841690747788848538205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23564911175327436929435213 8836841690747788848538205)
        ·
          refine ⟨3313815634030420818201827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8836841690747788848538205 3313815634030420818201827)
          ·
            refine ⟨4970723451045631227302741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313815634030420818201827 4970723451045631227302741)
            ·
              refine ⟨29125332720970495472477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4970723451045631227302741 29125332720970495472477)
              ·
                rfl

theorem cell20_574304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 9].length) (baseStart_574304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574304 prefixEnd_574304 := by exact prefixLift 574304
  have htrace : WordTrace (prefixWord ++ tailWord_574304) baseStart_574304 baseEnd_574304 := by
    simpa [prefixWord, tailWord_574304, baseEnd_574304] using wordTrace_append hprefix tailTrace_574304
  have hstable : (prefixWord ++ tailWord_574304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574304).length < 2 ^ (prefixWord ++ tailWord_574304).sum := by decide
  have hdescent : baseEnd_574304 < baseStart_574304 := by decide
  rcases family_descends (prefixWord ++ tailWord_574304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574307 : List Nat := [1, 1, 1, 5, 3, 1, 3, 2, 3]
def baseStart_574307 : Nat := 118140960795 + 574307 * 2 ^ 59
def prefixEnd_574307 : Nat := 4983230072969 + 3 ^ 40 * 574307 * 2
def baseEnd_574307 : Nat := 262129363770479782152281

theorem tailTrace_574307 : CollatzResearch.WordTrace tailWord_574307 prefixEnd_574307 262129363770479782152281 := by
  unfold tailWord_574307
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946697130391297671857175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13964464753594198447904783 20946697130391297671857175)
  ·
    refine ⟨31420045695586946507785763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20946697130391297671857175 31420045695586946507785763)
    ·
      refine ⟨47130068543380419761678645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31420045695586946507785763 47130068543380419761678645)
      ·
        refine ⟨4418443925941914352657373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47130068543380419761678645 4418443925941914352657373)
        ·
          refine ⟨1656916472228217882246515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4418443925941914352657373 1656916472228217882246515)
          ·
            refine ⟨2485374708342326823369773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656916472228217882246515 2485374708342326823369773)
            ·
              refine ⟨932015515628372558763665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2485374708342326823369773 932015515628372558763665)
              ·
                refine ⟨699011636721279419072749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932015515628372558763665 699011636721279419072749)
                ·
                  refine ⟨262129363770479782152281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699011636721279419072749 262129363770479782152281)
                  ·
                    rfl

theorem cell20_574307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_574307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574307 prefixEnd_574307 := by exact prefixLift 574307
  have htrace : WordTrace (prefixWord ++ tailWord_574307) baseStart_574307 baseEnd_574307 := by
    simpa [prefixWord, tailWord_574307, baseEnd_574307] using wordTrace_append hprefix tailTrace_574307
  have hstable : (prefixWord ++ tailWord_574307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574307).length < 2 ^ (prefixWord ++ tailWord_574307).sum := by decide
  have hdescent : baseEnd_574307 < baseStart_574307 := by decide
  rcases family_descends (prefixWord ++ tailWord_574307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574334 : List Nat := [4, 2, 3, 1, 2, 2, 2, 4]
def baseStart_574334 : Nat := 118140960795 + 574334 * 2 ^ 59
def prefixEnd_574334 : Nat := 4983230072969 + 3 ^ 40 * 574334 * 2
def baseEnd_574334 : Nat := 87380562435395896084057

theorem tailTrace_574334 : CollatzResearch.WordTrace tailWord_574334 prefixEnd_574334 87380562435395896084057 := by
  unfold tailWord_574334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618460237661685160386257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13965121267528987522060037 2618460237661685160386257)
  ·
    refine ⟨1963845178246263870289693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2618460237661685160386257 1963845178246263870289693)
    ·
      refine ⟨736441941842348951358635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1963845178246263870289693 736441941842348951358635)
      ·
        refine ⟨1104662912763523427037953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736441941842348951358635 1104662912763523427037953)
        ·
          refine ⟨828497184572642570278465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1104662912763523427037953 828497184572642570278465)
          ·
            refine ⟨621372888429481927708849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828497184572642570278465 621372888429481927708849)
            ·
              refine ⟨466029666322111445781637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621372888429481927708849 466029666322111445781637)
              ·
                refine ⟨87380562435395896084057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466029666322111445781637 87380562435395896084057)
                ·
                  rfl

theorem cell20_574334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_574334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574334 prefixEnd_574334 := by exact prefixLift 574334
  have htrace : WordTrace (prefixWord ++ tailWord_574334) baseStart_574334 baseEnd_574334 := by
    simpa [prefixWord, tailWord_574334, baseEnd_574334] using wordTrace_append hprefix tailTrace_574334
  have hstable : (prefixWord ++ tailWord_574334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574334).length < 2 ^ (prefixWord ++ tailWord_574334).sum := by decide
  have hdescent : baseEnd_574334 < baseStart_574334 := by decide
  rcases family_descends (prefixWord ++ tailWord_574334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574335 : List Nat := [1, 1, 2, 2, 1, 1, 6, 2, 4]
def baseStart_574335 : Nat := 118140960795 + 574335 * 2 ^ 59
def prefixEnd_574335 : Nat := 4983230072969 + 3 ^ 40 * 574335 * 2
def baseEnd_574335 : Nat := 262142143733436129218833

theorem tailTrace_574335 : CollatzResearch.WordTrace tailWord_574335 prefixEnd_574335 262142143733436129218833 := by
  unfold tailWord_574335
  simp only [CollatzResearch.WordTrace]
  refine ⟨20947718374289858453876459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13965145582859905635917639 20947718374289858453876459)
  ·
    refine ⟨31421577561434787680814689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20947718374289858453876459 31421577561434787680814689)
    ·
      refine ⟨23566183171076090760611017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31421577561434787680814689 23566183171076090760611017)
      ·
        refine ⟨17674637378307068070458263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23566183171076090760611017 17674637378307068070458263)
        ·
          refine ⟨26511956067460602105687395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17674637378307068070458263 26511956067460602105687395)
          ·
            refine ⟨39767934101190903158531093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26511956067460602105687395 39767934101190903158531093)
            ·
              refine ⟨1864121910993323585556145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39767934101190903158531093 1864121910993323585556145)
              ·
                refine ⟨1398091433244992689167109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864121910993323585556145 1398091433244992689167109)
                ·
                  refine ⟨262142143733436129218833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398091433244992689167109 262142143733436129218833)
                  ·
                    rfl

theorem cell20_574335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2, 4].length) (baseStart_574335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574335 prefixEnd_574335 := by exact prefixLift 574335
  have htrace : WordTrace (prefixWord ++ tailWord_574335) baseStart_574335 baseEnd_574335 := by
    simpa [prefixWord, tailWord_574335, baseEnd_574335] using wordTrace_append hprefix tailTrace_574335
  have hstable : (prefixWord ++ tailWord_574335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574335).length < 2 ^ (prefixWord ++ tailWord_574335).sum := by decide
  have hdescent : baseEnd_574335 < baseStart_574335 := by decide
  rcases family_descends (prefixWord ++ tailWord_574335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574369 : List Nat := [1, 2, 3, 4, 1, 3, 1, 1, 4]
def baseStart_574369 : Nat := 118140960795 + 574369 * 2 ^ 59
def prefixEnd_574369 : Nat := 4983230072969 + 3 ^ 40 * 574369 * 2
def baseEnd_574369 : Nat := 262157662259883122085361

theorem tailTrace_574369 : CollatzResearch.WordTrace tailWord_574369 prefixEnd_574369 262157662259883122085361 := by
  unfold tailWord_574369
  simp only [CollatzResearch.WordTrace]
  refine ⟨20948958456166682260614161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13965972304111121507076107 20948958456166682260614161)
  ·
    refine ⟨15711718842125011695460621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20948958456166682260614161 15711718842125011695460621)
    ·
      refine ⟨5891894565796879385797733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15711718842125011695460621 5891894565796879385797733)
      ·
        refine ⟨1104730231086914884837075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5891894565796879385797733 1104730231086914884837075)
        ·
          refine ⟨1657095346630372327255613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104730231086914884837075 1657095346630372327255613)
          ·
            refine ⟨621410754986389622720855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1657095346630372327255613 621410754986389622720855)
            ·
              refine ⟨932116132479584434081283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621410754986389622720855 932116132479584434081283)
              ·
                refine ⟨1398174198719376651121925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932116132479584434081283 1398174198719376651121925)
                ·
                  refine ⟨262157662259883122085361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398174198719376651121925 262157662259883122085361)
                  ·
                    rfl

theorem cell20_574369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_574369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574369 prefixEnd_574369 := by exact prefixLift 574369
  have htrace : WordTrace (prefixWord ++ tailWord_574369) baseStart_574369 baseEnd_574369 := by
    simpa [prefixWord, tailWord_574369, baseEnd_574369] using wordTrace_append hprefix tailTrace_574369
  have hstable : (prefixWord ++ tailWord_574369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574369).length < 2 ^ (prefixWord ++ tailWord_574369).sum := by decide
  have hdescent : baseEnd_574369 < baseStart_574369 := by decide
  rcases family_descends (prefixWord ++ tailWord_574369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574387 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_574387 : Nat := 118140960795 + 574387 * 2 ^ 59
def prefixEnd_574387 : Nat := 4983230072969 + 3 ^ 40 * 574387 * 2
def baseEnd_574387 : Nat := 262165877950355059485287

theorem tailTrace_574387 : CollatzResearch.WordTrace tailWord_574387 prefixEnd_574387 262165877950355059485287 := by
  unfold tailWord_574387
  simp only [CollatzResearch.WordTrace]
  refine ⟨20949614970101471334769415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13966409980067647556512943 20949614970101471334769415)
  ·
    refine ⟨31424422455152207002154123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20949614970101471334769415 31424422455152207002154123)
    ·
      refine ⟨47136633682728310503231185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31424422455152207002154123 47136633682728310503231185)
      ·
        refine ⟨35352475262046232877423389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47136633682728310503231185 35352475262046232877423389)
        ·
          refine ⟨13257178223267337329033771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35352475262046232877423389 13257178223267337329033771)
          ·
            refine ⟨19885767334901005993550657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13257178223267337329033771 19885767334901005993550657)
            ·
              refine ⟨14914325501175754495162993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19885767334901005993550657 14914325501175754495162993)
              ·
                refine ⟨11185744125881815871372245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14914325501175754495162993 11185744125881815871372245)
                ·
                  refine ⟨262165877950355059485287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11185744125881815871372245 262165877950355059485287)
                  ·
                    rfl

theorem cell20_574387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_574387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574387 prefixEnd_574387 := by exact prefixLift 574387
  have htrace : WordTrace (prefixWord ++ tailWord_574387) baseStart_574387 baseEnd_574387 := by
    simpa [prefixWord, tailWord_574387, baseEnd_574387] using wordTrace_append hprefix tailTrace_574387
  have hstable : (prefixWord ++ tailWord_574387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574387).length < 2 ^ (prefixWord ++ tailWord_574387).sum := by decide
  have hdescent : baseEnd_574387 < baseStart_574387 := by decide
  rcases family_descends (prefixWord ++ tailWord_574387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574424 : List Nat := [2, 1, 2, 2, 2, 5, 2, 2, 2]
def baseStart_574424 : Nat := 118140960795 + 574424 * 2 ^ 59
def prefixEnd_574424 : Nat := 4983230072969 + 3 ^ 40 * 574424 * 2
def baseEnd_574424 : Nat := 262182765758547375251803

theorem tailTrace_574424 : CollatzResearch.WordTrace tailWord_574424 prefixEnd_574424 262182765758547375251803 := by
  unfold tailWord_574424
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475482235483713326933163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13967309647311617769244217 10475482235483713326933163)
  ·
    refine ⟨15713223353225569990399745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10475482235483713326933163 15713223353225569990399745)
    ·
      refine ⟨11784917514919177492799809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15713223353225569990399745 11784917514919177492799809)
      ·
        refine ⟨8838688136189383119599857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11784917514919177492799809 8838688136189383119599857)
        ·
          refine ⟨6629016102142037339699893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8838688136189383119599857 6629016102142037339699893)
          ·
            refine ⟨621470259575816000596865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6629016102142037339699893 621470259575816000596865)
            ·
              refine ⟨466102694681862000447649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621470259575816000596865 466102694681862000447649)
              ·
                refine ⟨349577021011396500335737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466102694681862000447649 349577021011396500335737)
                ·
                  refine ⟨262182765758547375251803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349577021011396500335737 262182765758547375251803)
                  ·
                    rfl

theorem cell20_574424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_574424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574424 prefixEnd_574424 := by exact prefixLift 574424
  have htrace : WordTrace (prefixWord ++ tailWord_574424) baseStart_574424 baseEnd_574424 := by
    simpa [prefixWord, tailWord_574424, baseEnd_574424] using wordTrace_append hprefix tailTrace_574424
  have hstable : (prefixWord ++ tailWord_574424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574424).length < 2 ^ (prefixWord ++ tailWord_574424).sum := by decide
  have hdescent : baseEnd_574424 < baseStart_574424 := by decide
  rcases family_descends (prefixWord ++ tailWord_574424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574449 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_574449 : Nat := 118140960795 + 574449 * 2 ^ 59
def prefixEnd_574449 : Nat := 4983230072969 + 3 ^ 40 * 574449 * 2
def baseEnd_574449 : Nat := 262194176439758399418367

theorem tailTrace_574449 : CollatzResearch.WordTrace tailWord_574449 prefixEnd_574449 262194176439758399418367 := by
  unfold tailWord_574449
  simp only [CollatzResearch.WordTrace]
  refine ⟨20951876295876855923526401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13967917530584570615684267 20951876295876855923526401)
  ·
    refine ⟨15713907221907641942644801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20951876295876855923526401 15713907221907641942644801)
    ·
      refine ⟨11785430416430731456983601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15713907221907641942644801 11785430416430731456983601)
      ·
        refine ⟨8839072812323048592737701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11785430416430731456983601 8839072812323048592737701)
        ·
          refine ⟨1657326152310571611138319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8839072812323048592737701 1657326152310571611138319)
          ·
            refine ⟨2485989228465857416707479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657326152310571611138319 2485989228465857416707479)
            ·
              refine ⟨3728983842698786125061219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485989228465857416707479 3728983842698786125061219)
              ·
                refine ⟨5593475764048179187591829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3728983842698786125061219 5593475764048179187591829)
                ·
                  refine ⟨262194176439758399418367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5593475764048179187591829 262194176439758399418367)
                  ·
                    rfl

theorem cell20_574449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_574449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574449 prefixEnd_574449 := by exact prefixLift 574449
  have htrace : WordTrace (prefixWord ++ tailWord_574449) baseStart_574449 baseEnd_574449 := by
    simpa [prefixWord, tailWord_574449, baseEnd_574449] using wordTrace_append hprefix tailTrace_574449
  have hstable : (prefixWord ++ tailWord_574449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574449).length < 2 ^ (prefixWord ++ tailWord_574449).sum := by decide
  have hdescent : baseEnd_574449 < baseStart_574449 := by decide
  rcases family_descends (prefixWord ++ tailWord_574449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574521 : List Nat := [1, 2, 1, 5, 2, 1, 3, 3, 2]
def baseStart_574521 : Nat := 118140960795 + 574521 * 2 ^ 59
def prefixEnd_574521 : Nat := 4983230072969 + 3 ^ 40 * 574521 * 2
def baseEnd_574521 : Nat := 262227039201646149018073

theorem tailTrace_574521 : CollatzResearch.WordTrace tailWord_574521 prefixEnd_574521 262227039201646149018073 := by
  unfold tailWord_574521
  simp only [CollatzResearch.WordTrace]
  refine ⟨20954502351616012220147417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13969668234410674813431611 20954502351616012220147417)
  ·
    refine ⟨15715876763712009165110563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20954502351616012220147417 15715876763712009165110563)
    ·
      refine ⟨23573815145568013747665845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15715876763712009165110563 23573815145568013747665845)
      ·
        refine ⟨2210045169897001288843673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23573815145568013747665845 2210045169897001288843673)
        ·
          refine ⟨1657533877422750966632755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210045169897001288843673 1657533877422750966632755)
          ·
            refine ⟨2486300816134126449949133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1657533877422750966632755 2486300816134126449949133)
            ·
              refine ⟨932362806050297418730925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2486300816134126449949133 932362806050297418730925)
              ·
                refine ⟨349636052268861532024097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 932362806050297418730925 349636052268861532024097)
                ·
                  refine ⟨262227039201646149018073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349636052268861532024097 262227039201646149018073)
                  ·
                    rfl

theorem cell20_574521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_574521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574521 prefixEnd_574521 := by exact prefixLift 574521
  have htrace : WordTrace (prefixWord ++ tailWord_574521) baseStart_574521 baseEnd_574521 := by
    simpa [prefixWord, tailWord_574521, baseEnd_574521] using wordTrace_append hprefix tailTrace_574521
  have hstable : (prefixWord ++ tailWord_574521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574521).length < 2 ^ (prefixWord ++ tailWord_574521).sum := by decide
  have hdescent : baseEnd_574521 < baseStart_574521 := by decide
  rcases family_descends (prefixWord ++ tailWord_574521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574577 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_574577 : Nat := 118140960795 + 574577 * 2 ^ 59
def prefixEnd_574577 : Nat := 4983230072969 + 3 ^ 40 * 574577 * 2
def baseEnd_574577 : Nat := 262252599127558843151177

theorem tailTrace_574577 : CollatzResearch.WordTrace tailWord_574577 prefixEnd_574577 262252599127558843151177 := by
  unfold tailWord_574577
  simp only [CollatzResearch.WordTrace]
  refine ⟨20956544839413133784185985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13971029892942089189457323 20956544839413133784185985)
  ·
    refine ⟨15717408629559850338139489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20956544839413133784185985 15717408629559850338139489)
    ·
      refine ⟨11788056472169887753604617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15717408629559850338139489 11788056472169887753604617)
      ·
        refine ⟨8841042354127415815203463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11788056472169887753604617 8841042354127415815203463)
        ·
          refine ⟨13261563531191123722805195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8841042354127415815203463 13261563531191123722805195)
          ·
            refine ⟨19892345296786685584207793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13261563531191123722805195 19892345296786685584207793)
            ·
              refine ⟨14919258972590014188155845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19892345296786685584207793 14919258972590014188155845)
              ·
                refine ⟨2797361057360627660279221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14919258972590014188155845 2797361057360627660279221)
                ·
                  refine ⟨262252599127558843151177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2797361057360627660279221 262252599127558843151177)
                  ·
                    rfl

theorem cell20_574577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_574577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574577 prefixEnd_574577 := by exact prefixLift 574577
  have htrace : WordTrace (prefixWord ++ tailWord_574577) baseStart_574577 baseEnd_574577 := by
    simpa [prefixWord, tailWord_574577, baseEnd_574577] using wordTrace_append hprefix tailTrace_574577
  have hstable : (prefixWord ++ tailWord_574577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574577).length < 2 ^ (prefixWord ++ tailWord_574577).sum := by decide
  have hdescent : baseEnd_574577 < baseStart_574577 := by decide
  rcases family_descends (prefixWord ++ tailWord_574577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574597 : List Nat := [1, 3, 1, 1, 6, 1, 1, 4, 2]
def baseStart_574597 : Nat := 118140960795 + 574597 * 2 ^ 59
def prefixEnd_574597 : Nat := 4983230072969 + 3 ^ 40 * 574597 * 2
def baseEnd_574597 : Nat := 262261727672527662484429

theorem tailTrace_574597 : CollatzResearch.WordTrace tailWord_574597 prefixEnd_574597 262261727672527662484429 := by
  unfold tailWord_574597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20957274299340677199914045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13971516199560451466609363 20957274299340677199914045)
  ·
    refine ⟨7858977862252753949967767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20957274299340677199914045 7858977862252753949967767)
    ·
      refine ⟨11788466793379130924951651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7858977862252753949967767 11788466793379130924951651)
      ·
        refine ⟨17682700190068696387427477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11788466793379130924951651 17682700190068696387427477)
        ·
          refine ⟨828876571409470143160663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17682700190068696387427477 828876571409470143160663)
          ·
            refine ⟨1243314857114205214740995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828876571409470143160663 1243314857114205214740995)
            ·
              refine ⟨1864972285671307822111493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243314857114205214740995 1864972285671307822111493)
              ·
                refine ⟨349682303563370216645905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1864972285671307822111493 349682303563370216645905)
                ·
                  refine ⟨262261727672527662484429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349682303563370216645905 262261727672527662484429)
                  ·
                    rfl

theorem cell20_574597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_574597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574597 prefixEnd_574597 := by exact prefixLift 574597
  have htrace : WordTrace (prefixWord ++ tailWord_574597) baseStart_574597 baseEnd_574597 := by
    simpa [prefixWord, tailWord_574597, baseEnd_574597] using wordTrace_append hprefix tailTrace_574597
  have hstable : (prefixWord ++ tailWord_574597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574597).length < 2 ^ (prefixWord ++ tailWord_574597).sum := by decide
  have hdescent : baseEnd_574597 < baseStart_574597 := by decide
  rcases family_descends (prefixWord ++ tailWord_574597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574618 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 4]
def baseStart_574618 : Nat := 118140960795 + 574618 * 2 ^ 59
def prefixEnd_574618 : Nat := 4983230072969 + 3 ^ 40 * 574618 * 2
def baseEnd_574618 : Nat := 262271312644744922784343

theorem tailTrace_574618 : CollatzResearch.WordTrace tailWord_574618 prefixEnd_574618 262271312644744922784343 := by
  unfold tailWord_574618
  simp only [CollatzResearch.WordTrace]
  refine ⟨5239510058066149446607127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13972026821509731857619005 5239510058066149446607127)
  ·
    refine ⟨7859265087099224169910691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5239510058066149446607127 7859265087099224169910691)
    ·
      refine ⟨11788897630648836254866037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7859265087099224169910691 11788897630648836254866037)
      ·
        refine ⟨1105209152873328398893691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11788897630648836254866037 1105209152873328398893691)
        ·
          refine ⟨1657813729309992598340537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1105209152873328398893691 1657813729309992598340537)
          ·
            refine ⟨1243360296982494448755403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1657813729309992598340537 1243360296982494448755403)
            ·
              refine ⟨1865040445473741673133105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243360296982494448755403 1865040445473741673133105)
              ·
                refine ⟨1398780334105306254849829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865040445473741673133105 1398780334105306254849829)
                ·
                  refine ⟨262271312644744922784343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398780334105306254849829 262271312644744922784343)
                  ·
                    rfl

theorem cell20_574618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_574618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574618 prefixEnd_574618 := by exact prefixLift 574618
  have htrace : WordTrace (prefixWord ++ tailWord_574618) baseStart_574618 baseEnd_574618 := by
    simpa [prefixWord, tailWord_574618, baseEnd_574618] using wordTrace_append hprefix tailTrace_574618
  have hstable : (prefixWord ++ tailWord_574618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574618).length < 2 ^ (prefixWord ++ tailWord_574618).sum := by decide
  have hdescent : baseEnd_574618 < baseStart_574618 := by decide
  rcases family_descends (prefixWord ++ tailWord_574618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574625 : List Nat := [1, 2, 3, 3, 1, 1, 5, 4]
def baseStart_574625 : Nat := 118140960795 + 574625 * 2 ^ 59
def prefixEnd_574625 : Nat := 4983230072969 + 3 ^ 40 * 574625 * 2
def baseEnd_574625 : Nat := 87424835878494669850327

theorem tailTrace_574625 : CollatzResearch.WordTrace tailWord_574625 prefixEnd_574625 87424835878494669850327 := by
  unfold tailWord_574625
  simp only [CollatzResearch.WordTrace]
  refine ⟨20958295543239237981933329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13972197028826158654622219 20958295543239237981933329)
  ·
    refine ⟨15718721657429428486449997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20958295543239237981933329 15718721657429428486449997)
    ·
      refine ⟨5894520621536035682418749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15718721657429428486449997 5894520621536035682418749)
      ·
        refine ⟨2210445233076013380907031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5894520621536035682418749 2210445233076013380907031)
        ·
          refine ⟨3315667849614020071360547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210445233076013380907031 3315667849614020071360547)
          ·
            refine ⟨4973501774421030107040821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315667849614020071360547 4973501774421030107040821)
            ·
              refine ⟨466265791351971572535077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4973501774421030107040821 466265791351971572535077)
              ·
                refine ⟨87424835878494669850327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466265791351971572535077 87424835878494669850327)
                ·
                  rfl

theorem cell20_574625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_574625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574625 prefixEnd_574625 := by exact prefixLift 574625
  have htrace : WordTrace (prefixWord ++ tailWord_574625) baseStart_574625 baseEnd_574625 := by
    simpa [prefixWord, tailWord_574625, baseEnd_574625] using wordTrace_append hprefix tailTrace_574625
  have hstable : (prefixWord ++ tailWord_574625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574625).length < 2 ^ (prefixWord ++ tailWord_574625).sum := by decide
  have hdescent : baseEnd_574625 < baseStart_574625 := by decide
  rcases family_descends (prefixWord ++ tailWord_574625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574649 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 3]
def baseStart_574649 : Nat := 118140960795 + 574649 * 2 ^ 59
def prefixEnd_574649 : Nat := 4983230072969 + 3 ^ 40 * 574649 * 2
def baseEnd_574649 : Nat := 262285461889446592750883

theorem tailTrace_574649 : CollatzResearch.WordTrace tailWord_574649 prefixEnd_574649 262285461889446592750883 := by
  unfold tailWord_574649
  simp only [CollatzResearch.WordTrace]
  refine ⟨20959170895152290080807001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13972780596768193387204667 20959170895152290080807001)
  ·
    refine ⟨15719378171364217560605251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20959170895152290080807001 15719378171364217560605251)
    ·
      refine ⟨23579067257046326340907877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15719378171364217560605251 23579067257046326340907877)
      ·
        refine ⟨4421075110696186188920227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23579067257046326340907877 4421075110696186188920227)
        ·
          refine ⟨6631612666044279283380341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4421075110696186188920227 6631612666044279283380341)
          ·
            refine ⟨621713687441651182816907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6631612666044279283380341 621713687441651182816907)
            ·
              refine ⟨932570531162476774225361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 621713687441651182816907 932570531162476774225361)
              ·
                refine ⟨699427898371857580669021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932570531162476774225361 699427898371857580669021)
                ·
                  refine ⟨262285461889446592750883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 699427898371857580669021 262285461889446592750883)
                  ·
                    rfl

theorem cell20_574649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_574649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574649 prefixEnd_574649 := by exact prefixLift 574649
  have htrace : WordTrace (prefixWord ++ tailWord_574649) baseStart_574649 baseEnd_574649 := by
    simpa [prefixWord, tailWord_574649, baseEnd_574649] using wordTrace_append hprefix tailTrace_574649
  have hstable : (prefixWord ++ tailWord_574649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574649).length < 2 ^ (prefixWord ++ tailWord_574649).sum := by decide
  have hdescent : baseEnd_574649 < baseStart_574649 := by decide
  rcases family_descends (prefixWord ++ tailWord_574649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574656 : List Nat := [2, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_574656 : Nat := 118140960795 + 574656 * 2 ^ 59
def prefixEnd_574656 : Nat := 4983230072969 + 3 ^ 40 * 574656 * 2
def baseEnd_574656 : Nat := 262288656880185679517521

theorem tailTrace_574656 : CollatzResearch.WordTrace tailWord_574656 prefixEnd_574656 262288656880185679517521 := by
  unfold tailWord_574656
  simp only [CollatzResearch.WordTrace]
  refine ⟨10479713103063465138155911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13972950804084620184207881 10479713103063465138155911)
  ·
    refine ⟨15719569654595197707233867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10479713103063465138155911 15719569654595197707233867)
    ·
      refine ⟨23579354481892796560850801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15719569654595197707233867 23579354481892796560850801)
      ·
        refine ⟨17684515861419597420638101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23579354481892796560850801 17684515861419597420638101)
        ·
          refine ⟨828961681004043629092411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17684515861419597420638101 828961681004043629092411)
          ·
            refine ⟨1243442521506065443638617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 828961681004043629092411 1243442521506065443638617)
            ·
              refine ⟨932581891129549082728963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1243442521506065443638617 932581891129549082728963)
              ·
                refine ⟨1398872836694323624093445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 932581891129549082728963 1398872836694323624093445)
                ·
                  refine ⟨262288656880185679517521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1398872836694323624093445 262288656880185679517521)
                  ·
                    rfl

theorem cell20_574656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_574656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574656 prefixEnd_574656 := by exact prefixLift 574656
  have htrace : WordTrace (prefixWord ++ tailWord_574656) baseStart_574656 baseEnd_574656 := by
    simpa [prefixWord, tailWord_574656, baseEnd_574656] using wordTrace_append hprefix tailTrace_574656
  have hstable : (prefixWord ++ tailWord_574656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574656).length < 2 ^ (prefixWord ++ tailWord_574656).sum := by decide
  have hdescent : baseEnd_574656 < baseStart_574656 := by decide
  rcases family_descends (prefixWord ++ tailWord_574656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574676 : List Nat := [2, 4, 1, 4, 2, 1, 2, 4]
def baseStart_574676 : Nat := 118140960795 + 574676 * 2 ^ 59
def prefixEnd_574676 : Nat := 4983230072969 + 3 ^ 40 * 574676 * 2
def baseEnd_574676 : Nat := 87432595141718166283591

theorem tailTrace_574676 : CollatzResearch.WordTrace tailWord_574676 prefixEnd_574676 87432595141718166283591 := by
  unfold tailWord_574676
  simp only [CollatzResearch.WordTrace]
  refine ⟨10480077833027236846019941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13973437110702982461359921 10480077833027236846019941)
  ·
    refine ⟨1965014593692606908628739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10480077833027236846019941 1965014593692606908628739)
    ·
      refine ⟨2947521890538910362943109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965014593692606908628739 2947521890538910362943109)
      ·
        refine ⟨552660354476045693051833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2947521890538910362943109 552660354476045693051833)
        ·
          refine ⟨414495265857034269788875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 552660354476045693051833 414495265857034269788875)
          ·
            refine ⟨621742898785551404683313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414495265857034269788875 621742898785551404683313)
            ·
              refine ⟨466307174089163553512485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621742898785551404683313 466307174089163553512485)
              ·
                refine ⟨87432595141718166283591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466307174089163553512485 87432595141718166283591)
                ·
                  rfl

theorem cell20_574676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_574676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574676 prefixEnd_574676 := by exact prefixLift 574676
  have htrace : WordTrace (prefixWord ++ tailWord_574676) baseStart_574676 baseEnd_574676 := by
    simpa [prefixWord, tailWord_574676, baseEnd_574676] using wordTrace_append hprefix tailTrace_574676
  have hstable : (prefixWord ++ tailWord_574676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574676).length < 2 ^ (prefixWord ++ tailWord_574676).sum := by decide
  have hdescent : baseEnd_574676 < baseStart_574676 := by decide
  rcases family_descends (prefixWord ++ tailWord_574676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574680 : List Nat := [2, 1, 2, 2, 5, 2, 2, 4]
def baseStart_574680 : Nat := 118140960795 + 574680 * 2 ^ 59
def prefixEnd_574680 : Nat := 4983230072969 + 3 ^ 40 * 574680 * 2
def baseEnd_574680 : Nat := 87433203711382754239141

theorem tailTrace_574680 : CollatzResearch.WordTrace tailWord_574680 prefixEnd_574680 87433203711382754239141 := by
  unfold tailWord_574680
  simp only [CollatzResearch.WordTrace]
  refine ⟨10480150779019991187592747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13973534372026654916790329 10480150779019991187592747)
  ·
    refine ⟨15720226168529986781389121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10480150779019991187592747 15720226168529986781389121)
    ·
      refine ⟨11790169626397490086041841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15720226168529986781389121 11790169626397490086041841)
      ·
        refine ⟨8842627219798117564531381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11790169626397490086041841 8842627219798117564531381)
        ·
          refine ⟨828996301856073521674817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8842627219798117564531381 828996301856073521674817)
          ·
            refine ⟨621747226392055141256113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 828996301856073521674817 621747226392055141256113)
            ·
              refine ⟨466310419794041355942085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621747226392055141256113 466310419794041355942085)
              ·
                refine ⟨87433203711382754239141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466310419794041355942085 87433203711382754239141)
                ·
                  rfl

theorem cell20_574680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_574680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574680 prefixEnd_574680 := by exact prefixLift 574680
  have htrace : WordTrace (prefixWord ++ tailWord_574680) baseStart_574680 baseEnd_574680 := by
    simpa [prefixWord, tailWord_574680, baseEnd_574680] using wordTrace_append hprefix tailTrace_574680
  have hstable : (prefixWord ++ tailWord_574680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574680).length < 2 ^ (prefixWord ++ tailWord_574680).sum := by decide
  have hdescent : baseEnd_574680 < baseStart_574680 := by decide
  rcases family_descends (prefixWord ++ tailWord_574680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574701 : List Nat := [1, 5, 1, 2, 2, 3, 6]
def baseStart_574701 : Nat := 118140960795 + 574701 * 2 ^ 59
def prefixEnd_574701 : Nat := 4983230072969 + 3 ^ 40 * 574701 * 2
def baseEnd_574701 : Nat := 29145466234040613668593

theorem tailTrace_574701 : CollatzResearch.WordTrace tailWord_574701 prefixEnd_574701 29145466234040613668593 := by
  unfold tailWord_574701
  simp only [CollatzResearch.WordTrace]
  refine ⟨20961067490963902961699957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13974044993975935307799971 20961067490963902961699957)
  ·
    refine ⟨1965100077277865902659371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20961067490963902961699957 1965100077277865902659371)
    ·
      refine ⟨2947650115916798853989057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965100077277865902659371 2947650115916798853989057)
      ·
        refine ⟨2210737586937599140491793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2947650115916798853989057 2210737586937599140491793)
        ·
          refine ⟨1658053190203199355368845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210737586937599140491793 1658053190203199355368845)
          ·
            refine ⟨621769946326199758263317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1658053190203199355368845 621769946326199758263317)
            ·
              refine ⟨29145466234040613668593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 621769946326199758263317 29145466234040613668593)
              ·
                rfl

theorem cell20_574701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 6].length) (baseStart_574701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574701 prefixEnd_574701 := by exact prefixLift 574701
  have htrace : WordTrace (prefixWord ++ tailWord_574701) baseStart_574701 baseEnd_574701 := by
    simpa [prefixWord, tailWord_574701, baseEnd_574701] using wordTrace_append hprefix tailTrace_574701
  have hstable : (prefixWord ++ tailWord_574701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574701).length < 2 ^ (prefixWord ++ tailWord_574701).sum := by decide
  have hdescent : baseEnd_574701 < baseStart_574701 := by decide
  rcases family_descends (prefixWord ++ tailWord_574701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574760 : List Nat := [2, 1, 5, 1, 2, 9]
def baseStart_574760 : Nat := 118140960795 + 574760 * 2 ^ 59
def prefixEnd_574760 : Nat := 4983230072969 + 3 ^ 40 * 574760 * 2
def baseEnd_574760 : Nat := 9716152789408279261127

theorem tailTrace_574760 : CollatzResearch.WordTrace tailWord_574760 prefixEnd_574760 9716152789408279261127 := by
  unfold tailWord_574760
  simp only [CollatzResearch.WordTrace]
  refine ⟨10481609698875078019048867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13975479598500104025398489 10481609698875078019048867)
  ·
    refine ⟨15722414548312617028573301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10481609698875078019048867 15722414548312617028573301)
    ·
      refine ⟨1473976363904307846428747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15722414548312617028573301 1473976363904307846428747)
      ·
        refine ⟨2210964545856461769643121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473976363904307846428747 2210964545856461769643121)
        ·
          refine ⟨1658223409392346327232341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2210964545856461769643121 1658223409392346327232341)
          ·
            refine ⟨9716152789408279261127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1658223409392346327232341 9716152789408279261127)
            ·
              rfl

theorem cell20_574760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 9].length) (baseStart_574760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574760 prefixEnd_574760 := by exact prefixLift 574760
  have htrace : WordTrace (prefixWord ++ tailWord_574760) baseStart_574760 baseEnd_574760 := by
    simpa [prefixWord, tailWord_574760, baseEnd_574760] using wordTrace_append hprefix tailTrace_574760
  have hstable : (prefixWord ++ tailWord_574760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574760).length < 2 ^ (prefixWord ++ tailWord_574760).sum := by decide
  have hdescent : baseEnd_574760 < baseStart_574760 := by decide
  rcases family_descends (prefixWord ++ tailWord_574760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574790 : List Nat := [6, 1, 1, 3, 1, 1, 3, 4]
def baseStart_574790 : Nat := 118140960795 + 574790 * 2 ^ 59
def prefixEnd_574790 : Nat := 4983230072969 + 3 ^ 40 * 574790 * 2
def baseEnd_574790 : Nat := 87449939377158923016769

theorem tailTrace_574790 : CollatzResearch.WordTrace tailWord_574790 prefixEnd_574790 87449939377158923016769 := by
  unfold tailWord_574790
  simp only [CollatzResearch.WordTrace]
  refine ⟨655134799613795973802807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13976209058427647441126549 655134799613795973802807)
  ·
    refine ⟨982702199420693960704211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655134799613795973802807 982702199420693960704211)
    ·
      refine ⟨1474053299131040941056317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 982702199420693960704211 1474053299131040941056317)
      ·
        refine ⟨552769987174140352896119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1474053299131040941056317 552769987174140352896119)
        ·
          refine ⟨829154980761210529344179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 552769987174140352896119 829154980761210529344179)
          ·
            refine ⟨1243732471141815794016269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829154980761210529344179 1243732471141815794016269)
            ·
              refine ⟨466399676678180922756101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1243732471141815794016269 466399676678180922756101)
              ·
                refine ⟨87449939377158923016769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466399676678180922756101 87449939377158923016769)
                ·
                  rfl

theorem cell20_574790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_574790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574790 prefixEnd_574790 := by exact prefixLift 574790
  have htrace : WordTrace (prefixWord ++ tailWord_574790) baseStart_574790 baseEnd_574790 := by
    simpa [prefixWord, tailWord_574790, baseEnd_574790] using wordTrace_append hprefix tailTrace_574790
  have hstable : (prefixWord ++ tailWord_574790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574790).length < 2 ^ (prefixWord ++ tailWord_574790).sum := by decide
  have hdescent : baseEnd_574790 < baseStart_574790 := by decide
  rcases family_descends (prefixWord ++ tailWord_574790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574791 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_574791 : Nat := 118140960795 + 574791 * 2 ^ 59
def prefixEnd_574791 : Nat := 4983230072969 + 3 ^ 40 * 574791 * 2
def baseEnd_574791 : Nat := 262350274558725210016969

theorem tailTrace_574791 : CollatzResearch.WordTrace tailWord_574791 prefixEnd_574791 262350274558725210016969 := by
  unfold tailWord_574791
  simp only [CollatzResearch.WordTrace]
  refine ⟨20964350060637848332476227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13976233373758565554984151 20964350060637848332476227)
  ·
    refine ⟨31446525090956772498714341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20964350060637848332476227 31446525090956772498714341)
    ·
      refine ⟨5896223454554394843508939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31446525090956772498714341 5896223454554394843508939)
      ·
        refine ⟨8844335181831592265263409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5896223454554394843508939 8844335181831592265263409)
        ·
          refine ⟨6633251386373694198947557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8844335181831592265263409 6633251386373694198947557)
          ·
            refine ⟨1243734634945067662302667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6633251386373694198947557 1243734634945067662302667)
            ·
              refine ⟨1865601952417601493454001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1243734634945067662302667 1865601952417601493454001)
              ·
                refine ⟨1399201464313201120090501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865601952417601493454001 1399201464313201120090501)
                ·
                  refine ⟨262350274558725210016969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399201464313201120090501 262350274558725210016969)
                  ·
                    rfl

theorem cell20_574791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_574791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574791 prefixEnd_574791 := by exact prefixLift 574791
  have htrace : WordTrace (prefixWord ++ tailWord_574791) baseStart_574791 baseEnd_574791 := by
    simpa [prefixWord, tailWord_574791, baseEnd_574791] using wordTrace_append hprefix tailTrace_574791
  have hstable : (prefixWord ++ tailWord_574791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574791).length < 2 ^ (prefixWord ++ tailWord_574791).sum := by decide
  have hdescent : baseEnd_574791 < baseStart_574791 := by decide
  rcases family_descends (prefixWord ++ tailWord_574791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574808 : List Nat := [2, 1, 2, 2, 1, 1, 6, 3, 2]
def baseStart_574808 : Nat := 118140960795 + 574808 * 2 ^ 59
def prefixEnd_574808 : Nat := 4983230072969 + 3 ^ 40 * 574808 * 2
def baseEnd_574808 : Nat := 262358033821948706450233

theorem tailTrace_574808 : CollatzResearch.WordTrace tailWord_574808 prefixEnd_574808 262358033821948706450233 := by
  unfold tailWord_574808
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482485050788130117922539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13976646734384173490563385 10482485050788130117922539)
  ·
    refine ⟨15723727576182195176883809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10482485050788130117922539 15723727576182195176883809)
    ·
      refine ⟨11792795682136646382662857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15723727576182195176883809 11792795682136646382662857)
      ·
        refine ⟨8844596761602484786997143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11792795682136646382662857 8844596761602484786997143)
        ·
          refine ⟨13266895142403727180495715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8844596761602484786997143 13266895142403727180495715)
          ·
            refine ⟨19900342713605590770743573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13266895142403727180495715 19900342713605590770743573)
            ·
              refine ⟨932828564700262067378605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19900342713605590770743573 932828564700262067378605)
              ·
                refine ⟨349810711762598275266977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 932828564700262067378605 349810711762598275266977)
                ·
                  refine ⟨262358033821948706450233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349810711762598275266977 262358033821948706450233)
                  ·
                    rfl

theorem cell20_574808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 3, 2].length) (baseStart_574808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574808 prefixEnd_574808 := by exact prefixLift 574808
  have htrace : WordTrace (prefixWord ++ tailWord_574808) baseStart_574808 baseEnd_574808 := by
    simpa [prefixWord, tailWord_574808, baseEnd_574808] using wordTrace_append hprefix tailTrace_574808
  have hstable : (prefixWord ++ tailWord_574808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574808).length < 2 ^ (prefixWord ++ tailWord_574808).sum := by decide
  have hdescent : baseEnd_574808 < baseStart_574808 := by decide
  rcases family_descends (prefixWord ++ tailWord_574808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574829 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_574829 : Nat := 118140960795 + 574829 * 2 ^ 59
def prefixEnd_574829 : Nat := 4983230072969 + 3 ^ 40 * 574829 * 2
def baseEnd_574829 : Nat := 262367618794165966750147

theorem tailTrace_574829 : CollatzResearch.WordTrace tailWord_574829 prefixEnd_574829 262367618794165966750147 := by
  unfold tailWord_574829
  simp only [CollatzResearch.WordTrace]
  refine ⟨20965736034500180822359541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13977157356333453881573027 20965736034500180822359541)
  ·
    refine ⟨1965537753234391952096207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20965736034500180822359541 1965537753234391952096207)
    ·
      refine ⟨2948306629851587928144311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1965537753234391952096207 2948306629851587928144311)
      ·
        refine ⟨4422459944777381892216467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2948306629851587928144311 4422459944777381892216467)
        ·
          refine ⟨6633689917166072838324701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422459944777381892216467 6633689917166072838324701)
          ·
            refine ⟨2487633718937277314371763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6633689917166072838324701 2487633718937277314371763)
            ·
              refine ⟨3731450578405915971557645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487633718937277314371763 3731450578405915971557645)
              ·
                refine ⟨1399293966902218489334117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3731450578405915971557645 1399293966902218489334117)
                ·
                  refine ⟨262367618794165966750147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399293966902218489334117 262367618794165966750147)
                  ·
                    rfl

theorem cell20_574829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_574829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574829 prefixEnd_574829 := by exact prefixLift 574829
  have htrace : WordTrace (prefixWord ++ tailWord_574829) baseStart_574829 baseEnd_574829 := by
    simpa [prefixWord, tailWord_574829, baseEnd_574829] using wordTrace_append hprefix tailTrace_574829
  have hstable : (prefixWord ++ tailWord_574829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574829).length < 2 ^ (prefixWord ++ tailWord_574829).sum := by decide
  have hdescent : baseEnd_574829 < baseStart_574829 := by decide
  rcases family_descends (prefixWord ++ tailWord_574829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574849 : List Nat := [1, 2, 4, 3, 3, 1, 2, 4]
def baseStart_574849 : Nat := 118140960795 + 574849 * 2 ^ 59
def prefixEnd_574849 : Nat := 4983230072969 + 3 ^ 40 * 574849 * 2
def baseEnd_574849 : Nat := 87458915779711595361133

theorem tailTrace_574849 : CollatzResearch.WordTrace tailWord_574849 prefixEnd_574849 87458915779711595361133 := by
  unfold tailWord_574849
  simp only [CollatzResearch.WordTrace]
  refine ⟨20966465494427724238087601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13977643662951816158725067 20966465494427724238087601)
  ·
    refine ⟨15724849120820793178565701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20966465494427724238087601 15724849120820793178565701)
    ·
      refine ⟨2948409210153898720981069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15724849120820793178565701 2948409210153898720981069)
      ·
        refine ⟨1105653453807712020367901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2948409210153898720981069 1105653453807712020367901)
        ·
          refine ⟨414620045177892007637963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1105653453807712020367901 414620045177892007637963)
          ·
            refine ⟨621930067766838011456945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 414620045177892007637963 621930067766838011456945)
            ·
              refine ⟨466447550825128508592709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 621930067766838011456945 466447550825128508592709)
              ·
                refine ⟨87458915779711595361133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466447550825128508592709 87458915779711595361133)
                ·
                  rfl

theorem cell20_574849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 4].length) (baseStart_574849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574849 prefixEnd_574849 := by exact prefixLift 574849
  have htrace : WordTrace (prefixWord ++ tailWord_574849) baseStart_574849 baseEnd_574849 := by
    simpa [prefixWord, tailWord_574849, baseEnd_574849] using wordTrace_append hprefix tailTrace_574849
  have hstable : (prefixWord ++ tailWord_574849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574849).length < 2 ^ (prefixWord ++ tailWord_574849).sum := by decide
  have hdescent : baseEnd_574849 < baseStart_574849 := by decide
  rcases family_descends (prefixWord ++ tailWord_574849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574977 : List Nat := [1, 2, 4, 1, 4, 1, 2, 3, 2]
def baseStart_574977 : Nat := 118140960795 + 574977 * 2 ^ 59
def prefixEnd_574977 : Nat := 4983230072969 + 3 ^ 40 * 574977 * 2
def baseEnd_574977 : Nat := 262435170026935229816209

theorem tailTrace_574977 : CollatzResearch.WordTrace tailWord_574977 prefixEnd_574977 262435170026935229816209 := by
  unfold tailWord_574977
  simp only [CollatzResearch.WordTrace]
  refine ⟨20971134037964002098747185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13980756025309334732498123 20971134037964002098747185)
  ·
    refine ⟨15728350528473001574060389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20971134037964002098747185 15728350528473001574060389)
    ·
      refine ⟨2949065724088687795136323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15728350528473001574060389 2949065724088687795136323)
      ·
        refine ⟨4423598586133031692704485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2949065724088687795136323 4423598586133031692704485)
        ·
          refine ⟨829424734899943442382091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4423598586133031692704485 829424734899943442382091)
          ·
            refine ⟨1244137102349915163573137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829424734899943442382091 1244137102349915163573137)
            ·
              refine ⟨933102826762436372679853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1244137102349915163573137 933102826762436372679853)
              ·
                refine ⟨349913560035913639754945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933102826762436372679853 349913560035913639754945)
                ·
                  refine ⟨262435170026935229816209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349913560035913639754945 262435170026935229816209)
                  ·
                    rfl

theorem cell20_574977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_574977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574977 prefixEnd_574977 := by exact prefixLift 574977
  have htrace : WordTrace (prefixWord ++ tailWord_574977) baseStart_574977 baseEnd_574977 := by
    simpa [prefixWord, tailWord_574977, baseEnd_574977] using wordTrace_append hprefix tailTrace_574977
  have hstable : (prefixWord ++ tailWord_574977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574977).length < 2 ^ (prefixWord ++ tailWord_574977).sum := by decide
  have hdescent : baseEnd_574977 < baseStart_574977 := by decide
  rcases family_descends (prefixWord ++ tailWord_574977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574988 : List Nat := [2, 2, 1, 2, 5, 1, 7]
def baseStart_574988 : Nat := 118140960795 + 574988 * 2 ^ 59
def prefixEnd_574988 : Nat := 4983230072969 + 3 ^ 40 * 574988 * 2
def baseEnd_574988 : Nat := 29160021191852008938833

theorem tailTrace_574988 : CollatzResearch.WordTrace tailWord_574988 prefixEnd_574988 29160021191852008938833 := by
  unfold tailWord_574988
  simp only [CollatzResearch.WordTrace]
  refine ⟨10485767620462075488698809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13981023493949433984931745 10485767620462075488698809)
  ·
    refine ⟨7864325715346556616524107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10485767620462075488698809 7864325715346556616524107)
    ·
      refine ⟨11796488573019834924786161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7864325715346556616524107 11796488573019834924786161)
      ·
        refine ⟨8847366429764876193589621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11796488573019834924786161 8847366429764876193589621)
        ·
          refine ⟨829440602790457143149027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8847366429764876193589621 829440602790457143149027)
          ·
            refine ⟨1244160904185685714723541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829440602790457143149027 1244160904185685714723541)
            ·
              refine ⟨29160021191852008938833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1244160904185685714723541 29160021191852008938833)
              ·
                rfl

theorem cell20_574988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 7].length) (baseStart_574988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574988 prefixEnd_574988 := by exact prefixLift 574988
  have htrace : WordTrace (prefixWord ++ tailWord_574988) baseStart_574988 baseEnd_574988 := by
    simpa [prefixWord, tailWord_574988, baseEnd_574988] using wordTrace_append hprefix tailTrace_574988
  have hstable : (prefixWord ++ tailWord_574988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574988).length < 2 ^ (prefixWord ++ tailWord_574988).sum := by decide
  have hdescent : baseEnd_574988 < baseStart_574988 := by decide
  rcases family_descends (prefixWord ++ tailWord_574988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_574995 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 5]
def baseStart_574995 : Nat := 118140960795 + 574995 * 2 ^ 59
def prefixEnd_574995 : Nat := 4983230072969 + 3 ^ 40 * 574995 * 2
def baseEnd_574995 : Nat := 262443385717407167216135

theorem tailTrace_574995 : CollatzResearch.WordTrace tailWord_574995 prefixEnd_574995 262443385717407167216135 := by
  unfold tailWord_574995
  simp only [CollatzResearch.WordTrace]
  refine ⟨20971790551898791172902439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13981193701265860781934959 20971790551898791172902439)
  ·
    refine ⟨31457685827848186759353659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20971790551898791172902439 31457685827848186759353659)
    ·
      refine ⟨47186528741772280139030489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31457685827848186759353659 47186528741772280139030489)
      ·
        refine ⟨35389896556329210104272867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47186528741772280139030489 35389896556329210104272867)
        ·
          refine ⟨53084844834493815156409301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35389896556329210104272867 53084844834493815156409301)
          ·
            refine ⟨1244176050808448792728343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 53084844834493815156409301 1244176050808448792728343)
            ·
              refine ⟨1866264076212673189092515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244176050808448792728343 1866264076212673189092515)
              ·
                refine ⟨2799396114319009783638773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1866264076212673189092515 2799396114319009783638773)
                ·
                  refine ⟨262443385717407167216135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2799396114319009783638773 262443385717407167216135)
                  ·
                    rfl

theorem cell20_574995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 5].length) (baseStart_574995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_574995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_574995 prefixEnd_574995 := by exact prefixLift 574995
  have htrace : WordTrace (prefixWord ++ tailWord_574995) baseStart_574995 baseEnd_574995 := by
    simpa [prefixWord, tailWord_574995, baseEnd_574995] using wordTrace_append hprefix tailTrace_574995
  have hstable : (prefixWord ++ tailWord_574995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_574995).length < 2 ^ (prefixWord ++ tailWord_574995).sum := by decide
  have hdescent : baseEnd_574995 < baseStart_574995 := by decide
  rcases family_descends (prefixWord ++ tailWord_574995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575022 : List Nat := [4, 1, 3, 1, 2, 3, 2, 4]
def baseStart_575022 : Nat := 118140960795 + 575022 * 2 ^ 59
def prefixEnd_575022 : Nat := 4983230072969 + 3 ^ 40 * 575022 * 2
def baseEnd_575022 : Nat := 87485236417705024438675

theorem tailTrace_575022 : CollatzResearch.WordTrace tailWord_575022 prefixEnd_575022 87485236417705024438675 := by
  unfold tailWord_575022
  simp only [CollatzResearch.WordTrace]
  refine ⟨2621596915350121848016915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13981850215200649856090213 2621596915350121848016915)
  ·
    refine ⟨3932395373025182772025373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2621596915350121848016915 3932395373025182772025373)
    ·
      refine ⟨1474648264884443539509515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3932395373025182772025373 1474648264884443539509515)
      ·
        refine ⟨2211972397326665309264273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474648264884443539509515 2211972397326665309264273)
        ·
          refine ⟨1658979297994998981948205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2211972397326665309264273 1658979297994998981948205)
          ·
            refine ⟨622117236748124618230577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1658979297994998981948205 622117236748124618230577)
            ·
              refine ⟨466587927561093463672933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622117236748124618230577 466587927561093463672933)
              ·
                refine ⟨87485236417705024438675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 466587927561093463672933 87485236417705024438675)
                ·
                  rfl

theorem cell20_575022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_575022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575022 prefixEnd_575022 := by exact prefixLift 575022
  have htrace : WordTrace (prefixWord ++ tailWord_575022) baseStart_575022 baseEnd_575022 := by
    simpa [prefixWord, tailWord_575022, baseEnd_575022] using wordTrace_append hprefix tailTrace_575022
  have hstable : (prefixWord ++ tailWord_575022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575022).length < 2 ^ (prefixWord ++ tailWord_575022).sum := by decide
  have hdescent : baseEnd_575022 < baseStart_575022 := by decide
  rcases family_descends (prefixWord ++ tailWord_575022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575033 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_575033 : Nat := 118140960795 + 575033 * 2 ^ 59
def prefixEnd_575033 : Nat := 4983230072969 + 3 ^ 40 * 575033 * 2
def baseEnd_575033 : Nat := 262460729952847923949313

theorem tailTrace_575033 : CollatzResearch.WordTrace tailWord_575033 prefixEnd_575033 262460729952847923949313 := by
  unfold tailWord_575033
  simp only [CollatzResearch.WordTrace]
  refine ⟨20973176525761123662785753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13982117683840749108523835 20973176525761123662785753)
  ·
    refine ⟨15729882394320842747089315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20973176525761123662785753 15729882394320842747089315)
    ·
      refine ⟨23594823591481264120633973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15729882394320842747089315 23594823591481264120633973)
      ·
        refine ⟨2212014711701368511309435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23594823591481264120633973 2212014711701368511309435)
        ·
          refine ⟨3318022067552052766964153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212014711701368511309435 3318022067552052766964153)
          ·
            refine ⟨2488516550664039575223115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3318022067552052766964153 2488516550664039575223115)
            ·
              refine ⟨3732774825996059362834673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2488516550664039575223115 3732774825996059362834673)
              ·
                refine ⟨2799581119497044522126005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3732774825996059362834673 2799581119497044522126005)
                ·
                  refine ⟨262460729952847923949313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2799581119497044522126005 262460729952847923949313)
                  ·
                    rfl

theorem cell20_575033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_575033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575033 prefixEnd_575033 := by exact prefixLift 575033
  have htrace : WordTrace (prefixWord ++ tailWord_575033) baseStart_575033 baseEnd_575033 := by
    simpa [prefixWord, tailWord_575033, baseEnd_575033] using wordTrace_append hprefix tailTrace_575033
  have hstable : (prefixWord ++ tailWord_575033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575033).length < 2 ^ (prefixWord ++ tailWord_575033).sum := by decide
  have hdescent : baseEnd_575033 < baseStart_575033 := by decide
  rcases family_descends (prefixWord ++ tailWord_575033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575053 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 4]
def baseStart_575053 : Nat := 118140960795 + 575053 * 2 ^ 59
def prefixEnd_575053 : Nat := 4983230072969 + 3 ^ 40 * 575053 * 2
def baseEnd_575053 : Nat := 262469858497816743282565

theorem tailTrace_575053 : CollatzResearch.WordTrace tailWord_575053 prefixEnd_575053 262469858497816743282565 := by
  unfold tailWord_575053
  simp only [CollatzResearch.WordTrace]
  refine ⟨20973905985688667078513813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13982603990459111385675875 20973905985688667078513813)
  ·
    refine ⟨983151843079156269305335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20973905985688667078513813 983151843079156269305335)
    ·
      refine ⟨1474727764618734403958003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983151843079156269305335 1474727764618734403958003)
      ·
        refine ⟨2212091646928101605937005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1474727764618734403958003 2212091646928101605937005)
        ·
          refine ⟨829534367598038102226377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2212091646928101605937005 829534367598038102226377)
          ·
            refine ⟨622150775698528576669783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829534367598038102226377 622150775698528576669783)
            ·
              refine ⟨933226163547792865004675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622150775698528576669783 933226163547792865004675)
              ·
                refine ⟨1399839245321689297507013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933226163547792865004675 1399839245321689297507013)
                ·
                  refine ⟨262469858497816743282565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399839245321689297507013 262469858497816743282565)
                  ·
                    rfl

theorem cell20_575053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_575053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575053 prefixEnd_575053 := by exact prefixLift 575053
  have htrace : WordTrace (prefixWord ++ tailWord_575053) baseStart_575053 baseEnd_575053 := by
    simpa [prefixWord, tailWord_575053, baseEnd_575053] using wordTrace_append hprefix tailTrace_575053
  have hstable : (prefixWord ++ tailWord_575053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575053).length < 2 ^ (prefixWord ++ tailWord_575053).sum := by decide
  have hdescent : baseEnd_575053 < baseStart_575053 := by decide
  rcases family_descends (prefixWord ++ tailWord_575053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575095 : List Nat := [1, 1, 3, 1, 1, 3, 1, 7, 2]
def baseStart_575095 : Nat := 118140960795 + 575095 * 2 ^ 59
def prefixEnd_575095 : Nat := 4983230072969 + 3 ^ 40 * 575095 * 2
def baseEnd_575095 : Nat := 262489028442251263882393

theorem tailTrace_575095 : CollatzResearch.WordTrace tailWord_575095 prefixEnd_575095 262489028442251263882393 := by
  unfold tailWord_575095
  simp only [CollatzResearch.WordTrace]
  refine ⟨20975437851536508251542739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13983625234357672167695159 20975437851536508251542739)
  ·
    refine ⟨31463156777304762377314109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20975437851536508251542739 31463156777304762377314109)
    ·
      refine ⟨11798683791489285891492791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31463156777304762377314109 11798683791489285891492791)
      ·
        refine ⟨17698025687233928837239187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11798683791489285891492791 17698025687233928837239187)
        ·
          refine ⟨26547038530850893255858781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17698025687233928837239187 26547038530850893255858781)
          ·
            refine ⟨9955139449069084970947043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26547038530850893255858781 9955139449069084970947043)
            ·
              refine ⟨14932709173603627456420565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9955139449069084970947043 14932709173603627456420565)
              ·
                refine ⟨349985371256335018509857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14932709173603627456420565 349985371256335018509857)
                ·
                  refine ⟨262489028442251263882393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349985371256335018509857 262489028442251263882393)
                  ·
                    rfl

theorem cell20_575095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 2].length) (baseStart_575095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575095 prefixEnd_575095 := by exact prefixLift 575095
  have htrace : WordTrace (prefixWord ++ tailWord_575095) baseStart_575095 baseEnd_575095 := by
    simpa [prefixWord, tailWord_575095, baseEnd_575095] using wordTrace_append hprefix tailTrace_575095
  have hstable : (prefixWord ++ tailWord_575095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575095).length < 2 ^ (prefixWord ++ tailWord_575095).sum := by decide
  have hdescent : baseEnd_575095 < baseStart_575095 := by decide
  rcases family_descends (prefixWord ++ tailWord_575095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575108 : List Nat := [2, 3, 2, 1, 4, 2, 2, 2, 2]
def baseStart_575108 : Nat := 118140960795 + 575108 * 2 ^ 59
def prefixEnd_575108 : Nat := 4983230072969 + 3 ^ 40 * 575108 * 2
def baseEnd_575108 : Nat := 262494961996480996449007

theorem tailTrace_575108 : CollatzResearch.WordTrace tailWord_575108 prefixEnd_575108 262494961996480996449007 := by
  unfold tailWord_575108
  simp only [CollatzResearch.WordTrace]
  refine ⟨10487956000244705735882989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13983941333659607647843985 10487956000244705735882989)
  ·
    refine ⟨3932983500091764650956121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10487956000244705735882989 3932983500091764650956121)
    ·
      refine ⟨2949737625068823488217091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3932983500091764650956121 2949737625068823488217091)
      ·
        refine ⟨4424606437603235232325637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2949737625068823488217091 4424606437603235232325637)
        ·
          refine ⟨829613707050606606061057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4424606437603235232325637 829613707050606606061057)
          ·
            refine ⟨622210280287954954545793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829613707050606606061057 622210280287954954545793)
            ·
              refine ⟨466657710215966215909345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622210280287954954545793 466657710215966215909345)
              ·
                refine ⟨349993282661974661932009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466657710215966215909345 349993282661974661932009)
                ·
                  refine ⟨262494961996480996449007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 349993282661974661932009 262494961996480996449007)
                  ·
                    rfl

theorem cell20_575108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_575108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575108 prefixEnd_575108 := by exact prefixLift 575108
  have htrace : WordTrace (prefixWord ++ tailWord_575108) baseStart_575108 baseEnd_575108 := by
    simpa [prefixWord, tailWord_575108, baseEnd_575108] using wordTrace_append hprefix tailTrace_575108
  have hstable : (prefixWord ++ tailWord_575108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575108).length < 2 ^ (prefixWord ++ tailWord_575108).sum := by decide
  have hdescent : baseEnd_575108 < baseStart_575108 := by decide
  rcases family_descends (prefixWord ++ tailWord_575108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575116 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_575116 : Nat := 118140960795 + 575116 * 2 ^ 59
def prefixEnd_575116 : Nat := 4983230072969 + 3 ^ 40 * 575116 * 2
def baseEnd_575116 : Nat := 262498613414468524182307

theorem tailTrace_575116 : CollatzResearch.WordTrace tailWord_575116 prefixEnd_575116 262498613414468524182307 := by
  unfold tailWord_575116
  simp only [CollatzResearch.WordTrace]
  refine ⟨10488101892230214419028601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13984135856306952558704801 10488101892230214419028601)
  ·
    refine ⟨7866076419172660814271451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10488101892230214419028601 7866076419172660814271451)
    ·
      refine ⟨11799114628758991221407177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7866076419172660814271451 11799114628758991221407177)
      ·
        refine ⟨8849335971569243416055383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11799114628758991221407177 8849335971569243416055383)
        ·
          refine ⟨13274003957353865124083075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8849335971569243416055383 13274003957353865124083075)
          ·
            refine ⟨19911005936030797686124613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13274003957353865124083075 19911005936030797686124613)
            ·
              refine ⟨3733313613005774566148365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19911005936030797686124613 3733313613005774566148365)
              ·
                refine ⟨1399992604877165462305637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3733313613005774566148365 1399992604877165462305637)
                ·
                  refine ⟨262498613414468524182307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1399992604877165462305637 262498613414468524182307)
                  ·
                    rfl

theorem cell20_575116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_575116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575116 prefixEnd_575116 := by exact prefixLift 575116
  have htrace : WordTrace (prefixWord ++ tailWord_575116) baseStart_575116 baseEnd_575116 := by
    simpa [prefixWord, tailWord_575116, baseEnd_575116] using wordTrace_append hprefix tailTrace_575116
  have hstable : (prefixWord ++ tailWord_575116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575116).length < 2 ^ (prefixWord ++ tailWord_575116).sum := by decide
  have hdescent : baseEnd_575116 < baseStart_575116 := by decide
  rcases family_descends (prefixWord ++ tailWord_575116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575164 : List Nat := [2, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_575164 : Nat := 118140960795 + 575164 * 2 ^ 59
def prefixEnd_575164 : Nat := 4983230072969 + 3 ^ 40 * 575164 * 2
def baseEnd_575164 : Nat := 262520521922393690582111

theorem tailTrace_575164 : CollatzResearch.WordTrace tailWord_575164 prefixEnd_575164 262520521922393690582111 := by
  unfold tailWord_575164
  simp only [CollatzResearch.WordTrace]
  refine ⟨10488977244143266517902273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13985302992191022023869697 10488977244143266517902273)
  ·
    refine ⟨7866732933107449888426705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10488977244143266517902273 7866732933107449888426705)
    ·
      refine ⟨5900049699830587416320029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7866732933107449888426705 5900049699830587416320029)
      ·
        refine ⟨2212518637436470281120011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5900049699830587416320029 2212518637436470281120011)
        ·
          refine ⟨3318777956154705421680017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2212518637436470281120011 3318777956154705421680017)
          ·
            refine ⟨2489083467116029066260013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3318777956154705421680017 2489083467116029066260013)
            ·
              refine ⟨933406300168510899847505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2489083467116029066260013 933406300168510899847505)
              ·
                refine ⟨700054725126383174885629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 933406300168510899847505 700054725126383174885629)
                ·
                  refine ⟨262520521922393690582111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700054725126383174885629 262520521922393690582111)
                  ·
                    rfl

theorem cell20_575164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_575164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575164 prefixEnd_575164 := by exact prefixLift 575164
  have htrace : WordTrace (prefixWord ++ tailWord_575164) baseStart_575164 baseEnd_575164 := by
    simpa [prefixWord, tailWord_575164, baseEnd_575164] using wordTrace_append hprefix tailTrace_575164
  have hstable : (prefixWord ++ tailWord_575164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575164).length < 2 ^ (prefixWord ++ tailWord_575164).sum := by decide
  have hdescent : baseEnd_575164 < baseStart_575164 := by decide
  rcases family_descends (prefixWord ++ tailWord_575164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575192 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_575192 : Nat := 118140960795 + 575192 * 2 ^ 59
def prefixEnd_575192 : Nat := 4983230072969 + 3 ^ 40 * 575192 * 2
def baseEnd_575192 : Nat := 262533301885350037648663

theorem tailTrace_575192 : CollatzResearch.WordTrace tailWord_575192 prefixEnd_575192 262533301885350037648663 := by
  unfold tailWord_575192
  simp only [CollatzResearch.WordTrace]
  refine ⟨10489487866092546908911915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13985983821456729211882553 10489487866092546908911915)
  ·
    refine ⟨15734231799138820363367873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10489487866092546908911915 15734231799138820363367873)
    ·
      refine ⟨11800673849354115272525905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15734231799138820363367873 11800673849354115272525905)
      ·
        refine ⟨8850505387015586454394429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11800673849354115272525905 8850505387015586454394429)
        ·
          refine ⟨3318939520130844920397911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8850505387015586454394429 3318939520130844920397911)
          ·
            refine ⟨4978409280196267380596867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3318939520130844920397911 4978409280196267380596867)
            ·
              refine ⟨7467613920294401070895301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978409280196267380596867 7467613920294401070895301)
              ·
                refine ⟨1400177610055200200792869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7467613920294401070895301 1400177610055200200792869)
                ·
                  refine ⟨262533301885350037648663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400177610055200200792869 262533301885350037648663)
                  ·
                    rfl

theorem cell20_575192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_575192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575192 prefixEnd_575192 := by exact prefixLift 575192
  have htrace : WordTrace (prefixWord ++ tailWord_575192) baseStart_575192 baseEnd_575192 := by
    simpa [prefixWord, tailWord_575192, baseEnd_575192] using wordTrace_append hprefix tailTrace_575192
  have hstable : (prefixWord ++ tailWord_575192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575192).length < 2 ^ (prefixWord ++ tailWord_575192).sum := by decide
  have hdescent : baseEnd_575192 < baseStart_575192 := by decide
  rcases family_descends (prefixWord ++ tailWord_575192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575199 : List Nat := [1, 1, 2, 3, 2, 2, 3, 6]
def baseStart_575199 : Nat := 118140960795 + 575199 * 2 ^ 59
def prefixEnd_575199 : Nat := 4983230072969 + 3 ^ 40 * 575199 * 2
def baseEnd_575199 : Nat := 87512165625363041471767

theorem tailTrace_575199 : CollatzResearch.WordTrace tailWord_575199 prefixEnd_575199 87512165625363041471767 := by
  unfold tailWord_575199
  simp only [CollatzResearch.WordTrace]
  refine ⟨20979231043159734013328651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13986154028773156008885767 20979231043159734013328651)
  ·
    refine ⟨31468846564739601019992977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20979231043159734013328651 31468846564739601019992977)
    ·
      refine ⟨23601634923554700764994733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31468846564739601019992977 23601634923554700764994733)
      ·
        refine ⟨8850613096333012786873025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23601634923554700764994733 8850613096333012786873025)
        ·
          refine ⟨6637959822249759590154769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8850613096333012786873025 6637959822249759590154769)
          ·
            refine ⟨4978469866687319692616077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6637959822249759590154769 4978469866687319692616077)
            ·
              refine ⟨1866926200007744884731029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4978469866687319692616077 1866926200007744884731029)
              ·
                refine ⟨87512165625363041471767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1866926200007744884731029 87512165625363041471767)
                ·
                  rfl

theorem cell20_575199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 6].length) (baseStart_575199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575199 prefixEnd_575199 := by exact prefixLift 575199
  have htrace : WordTrace (prefixWord ++ tailWord_575199) baseStart_575199 baseEnd_575199 := by
    simpa [prefixWord, tailWord_575199, baseEnd_575199] using wordTrace_append hprefix tailTrace_575199
  have hstable : (prefixWord ++ tailWord_575199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575199).length < 2 ^ (prefixWord ++ tailWord_575199).sum := by decide
  have hdescent : baseEnd_575199 < baseStart_575199 := by decide
  rcases family_descends (prefixWord ++ tailWord_575199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575281 : List Nat := [1, 2, 2, 3, 2, 4, 2, 2, 2]
def baseStart_575281 : Nat := 118140960795 + 575281 * 2 ^ 59
def prefixEnd_575281 : Nat := 4983230072969 + 3 ^ 40 * 575281 * 2
def baseEnd_575281 : Nat := 262573923910461283681633

theorem tailTrace_575281 : CollatzResearch.WordTrace tailWord_575281 prefixEnd_575281 262573923910461283681633 := by
  unfold tailWord_575281
  simp only [CollatzResearch.WordTrace]
  refine ⟨20982221828862662017813697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13988147885908441345209131 20982221828862662017813697)
  ·
    refine ⟨15736666371646996513360273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20982221828862662017813697 15736666371646996513360273)
    ·
      refine ⟨11802499778735247385020205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15736666371646996513360273 11802499778735247385020205)
      ·
        refine ⟨4425937417025717769382577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11802499778735247385020205 4425937417025717769382577)
        ·
          refine ⟨3319453062769288327036933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4425937417025717769382577 3319453062769288327036933)
          ·
            refine ⟨622397449269241561319425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3319453062769288327036933 622397449269241561319425)
            ·
              refine ⟨466798086951931170989569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622397449269241561319425 466798086951931170989569)
              ·
                refine ⟨350098565213948378242177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466798086951931170989569 350098565213948378242177)
                ·
                  refine ⟨262573923910461283681633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350098565213948378242177 262573923910461283681633)
                  ·
                    rfl

theorem cell20_575281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_575281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575281 prefixEnd_575281 := by exact prefixLift 575281
  have htrace : WordTrace (prefixWord ++ tailWord_575281) baseStart_575281 baseEnd_575281 := by
    simpa [prefixWord, tailWord_575281, baseEnd_575281] using wordTrace_append hprefix tailTrace_575281
  have hstable : (prefixWord ++ tailWord_575281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575281).length < 2 ^ (prefixWord ++ tailWord_575281).sum := by decide
  have hdescent : baseEnd_575281 < baseStart_575281 := by decide
  rcases family_descends (prefixWord ++ tailWord_575281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575299 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 3]
def baseStart_575299 : Nat := 118140960795 + 575299 * 2 ^ 59
def prefixEnd_575299 : Nat := 4983230072969 + 3 ^ 40 * 575299 * 2
def baseEnd_575299 : Nat := 262582139600933221081559

theorem tailTrace_575299 : CollatzResearch.WordTrace tailWord_575299 prefixEnd_575299 262582139600933221081559 := by
  unfold tailWord_575299
  simp only [CollatzResearch.WordTrace]
  refine ⟨20982878342797451091968951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13988585561864967394645967 20982878342797451091968951)
  ·
    refine ⟨31474317514196176637953427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20982878342797451091968951 31474317514196176637953427)
    ·
      refine ⟨47211476271294264956930141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31474317514196176637953427 47211476271294264956930141)
      ·
        refine ⟨17704303601735349358848803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47211476271294264956930141 17704303601735349358848803)
        ·
          refine ⟨26556455402603024038273205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17704303601735349358848803 26556455402603024038273205)
          ·
            refine ⟨2489667693994033503588113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26556455402603024038273205 2489667693994033503588113)
            ·
              refine ⟨1867250770495525127691085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2489667693994033503588113 1867250770495525127691085)
              ·
                refine ⟨700219038935821922884157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1867250770495525127691085 700219038935821922884157)
                ·
                  refine ⟨262582139600933221081559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700219038935821922884157 262582139600933221081559)
                  ·
                    rfl

theorem cell20_575299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3].length) (baseStart_575299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575299 prefixEnd_575299 := by exact prefixLift 575299
  have htrace : WordTrace (prefixWord ++ tailWord_575299) baseStart_575299 baseEnd_575299 := by
    simpa [prefixWord, tailWord_575299, baseEnd_575299] using wordTrace_append hprefix tailTrace_575299
  have hstable : (prefixWord ++ tailWord_575299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575299).length < 2 ^ (prefixWord ++ tailWord_575299).sum := by decide
  have hdescent : baseEnd_575299 < baseStart_575299 := by decide
  rcases family_descends (prefixWord ++ tailWord_575299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575302 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_575302 : Nat := 118140960795 + 575302 * 2 ^ 59
def prefixEnd_575302 : Nat := 4983230072969 + 3 ^ 40 * 575302 * 2
def baseEnd_575302 : Nat := 262583508882678543981547

theorem tailTrace_575302 : CollatzResearch.WordTrace tailWord_575302 prefixEnd_575302 262583508882678543981547 := by
  unfold tailWord_575302
  simp only [CollatzResearch.WordTrace]
  refine ⟨655718367555830706385255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13988658507857721736218773 655718367555830706385255)
  ·
    refine ⟨983577551333746059577883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655718367555830706385255 983577551333746059577883)
    ·
      refine ⟨1475366327000619089366825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 983577551333746059577883 1475366327000619089366825)
      ·
        refine ⟨1106524745250464317025119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1475366327000619089366825 1106524745250464317025119)
        ·
          refine ⟨1659787117875696475537679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1106524745250464317025119 1659787117875696475537679)
          ·
            refine ⟨2489680676813544713306519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1659787117875696475537679 2489680676813544713306519)
            ·
              refine ⟨3734521015220317069959779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2489680676813544713306519 3734521015220317069959779)
              ·
                refine ⟨5601781522830475604939669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734521015220317069959779 5601781522830475604939669)
                ·
                  refine ⟨262583508882678543981547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5601781522830475604939669 262583508882678543981547)
                  ·
                    rfl

theorem cell20_575302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_575302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575302 prefixEnd_575302 := by exact prefixLift 575302
  have htrace : WordTrace (prefixWord ++ tailWord_575302) baseStart_575302 baseEnd_575302 := by
    simpa [prefixWord, tailWord_575302, baseEnd_575302] using wordTrace_append hprefix tailTrace_575302
  have hstable : (prefixWord ++ tailWord_575302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575302).length < 2 ^ (prefixWord ++ tailWord_575302).sum := by decide
  have hdescent : baseEnd_575302 < baseStart_575302 := by decide
  rcases family_descends (prefixWord ++ tailWord_575302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575306 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_575306 : Nat := 118140960795 + 575306 * 2 ^ 59
def prefixEnd_575306 : Nat := 4983230072969 + 3 ^ 40 * 575306 * 2
def baseEnd_575306 : Nat := 262585334591672307848197

theorem tailTrace_575306 : CollatzResearch.WordTrace tailWord_575306 prefixEnd_575306 262585334591672307848197 := by
  unfold tailWord_575306
  simp only [CollatzResearch.WordTrace]
  refine ⟨5245783413443022821868443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13988755769181394191649181 5245783413443022821868443)
  ·
    refine ⟨7868675120164534232802665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5245783413443022821868443 7868675120164534232802665)
    ·
      refine ⟨5901506340123400674601999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7868675120164534232802665 5901506340123400674601999)
      ·
        refine ⟨8852259510185101011902999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5901506340123400674601999 8852259510185101011902999)
        ·
          refine ⟨13278389265277651517854499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8852259510185101011902999 13278389265277651517854499)
          ·
            refine ⟨19917583897916477276781749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13278389265277651517854499 19917583897916477276781749)
            ·
              refine ⟨1867273490429669744698289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19917583897916477276781749 1867273490429669744698289)
              ·
                refine ⟨1400455117822252308523717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1867273490429669744698289 1400455117822252308523717)
                ·
                  refine ⟨262585334591672307848197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400455117822252308523717 262585334591672307848197)
                  ·
                    rfl

theorem cell20_575306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_575306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575306 prefixEnd_575306 := by exact prefixLift 575306
  have htrace : WordTrace (prefixWord ++ tailWord_575306) baseStart_575306 baseEnd_575306 := by
    simpa [prefixWord, tailWord_575306, baseEnd_575306] using wordTrace_append hprefix tailTrace_575306
  have hstable : (prefixWord ++ tailWord_575306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575306).length < 2 ^ (prefixWord ++ tailWord_575306).sum := by decide
  have hdescent : baseEnd_575306 < baseStart_575306 := by decide
  rcases family_descends (prefixWord ++ tailWord_575306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575330 : List Nat := [3, 3, 2, 1, 2, 2, 7]
def baseStart_575330 : Nat := 118140960795 + 575330 * 2 ^ 59
def prefixEnd_575330 : Nat := 4983230072969 + 3 ^ 40 * 575330 * 2
def baseEnd_575330 : Nat := 29177365427292765672011

theorem tailTrace_575330 : CollatzResearch.WordTrace tailWord_575330 prefixEnd_575330 29177365427292765672011 := by
  unfold tailWord_575330
  simp only [CollatzResearch.WordTrace]
  refine ⟨5246002251421285846586861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13989339337123428924231629 5246002251421285846586861)
  ·
    refine ⟨1967250844282982192470073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5246002251421285846586861 1967250844282982192470073)
    ·
      refine ⟨1475438133212236644352555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1967250844282982192470073 1475438133212236644352555)
      ·
        refine ⟨2213157199818354966528833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475438133212236644352555 2213157199818354966528833)
        ·
          refine ⟨1659867899863766224896625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213157199818354966528833 1659867899863766224896625)
          ·
            refine ⟨1244900924897824668672469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1659867899863766224896625 1244900924897824668672469)
            ·
              refine ⟨29177365427292765672011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1244900924897824668672469 29177365427292765672011)
              ·
                rfl

theorem cell20_575330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 7].length) (baseStart_575330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575330 prefixEnd_575330 := by exact prefixLift 575330
  have htrace : WordTrace (prefixWord ++ tailWord_575330) baseStart_575330 baseEnd_575330 := by
    simpa [prefixWord, tailWord_575330, baseEnd_575330] using wordTrace_append hprefix tailTrace_575330
  have hstable : (prefixWord ++ tailWord_575330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575330).length < 2 ^ (prefixWord ++ tailWord_575330).sum := by decide
  have hdescent : baseEnd_575330 < baseStart_575330 := by decide
  rcases family_descends (prefixWord ++ tailWord_575330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575350 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_575350 : Nat := 118140960795 + 575350 * 2 ^ 59
def prefixEnd_575350 : Nat := 4983230072969 + 3 ^ 40 * 575350 * 2
def baseEnd_575350 : Nat := 262605417390603710381351

theorem tailTrace_575350 : CollatzResearch.WordTrace tailWord_575350 prefixEnd_575350 262605417390603710381351 := by
  unfold tailWord_575350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311546154100792925129719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13989825643741791201383669 1311546154100792925129719)
  ·
    refine ⟨1967319231151189387694579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1311546154100792925129719 1967319231151189387694579)
    ·
      refine ⟨2950978846726784081541869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1967319231151189387694579 2950978846726784081541869)
      ·
        refine ⟨1106617067522544030578201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2950978846726784081541869 1106617067522544030578201)
        ·
          refine ⟨829962800641908022933651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1106617067522544030578201 829962800641908022933651)
          ·
            refine ⟨1244944200962862034400477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829962800641908022933651 1244944200962862034400477)
            ·
              refine ⟨466854075361073262900179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1244944200962862034400477 466854075361073262900179)
              ·
                refine ⟨700281113041609894350269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466854075361073262900179 700281113041609894350269)
                ·
                  refine ⟨262605417390603710381351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700281113041609894350269 262605417390603710381351)
                  ·
                    rfl

theorem cell20_575350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_575350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575350 prefixEnd_575350 := by exact prefixLift 575350
  have htrace : WordTrace (prefixWord ++ tailWord_575350) baseStart_575350 baseEnd_575350 := by
    simpa [prefixWord, tailWord_575350, baseEnd_575350] using wordTrace_append hprefix tailTrace_575350
  have hstable : (prefixWord ++ tailWord_575350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575350).length < 2 ^ (prefixWord ++ tailWord_575350).sum := by decide
  have hdescent : baseEnd_575350 < baseStart_575350 := by decide
  rcases family_descends (prefixWord ++ tailWord_575350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575368 : List Nat := [2, 1, 3, 3, 3, 1, 1, 6]
def baseStart_575368 : Nat := 118140960795 + 575368 * 2 ^ 59
def prefixEnd_575368 : Nat := 4983230072969 + 3 ^ 40 * 575368 * 2
def baseEnd_575368 : Nat := 87537877693691882593759

theorem tailTrace_575368 : CollatzResearch.WordTrace tailWord_575368 prefixEnd_575368 87537877693691882593759 := by
  unfold tailWord_575368
  simp only [CollatzResearch.WordTrace]
  refine ⟨10492697489773737938115379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13990263319698317250820505 10492697489773737938115379)
  ·
    refine ⟨15739046234660606907173069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10492697489773737938115379 15739046234660606907173069)
    ·
      refine ⟨5902142337997727590189901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15739046234660606907173069 5902142337997727590189901)
      ·
        refine ⟨2213303376749147846321213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5902142337997727590189901 2213303376749147846321213)
        ·
          refine ⟨829988766280930442370455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2213303376749147846321213 829988766280930442370455)
          ·
            refine ⟨1244983149421395663555683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 829988766280930442370455 1244983149421395663555683)
            ·
              refine ⟨1867474724132093495333525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1244983149421395663555683 1867474724132093495333525)
              ·
                refine ⟨87537877693691882593759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1867474724132093495333525 87537877693691882593759)
                ·
                  rfl

theorem cell20_575368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_575368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575368 prefixEnd_575368 := by exact prefixLift 575368
  have htrace : WordTrace (prefixWord ++ tailWord_575368) baseStart_575368 baseEnd_575368 := by
    simpa [prefixWord, tailWord_575368, baseEnd_575368] using wordTrace_append hprefix tailTrace_575368
  have hstable : (prefixWord ++ tailWord_575368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575368).length < 2 ^ (prefixWord ++ tailWord_575368).sum := by decide
  have hdescent : baseEnd_575368 < baseStart_575368 := by decide
  rcases family_descends (prefixWord ++ tailWord_575368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575374 : List Nat := [4, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_575374 : Nat := 118140960795 + 575374 * 2 ^ 59
def prefixEnd_575374 : Nat := 4983230072969 + 3 ^ 40 * 575374 * 2
def baseEnd_575374 : Nat := 262616371644566293581253

theorem tailTrace_575374 : CollatzResearch.WordTrace tailWord_575374 prefixEnd_575374 262616371644566293581253 := by
  unfold tailWord_575374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2623201727190717362618647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13990409211683825933966117 2623201727190717362618647)
  ·
    refine ⟨3934802590786076043927971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2623201727190717362618647 3934802590786076043927971)
    ·
      refine ⟨5902203886179114065891957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3934802590786076043927971 5902203886179114065891957)
      ·
        refine ⟨553331614329291943677371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5902203886179114065891957 553331614329291943677371)
        ·
          refine ⟨829997421493937915516057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553331614329291943677371 829997421493937915516057)
          ·
            refine ⟨622498066120453436637043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 829997421493937915516057 622498066120453436637043)
            ·
              refine ⟨933747099180680154955565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622498066120453436637043 933747099180680154955565)
              ·
                refine ⟨350155162192755058108337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 933747099180680154955565 350155162192755058108337)
                ·
                  refine ⟨262616371644566293581253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350155162192755058108337 262616371644566293581253)
                  ·
                    rfl

theorem cell20_575374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_575374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575374 prefixEnd_575374 := by exact prefixLift 575374
  have htrace : WordTrace (prefixWord ++ tailWord_575374) baseStart_575374 baseEnd_575374 := by
    simpa [prefixWord, tailWord_575374, baseEnd_575374] using wordTrace_append hprefix tailTrace_575374
  have hstable : (prefixWord ++ tailWord_575374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575374).length < 2 ^ (prefixWord ++ tailWord_575374).sum := by decide
  have hdescent : baseEnd_575374 < baseStart_575374 := by decide
  rcases family_descends (prefixWord ++ tailWord_575374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575389 : List Nat := [1, 4, 2, 1, 2, 2, 8]
def baseStart_575389 : Nat := 118140960795 + 575389 * 2 ^ 59
def prefixEnd_575389 : Nat := 4983230072969 + 3 ^ 40 * 575389 * 2
def baseEnd_575389 : Nat := 29180357561476989786799

theorem tailTrace_575389 : CollatzResearch.WordTrace tailWord_575389 prefixEnd_575389 29180357561476989786799 := by
  unfold tailWord_575389
  simp only [CollatzResearch.WordTrace]
  refine ⟨20986160912471396462745221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13990773941647597641830147 20986160912471396462745221)
  ·
    refine ⟨3934905171088386836764729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20986160912471396462745221 3934905171088386836764729)
    ·
      refine ⟨2951178878316290127573547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3934905171088386836764729 2951178878316290127573547)
      ·
        refine ⟨4426768317474435191360321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2951178878316290127573547 4426768317474435191360321)
        ·
          refine ⟨3320076238105826393520241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4426768317474435191360321 3320076238105826393520241)
          ·
            refine ⟨2490057178579369795140181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3320076238105826393520241 2490057178579369795140181)
            ·
              refine ⟨29180357561476989786799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2490057178579369795140181 29180357561476989786799)
              ·
                rfl

theorem cell20_575389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 8].length) (baseStart_575389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575389 prefixEnd_575389 := by exact prefixLift 575389
  have htrace : WordTrace (prefixWord ++ tailWord_575389) baseStart_575389 baseEnd_575389 := by
    simpa [prefixWord, tailWord_575389, baseEnd_575389] using wordTrace_append hprefix tailTrace_575389
  have hstable : (prefixWord ++ tailWord_575389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575389).length < 2 ^ (prefixWord ++ tailWord_575389).sum := by decide
  have hdescent : baseEnd_575389 < baseStart_575389 := by decide
  rcases family_descends (prefixWord ++ tailWord_575389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575399 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_575399 : Nat := 118140960795 + 575399 * 2 ^ 59
def prefixEnd_575399 : Nat := 4983230072969 + 3 ^ 40 * 575399 * 2
def baseEnd_575399 : Nat := 262627782325777317747817

theorem tailTrace_575399 : CollatzResearch.WordTrace tailWord_575399 prefixEnd_575399 262627782325777317747817 := by
  unfold tailWord_575399
  simp only [CollatzResearch.WordTrace]
  refine ⟨20986525642435168170609251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13991017094956778780406167 20986525642435168170609251)
  ·
    refine ⟨31479788463652752255913877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20986525642435168170609251 31479788463652752255913877)
    ·
      refine ⟨1475615084233722761995963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31479788463652752255913877 1475615084233722761995963)
      ·
        refine ⟨2213422626350584142993945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1475615084233722761995963 2213422626350584142993945)
        ·
          refine ⟨1660066969762938107245459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213422626350584142993945 1660066969762938107245459)
          ·
            refine ⟨2490100454644407160868189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660066969762938107245459 2490100454644407160868189)
            ·
              refine ⟨933787670491652685325571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2490100454644407160868189 933787670491652685325571)
              ·
                refine ⟨1400681505737479027988357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 933787670491652685325571 1400681505737479027988357)
                ·
                  refine ⟨262627782325777317747817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1400681505737479027988357 262627782325777317747817)
                  ·
                    rfl

theorem cell20_575399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_575399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575399 prefixEnd_575399 := by exact prefixLift 575399
  have htrace : WordTrace (prefixWord ++ tailWord_575399) baseStart_575399 baseEnd_575399 := by
    simpa [prefixWord, tailWord_575399, baseEnd_575399] using wordTrace_append hprefix tailTrace_575399
  have hstable : (prefixWord ++ tailWord_575399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575399).length < 2 ^ (prefixWord ++ tailWord_575399).sum := by decide
  have hdescent : baseEnd_575399 < baseStart_575399 := by decide
  rcases family_descends (prefixWord ++ tailWord_575399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575409 : List Nat := [1, 2, 2, 4, 2, 3, 2, 1, 3]
def baseStart_575409 : Nat := 118140960795 + 575409 * 2 ^ 59
def prefixEnd_575409 : Nat := 4983230072969 + 3 ^ 40 * 575409 * 2
def baseEnd_575409 : Nat := 262632346598261727414443

theorem tailTrace_575409 : CollatzResearch.WordTrace tailWord_575409 prefixEnd_575409 262632346598261727414443 := by
  unfold tailWord_575409
  simp only [CollatzResearch.WordTrace]
  refine ⟨20986890372398939878473281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13991260248265959918982187 20986890372398939878473281)
  ·
    refine ⟨15740167779299204908854961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20986890372398939878473281 15740167779299204908854961)
    ·
      refine ⟨11805125834474403681641221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15740167779299204908854961 11805125834474403681641221)
      ·
        refine ⟨2213461093963950690307729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11805125834474403681641221 2213461093963950690307729)
        ·
          refine ⟨1660095820472963017730797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2213461093963950690307729 1660095820472963017730797)
          ·
            refine ⟨622535932677361131649049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1660095820472963017730797 622535932677361131649049)
            ·
              refine ⟨466901949508020848736787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622535932677361131649049 466901949508020848736787)
              ·
                refine ⟨700352924262031273105181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 466901949508020848736787 700352924262031273105181)
                ·
                  refine ⟨262632346598261727414443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700352924262031273105181 262632346598261727414443)
                  ·
                    rfl

theorem cell20_575409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_575409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575409 prefixEnd_575409 := by exact prefixLift 575409
  have htrace : WordTrace (prefixWord ++ tailWord_575409) baseStart_575409 baseEnd_575409 := by
    simpa [prefixWord, tailWord_575409, baseEnd_575409] using wordTrace_append hprefix tailTrace_575409
  have hstable : (prefixWord ++ tailWord_575409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575409).length < 2 ^ (prefixWord ++ tailWord_575409).sum := by decide
  have hdescent : baseEnd_575409 < baseStart_575409 := by decide
  rcases family_descends (prefixWord ++ tailWord_575409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575434 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_575434 : Nat := 118140960795 + 575434 * 2 ^ 59
def prefixEnd_575434 : Nat := 4983230072969 + 3 ^ 40 * 575434 * 2
def baseEnd_575434 : Nat := 262643757279472751581007

theorem tailTrace_575434 : CollatzResearch.WordTrace tailWord_575434 prefixEnd_575434 262643757279472751581007 := by
  unfold tailWord_575434
  simp only [CollatzResearch.WordTrace]
  refine ⟨5246950549327092287033339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13991868131538912765422237 5246950549327092287033339)
  ·
    refine ⟨7870425823990638430550009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5246950549327092287033339 7870425823990638430550009)
    ·
      refine ⟨5902819367992978822912507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7870425823990638430550009 5902819367992978822912507)
      ·
        refine ⟨8854229051989468234368761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5902819367992978822912507 8854229051989468234368761)
        ·
          refine ⟨6640671788992101175776571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8854229051989468234368761 6640671788992101175776571)
          ·
            refine ⟨9961007683488151763664857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6640671788992101175776571 9961007683488151763664857)
            ·
              refine ⟨7470755762616113822748643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9961007683488151763664857 7470755762616113822748643)
              ·
                refine ⟨11206133643924170734122965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7470755762616113822748643 11206133643924170734122965)
                ·
                  refine ⟨262643757279472751581007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11206133643924170734122965 262643757279472751581007)
                  ·
                    rfl

theorem cell20_575434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_575434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575434 prefixEnd_575434 := by exact prefixLift 575434
  have htrace : WordTrace (prefixWord ++ tailWord_575434) baseStart_575434 baseEnd_575434 := by
    simpa [prefixWord, tailWord_575434, baseEnd_575434] using wordTrace_append hprefix tailTrace_575434
  have hstable : (prefixWord ++ tailWord_575434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575434).length < 2 ^ (prefixWord ++ tailWord_575434).sum := by decide
  have hdescent : baseEnd_575434 < baseStart_575434 := by decide
  rcases family_descends (prefixWord ++ tailWord_575434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575441 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_575441 : Nat := 118140960795 + 575441 * 2 ^ 59
def prefixEnd_575441 : Nat := 4983230072969 + 3 ^ 40 * 575441 * 2
def baseEnd_575441 : Nat := 262646952270211838347645

theorem tailTrace_575441 : CollatzResearch.WordTrace tailWord_575441 prefixEnd_575441 262646952270211838347645 := by
  unfold tailWord_575441
  simp only [CollatzResearch.WordTrace]
  refine ⟨20988057508283009343638177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13992038338855339562425451 20988057508283009343638177)
  ·
    refine ⟨15741043131212257007728633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20988057508283009343638177 15741043131212257007728633)
    ·
      refine ⟨11805782348409192755796475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15741043131212257007728633 11805782348409192755796475)
      ·
        refine ⟨17708673522613789133694713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11805782348409192755796475 17708673522613789133694713)
        ·
          refine ⟨13281505141960341850271035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17708673522613789133694713 13281505141960341850271035)
          ·
            refine ⟨19922257712940512775406553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13281505141960341850271035 19922257712940512775406553)
            ·
              refine ⟨14941693284705384581554915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19922257712940512775406553 14941693284705384581554915)
              ·
                refine ⟨22412539927058076872332373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14941693284705384581554915 22412539927058076872332373)
                ·
                  refine ⟨262646952270211838347645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22412539927058076872332373 262646952270211838347645)
                  ·
                    rfl

theorem cell20_575441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_575441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575441 prefixEnd_575441 := by exact prefixLift 575441
  have htrace : WordTrace (prefixWord ++ tailWord_575441) baseStart_575441 baseEnd_575441 := by
    simpa [prefixWord, tailWord_575441, baseEnd_575441] using wordTrace_append hprefix tailTrace_575441
  have hstable : (prefixWord ++ tailWord_575441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575441).length < 2 ^ (prefixWord ++ tailWord_575441).sum := by decide
  have hdescent : baseEnd_575441 < baseStart_575441 := by decide
  rcases family_descends (prefixWord ++ tailWord_575441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575450 : List Nat := [3, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_575450 : Nat := 118140960795 + 575450 * 2 ^ 59
def prefixEnd_575450 : Nat := 4983230072969 + 3 ^ 40 * 575450 * 2
def baseEnd_575450 : Nat := 262651060115447807047609

theorem tailTrace_575450 : CollatzResearch.WordTrace tailWord_575450 prefixEnd_575450 262651060115447807047609 := by
  unfold tailWord_575450
  simp only [CollatzResearch.WordTrace]
  refine ⟨5247096441312600970178951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13992257176833602587143869 5247096441312600970178951)
  ·
    refine ⟨7870644661968901455268427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5247096441312600970178951 7870644661968901455268427)
    ·
      refine ⟨11805966992953352182902641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7870644661968901455268427 11805966992953352182902641)
      ·
        refine ⟨8854475244715014137176981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11805966992953352182902641 8854475244715014137176981)
        ·
          refine ⟨415053527096016287680171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8854475244715014137176981 415053527096016287680171)
          ·
            refine ⟨622580290644024431520257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415053527096016287680171 622580290644024431520257)
            ·
              refine ⟨466935217983018323640193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 622580290644024431520257 466935217983018323640193)
              ·
                refine ⟨350201413487263742730145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 466935217983018323640193 350201413487263742730145)
                ·
                  refine ⟨262651060115447807047609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350201413487263742730145 262651060115447807047609)
                  ·
                    rfl

theorem cell20_575450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_575450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575450 prefixEnd_575450 := by exact prefixLift 575450
  have htrace : WordTrace (prefixWord ++ tailWord_575450) baseStart_575450 baseEnd_575450 := by
    simpa [prefixWord, tailWord_575450, baseEnd_575450] using wordTrace_append hprefix tailTrace_575450
  have hstable : (prefixWord ++ tailWord_575450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575450).length < 2 ^ (prefixWord ++ tailWord_575450).sum := by decide
  have hdescent : baseEnd_575450 < baseStart_575450 := by decide
  rcases family_descends (prefixWord ++ tailWord_575450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575548 : List Nat := [2, 2, 2, 2, 2, 1, 1, 1, 7]
def baseStart_575548 : Nat := 118140960795 + 575548 * 2 ^ 59
def prefixEnd_575548 : Nat := 4983230072969 + 3 ^ 40 * 575548 * 2
def baseEnd_575548 : Nat := 262695789985795021780541

theorem tailTrace_575548 : CollatzResearch.WordTrace tailWord_575548 prefixEnd_575548 262695789985795021780541 := by
  unfold tailWord_575548
  simp only [CollatzResearch.WordTrace]
  refine ⟨10495980059447683308891649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13994640079263577745188865 10495980059447683308891649)
  ·
    refine ⟨7871985044585762481668737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10495980059447683308891649 7871985044585762481668737)
    ·
      refine ⟨5903988783439321861251553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7871985044585762481668737 5903988783439321861251553)
      ·
        refine ⟨4427991587579491395938665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5903988783439321861251553 4427991587579491395938665)
        ·
          refine ⟨3320993690684618546953999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4427991587579491395938665 3320993690684618546953999)
          ·
            refine ⟨4981490536026927820430999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320993690684618546953999 4981490536026927820430999)
            ·
              refine ⟨7472235804040391730646499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981490536026927820430999 7472235804040391730646499)
              ·
                refine ⟨11208353706060587595969749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7472235804040391730646499 11208353706060587595969749)
                ·
                  refine ⟨262695789985795021780541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11208353706060587595969749 262695789985795021780541)
                  ·
                    rfl

theorem cell20_575548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_575548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575548 prefixEnd_575548 := by exact prefixLift 575548
  have htrace : WordTrace (prefixWord ++ tailWord_575548) baseStart_575548 baseEnd_575548 := by
    simpa [prefixWord, tailWord_575548, baseEnd_575548] using wordTrace_append hprefix tailTrace_575548
  have hstable : (prefixWord ++ tailWord_575548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575548).length < 2 ^ (prefixWord ++ tailWord_575548).sum := by decide
  have hdescent : baseEnd_575548 < baseStart_575548 := by decide
  rcases family_descends (prefixWord ++ tailWord_575548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575551 : List Nat := [1, 1, 2, 2, 3, 1, 5, 3, 2]
def baseStart_575551 : Nat := 118140960795 + 575551 * 2 ^ 59
def prefixEnd_575551 : Nat := 4983230072969 + 3 ^ 40 * 575551 * 2
def baseEnd_575551 : Nat := 262697159267540344680529

theorem tailTrace_575551 : CollatzResearch.WordTrace tailWord_575551 prefixEnd_575551 262697159267540344680529 := by
  unfold tailWord_575551
  simp only [CollatzResearch.WordTrace]
  refine ⟨20992069537884498130142507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13994713025256332086761671 20992069537884498130142507)
  ·
    refine ⟨31488104306826747195213761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20992069537884498130142507 31488104306826747195213761)
    ·
      refine ⟨23616078230120060396410321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31488104306826747195213761 23616078230120060396410321)
      ·
        refine ⟨17712058672590045297307741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23616078230120060396410321 17712058672590045297307741)
        ·
          refine ⟨6642022002221266986490403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17712058672590045297307741 6642022002221266986490403)
          ·
            refine ⟨9963033003331900479735605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642022002221266986490403 9963033003331900479735605)
            ·
              refine ⟨934034344062365669975213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9963033003331900479735605 934034344062365669975213)
              ·
                refine ⟨350262879023387126240705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 934034344062365669975213 350262879023387126240705)
                ·
                  refine ⟨262697159267540344680529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350262879023387126240705 262697159267540344680529)
                  ·
                    rfl

theorem cell20_575551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 2].length) (baseStart_575551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575551 prefixEnd_575551 := by exact prefixLift 575551
  have htrace : WordTrace (prefixWord ++ tailWord_575551) baseStart_575551 baseEnd_575551 := by
    simpa [prefixWord, tailWord_575551, baseEnd_575551] using wordTrace_append hprefix tailTrace_575551
  have hstable : (prefixWord ++ tailWord_575551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575551).length < 2 ^ (prefixWord ++ tailWord_575551).sum := by decide
  have hdescent : baseEnd_575551 < baseStart_575551 := by decide
  rcases family_descends (prefixWord ++ tailWord_575551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575565 : List Nat := [1, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_575565 : Nat := 118140960795 + 575565 * 2 ^ 59
def prefixEnd_575565 : Nat := 4983230072969 + 3 ^ 40 * 575565 * 2
def baseEnd_575565 : Nat := 262703549249018518213805

theorem tailTrace_575565 : CollatzResearch.WordTrace tailWord_575565 prefixEnd_575565 262703549249018518213805 := by
  unfold tailWord_575565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20992580159833778521152149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13995053439889185680768099 20992580159833778521152149)
  ·
    refine ⟨984027194992208368179007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20992580159833778521152149 984027194992208368179007)
    ·
      refine ⟨1476040792488312552268511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984027194992208368179007 1476040792488312552268511)
      ·
        refine ⟨2214061188732468828402767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476040792488312552268511 2214061188732468828402767)
        ·
          refine ⟨3321091783098703242604151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214061188732468828402767 3321091783098703242604151)
          ·
            refine ⟨4981637674648054863906227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321091783098703242604151 4981637674648054863906227)
            ·
              refine ⟨7472456511972082295859341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981637674648054863906227 7472456511972082295859341)
              ·
                refine ⟨2802171191989530860947253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7472456511972082295859341 2802171191989530860947253)
                ·
                  refine ⟨262703549249018518213805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2802171191989530860947253 262703549249018518213805)
                  ·
                    rfl

theorem cell20_575565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_575565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575565 prefixEnd_575565 := by exact prefixLift 575565
  have htrace : WordTrace (prefixWord ++ tailWord_575565) baseStart_575565 baseEnd_575565 := by
    simpa [prefixWord, tailWord_575565, baseEnd_575565] using wordTrace_append hprefix tailTrace_575565
  have hstable : (prefixWord ++ tailWord_575565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575565).length < 2 ^ (prefixWord ++ tailWord_575565).sum := by decide
  have hdescent : baseEnd_575565 < baseStart_575565 := by decide
  rcases family_descends (prefixWord ++ tailWord_575565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575593 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 6]
def baseStart_575593 : Nat := 118140960795 + 575593 * 2 ^ 59
def prefixEnd_575593 : Nat := 4983230072969 + 3 ^ 40 * 575593 * 2
def baseEnd_575593 : Nat := 262716329211974865280357

theorem tailTrace_575593 : CollatzResearch.WordTrace tailWord_575593 prefixEnd_575593 262716329211974865280357 := by
  unfold tailWord_575593
  simp only [CollatzResearch.WordTrace]
  refine ⟨20993601403732339303171433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13995734269154892868780955 20993601403732339303171433)
  ·
    refine ⟨15745201052799254477378575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20993601403732339303171433 15745201052799254477378575)
    ·
      refine ⟨23617801579198881716067863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15745201052799254477378575 23617801579198881716067863)
      ·
        refine ⟨35426702368798322574101795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23617801579198881716067863 35426702368798322574101795)
        ·
          refine ⟨53140053553197483861152693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35426702368798322574101795 53140053553197483861152693)
          ·
            refine ⟨4981880020612264111983065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53140053553197483861152693 4981880020612264111983065)
            ·
              refine ⟨3736410015459198083987299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4981880020612264111983065 3736410015459198083987299)
              ·
                refine ⟨5604615023188797125980949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736410015459198083987299 5604615023188797125980949)
                ·
                  refine ⟨262716329211974865280357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5604615023188797125980949 262716329211974865280357)
                  ·
                    rfl

theorem cell20_575593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_575593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575593 prefixEnd_575593 := by exact prefixLift 575593
  have htrace : WordTrace (prefixWord ++ tailWord_575593) baseStart_575593 baseEnd_575593 := by
    simpa [prefixWord, tailWord_575593, baseEnd_575593] using wordTrace_append hprefix tailTrace_575593
  have hstable : (prefixWord ++ tailWord_575593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575593).length < 2 ^ (prefixWord ++ tailWord_575593).sum := by decide
  have hdescent : baseEnd_575593 < baseStart_575593 := by decide
  rcases family_descends (prefixWord ++ tailWord_575593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575617 : List Nat := [1, 2, 4, 2, 3, 8]
def baseStart_575617 : Nat := 118140960795 + 575617 * 2 ^ 59
def prefixEnd_575617 : Nat := 4983230072969 + 3 ^ 40 * 575617 * 2
def baseEnd_575617 : Nat := 9730640128368053647417

theorem tailTrace_575617 : CollatzResearch.WordTrace tailWord_575617 prefixEnd_575617 9730640128368053647417 := by
  unfold tailWord_575617
  simp only [CollatzResearch.WordTrace]
  refine ⟨20994476755645391402045105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13996317837096927601363403 20994476755645391402045105)
  ·
    refine ⟨15745857566734043551533829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20994476755645391402045105 15745857566734043551533829)
    ·
      refine ⟨2952348293762633165912593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15745857566734043551533829 2952348293762633165912593)
      ·
        refine ⟨2214261220321974874434445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2952348293762633165912593 2214261220321974874434445)
        ·
          refine ⟨830347957620740577912917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2214261220321974874434445 830347957620740577912917)
          ·
            refine ⟨9730640128368053647417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 830347957620740577912917 9730640128368053647417)
            ·
              rfl

theorem cell20_575617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 8].length) (baseStart_575617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575617 prefixEnd_575617 := by exact prefixLift 575617
  have htrace : WordTrace (prefixWord ++ tailWord_575617) baseStart_575617 baseEnd_575617 := by
    simpa [prefixWord, tailWord_575617, baseEnd_575617] using wordTrace_append hprefix tailTrace_575617
  have hstable : (prefixWord ++ tailWord_575617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575617).length < 2 ^ (prefixWord ++ tailWord_575617).sum := by decide
  have hdescent : baseEnd_575617 < baseStart_575617 := by decide
  rcases family_descends (prefixWord ++ tailWord_575617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575648 : List Nat := [2, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_575648 : Nat := 118140960795 + 575648 * 2 ^ 59
def prefixEnd_575648 : Nat := 4983230072969 + 3 ^ 40 * 575648 * 2
def baseEnd_575648 : Nat := 262741432710639118446799

theorem tailTrace_575648 : CollatzResearch.WordTrace tailWord_575648 prefixEnd_575648 262741432710639118446799 := by
  unfold tailWord_575648
  simp only [CollatzResearch.WordTrace]
  refine ⟨10497803709266541848211799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13997071612355389130949065 10497803709266541848211799)
  ·
    refine ⟨15746705563899812772317699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10497803709266541848211799 15746705563899812772317699)
    ·
      refine ⟨23620058345849719158476549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15746705563899812772317699 23620058345849719158476549)
      ·
        refine ⟨4428760939846822342214353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23620058345849719158476549 4428760939846822342214353)
        ·
          refine ⟨3321570704885116756660765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4428760939846822342214353 3321570704885116756660765)
          ·
            refine ⟨1245589014331918783747787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3321570704885116756660765 1245589014331918783747787)
            ·
              refine ⟨1868383521497878175621681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245589014331918783747787 1868383521497878175621681)
              ·
                refine ⟨1401287641123408631716261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1868383521497878175621681 1401287641123408631716261)
                ·
                  refine ⟨262741432710639118446799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401287641123408631716261 262741432710639118446799)
                  ·
                    rfl

theorem cell20_575648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_575648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575648 prefixEnd_575648 := by exact prefixLift 575648
  have htrace : WordTrace (prefixWord ++ tailWord_575648) baseStart_575648 baseEnd_575648 := by
    simpa [prefixWord, tailWord_575648, baseEnd_575648] using wordTrace_append hprefix tailTrace_575648
  have hstable : (prefixWord ++ tailWord_575648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575648).length < 2 ^ (prefixWord ++ tailWord_575648).sum := by decide
  have hdescent : baseEnd_575648 < baseStart_575648 := by decide
  rcases family_descends (prefixWord ++ tailWord_575648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575668 : List Nat := [2, 5, 3, 1, 1, 1, 7]
def baseStart_575668 : Nat := 118140960795 + 575668 * 2 ^ 59
def prefixEnd_575668 : Nat := 4983230072969 + 3 ^ 40 * 575668 * 2
def baseEnd_575668 : Nat := 29194506806178659753339

theorem tailTrace_575668 : CollatzResearch.WordTrace tailWord_575668 prefixEnd_575668 29194506806178659753339 := by
  unfold tailWord_575668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10498168439230313556075829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13997557918973751408101105 10498168439230313556075829)
  ·
    refine ⟨984203291177841895882109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10498168439230313556075829 984203291177841895882109)
    ·
      refine ⟨369076234191690710955791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 984203291177841895882109 369076234191690710955791)
      ·
        refine ⟨553614351287536066433687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369076234191690710955791 553614351287536066433687)
        ·
          refine ⟨830421526931304099650531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553614351287536066433687 830421526931304099650531)
          ·
            refine ⟨1245632290396956149475797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830421526931304099650531 1245632290396956149475797)
            ·
              refine ⟨29194506806178659753339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1245632290396956149475797 29194506806178659753339)
              ·
                rfl

theorem cell20_575668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 7].length) (baseStart_575668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575668 prefixEnd_575668 := by exact prefixLift 575668
  have htrace : WordTrace (prefixWord ++ tailWord_575668) baseStart_575668 baseEnd_575668 := by
    simpa [prefixWord, tailWord_575668, baseEnd_575668] using wordTrace_append hprefix tailTrace_575668
  have hstable : (prefixWord ++ tailWord_575668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575668).length < 2 ^ (prefixWord ++ tailWord_575668).sum := by decide
  have hdescent : baseEnd_575668 < baseStart_575668 := by decide
  rcases family_descends (prefixWord ++ tailWord_575668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575682 : List Nat := [3, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_575682 : Nat := 118140960795 + 575682 * 2 ^ 59
def prefixEnd_575682 : Nat := 4983230072969 + 3 ^ 40 * 575682 * 2
def baseEnd_575682 : Nat := 262756951237086111313327

theorem tailTrace_575682 : CollatzResearch.WordTrace tailWord_575682 prefixEnd_575682 262756951237086111313327 := by
  unfold tailWord_575682
  simp only [CollatzResearch.WordTrace]
  refine ⟨5249211875102476875790325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13997898333606605002107533 5249211875102476875790325)
  ·
    refine ⟨492113613290857207105343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5249211875102476875790325 492113613290857207105343)
    ·
      refine ⟨738170419936285810658015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 492113613290857207105343 738170419936285810658015)
      ·
        refine ⟨1107255629904428715987023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738170419936285810658015 1107255629904428715987023)
        ·
          refine ⟨1660883444856643073980535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1107255629904428715987023 1660883444856643073980535)
          ·
            refine ⟨2491325167284964610970803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1660883444856643073980535 2491325167284964610970803)
            ·
              refine ⟨3736987750927446916456205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2491325167284964610970803 3736987750927446916456205)
              ·
                refine ⟨1401370406597792593671077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3736987750927446916456205 1401370406597792593671077)
                ·
                  refine ⟨262756951237086111313327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1401370406597792593671077 262756951237086111313327)
                  ·
                    rfl

theorem cell20_575682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_575682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575682 prefixEnd_575682 := by exact prefixLift 575682
  have htrace : WordTrace (prefixWord ++ tailWord_575682) baseStart_575682 baseEnd_575682 := by
    simpa [prefixWord, tailWord_575682, baseEnd_575682] using wordTrace_append hprefix tailTrace_575682
  have hstable : (prefixWord ++ tailWord_575682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575682).length < 2 ^ (prefixWord ++ tailWord_575682).sum := by decide
  have hdescent : baseEnd_575682 < baseStart_575682 := by decide
  rcases family_descends (prefixWord ++ tailWord_575682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575720 : List Nat := [2, 1, 4, 1, 2, 4, 1, 3, 2]
def baseStart_575720 : Nat := 118140960795 + 575720 * 2 ^ 59
def prefixEnd_575720 : Nat := 4983230072969 + 3 ^ 40 * 575720 * 2
def baseEnd_575720 : Nat := 262774295472526868046505

theorem tailTrace_575720 : CollatzResearch.WordTrace tailWord_575720 prefixEnd_575720 262774295472526868046505 := by
  unfold tailWord_575720
  simp only [CollatzResearch.WordTrace]
  refine ⟨10499116737136119996522307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13998822316181493328696409 10499116737136119996522307)
  ·
    refine ⟨15748675105704179994783461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10499116737136119996522307 15748675105704179994783461)
    ·
      refine ⟨2952876582319533749021899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15748675105704179994783461 2952876582319533749021899)
      ·
        refine ⟨4429314873479300623532849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952876582319533749021899 4429314873479300623532849)
        ·
          refine ⟨3321986155109475467649637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4429314873479300623532849 3321986155109475467649637)
          ·
            refine ⟨622872404083026650184307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3321986155109475467649637 622872404083026650184307)
            ·
              refine ⟨934308606124539975276461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 622872404083026650184307 934308606124539975276461)
              ·
                refine ⟨350365727296702490728673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 934308606124539975276461 350365727296702490728673)
                ·
                  refine ⟨262774295472526868046505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350365727296702490728673 262774295472526868046505)
                  ·
                    rfl

theorem cell20_575720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_575720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575720 prefixEnd_575720 := by exact prefixLift 575720
  have htrace : WordTrace (prefixWord ++ tailWord_575720) baseStart_575720 baseEnd_575720 := by
    simpa [prefixWord, tailWord_575720, baseEnd_575720] using wordTrace_append hprefix tailTrace_575720
  have hstable : (prefixWord ++ tailWord_575720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575720).length < 2 ^ (prefixWord ++ tailWord_575720).sum := by decide
  have hdescent : baseEnd_575720 < baseStart_575720 := by decide
  rcases family_descends (prefixWord ++ tailWord_575720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575738 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_575738 : Nat := 118140960795 + 575738 * 2 ^ 59
def prefixEnd_575738 : Nat := 4983230072969 + 3 ^ 40 * 575738 * 2
def baseEnd_575738 : Nat := 262782511162998805446431

theorem tailTrace_575738 : CollatzResearch.WordTrace tailWord_575738 prefixEnd_575738 262782511162998805446431 := by
  unfold tailWord_575738
  simp only [CollatzResearch.WordTrace]
  refine ⟨5249722497051757266799967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13999259992138019378133245 5249722497051757266799967)
  ·
    refine ⟨7874583745577635900199951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5249722497051757266799967 7874583745577635900199951)
    ·
      refine ⟨11811875618366453850299927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7874583745577635900199951 11811875618366453850299927)
      ·
        refine ⟨17717813427549680775449891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11811875618366453850299927 17717813427549680775449891)
        ·
          refine ⟨26576720141324521163174837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17717813427549680775449891 26576720141324521163174837)
          ·
            refine ⟨2491567513249173859047641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26576720141324521163174837 2491567513249173859047641)
            ·
              refine ⟨1868675634936880394285731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2491567513249173859047641 1868675634936880394285731)
              ·
                refine ⟨2803013452405320591428597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1868675634936880394285731 2803013452405320591428597)
                ·
                  refine ⟨262782511162998805446431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2803013452405320591428597 262782511162998805446431)
                  ·
                    rfl

theorem cell20_575738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_575738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575738 prefixEnd_575738 := by exact prefixLift 575738
  have htrace : WordTrace (prefixWord ++ tailWord_575738) baseStart_575738 baseEnd_575738 := by
    simpa [prefixWord, tailWord_575738, baseEnd_575738] using wordTrace_append hprefix tailTrace_575738
  have hstable : (prefixWord ++ tailWord_575738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575738).length < 2 ^ (prefixWord ++ tailWord_575738).sum := by decide
  have hdescent : baseEnd_575738 < baseStart_575738 := by decide
  rcases family_descends (prefixWord ++ tailWord_575738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575748 : List Nat := [2, 3, 2, 2, 3, 1, 2, 5]
def baseStart_575748 : Nat := 118140960795 + 575748 * 2 ^ 59
def prefixEnd_575748 : Nat := 4983230072969 + 3 ^ 40 * 575748 * 2
def baseEnd_575748 : Nat := 87595691811827738371019

theorem tailTrace_575748 : CollatzResearch.WordTrace tailWord_575748 prefixEnd_575748 87595691811827738371019 := by
  unfold tailWord_575748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10499627359085400387531949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13999503145447200516709265 10499627359085400387531949)
  ·
    refine ⟨3937360259657025145324481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10499627359085400387531949 3937360259657025145324481)
    ·
      refine ⟨2953020194742768858993361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3937360259657025145324481 2953020194742768858993361)
      ·
        refine ⟨2214765146057076644245021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2953020194742768858993361 2214765146057076644245021)
        ·
          refine ⟨830536929771403741591883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2214765146057076644245021 830536929771403741591883)
          ·
            refine ⟨1245805394657105612387825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830536929771403741591883 1245805394657105612387825)
            ·
              refine ⟨934354045992829209290869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245805394657105612387825 934354045992829209290869)
              ·
                refine ⟨87595691811827738371019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 934354045992829209290869 87595691811827738371019)
                ·
                  rfl

theorem cell20_575748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 5].length) (baseStart_575748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575748 prefixEnd_575748 := by exact prefixLift 575748
  have htrace : WordTrace (prefixWord ++ tailWord_575748) baseStart_575748 baseEnd_575748 := by
    simpa [prefixWord, tailWord_575748, baseEnd_575748] using wordTrace_append hprefix tailTrace_575748
  have hstable : (prefixWord ++ tailWord_575748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575748).length < 2 ^ (prefixWord ++ tailWord_575748).sum := by decide
  have hdescent : baseEnd_575748 < baseStart_575748 := by decide
  rcases family_descends (prefixWord ++ tailWord_575748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575786 : List Nat := [3, 1, 4, 2, 3, 7]
def baseStart_575786 : Nat := 118140960795 + 575786 * 2 ^ 59
def prefixEnd_575786 : Nat := 4983230072969 + 3 ^ 40 * 575786 * 2
def baseEnd_575786 : Nat := 9733497024849035994305

theorem tailTrace_575786 : CollatzResearch.WordTrace tailWord_575786 prefixEnd_575786 9733497024849035994305 := by
  unfold tailWord_575786
  simp only [CollatzResearch.WordTrace]
  refine ⟨5250160173008283316236803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14000427128022088843298141 5250160173008283316236803)
  ·
    refine ⟨7875240259512424974355205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5250160173008283316236803 7875240259512424974355205)
    ·
      refine ⟨1476607548658579682691601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7875240259512424974355205 1476607548658579682691601)
      ·
        refine ⟨1107455661493934762018701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1476607548658579682691601 1107455661493934762018701)
        ·
          refine ⟨415295873060225535757013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1107455661493934762018701 415295873060225535757013)
          ·
            refine ⟨9733497024849035994305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 415295873060225535757013 9733497024849035994305)
            ·
              rfl

theorem cell20_575786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 7].length) (baseStart_575786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575786 prefixEnd_575786 := by exact prefixLift 575786
  have htrace : WordTrace (prefixWord ++ tailWord_575786) baseStart_575786 baseEnd_575786 := by
    simpa [prefixWord, tailWord_575786, baseEnd_575786] using wordTrace_append hprefix tailTrace_575786
  have hstable : (prefixWord ++ tailWord_575786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575786).length < 2 ^ (prefixWord ++ tailWord_575786).sum := by decide
  have hdescent : baseEnd_575786 < baseStart_575786 := by decide
  rcases family_descends (prefixWord ++ tailWord_575786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575789 : List Nat := [1, 5, 3, 1, 2, 1, 2, 2, 3]
def baseStart_575789 : Nat := 118140960795 + 575789 * 2 ^ 59
def prefixEnd_575789 : Nat := 4983230072969 + 3 ^ 40 * 575789 * 2
def baseEnd_575789 : Nat := 262805788952669294746223

theorem tailTrace_575789 : CollatzResearch.WordTrace tailWord_575789 prefixEnd_575789 262805788952669294746223 := by
  unfold tailWord_575789
  simp only [CollatzResearch.WordTrace]
  refine ⟨21000750111022264777306421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14000500074014843184870947 21000750111022264777306421)
  ·
    refine ⟨1968820322908337322872477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21000750111022264777306421 1968820322908337322872477)
    ·
      refine ⟨738307621090626496077179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1968820322908337322872477 738307621090626496077179)
      ·
        refine ⟨1107461431635939744115769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 738307621090626496077179 1107461431635939744115769)
        ·
          refine ⟨830596073726954808086827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1107461431635939744115769 830596073726954808086827)
          ·
            refine ⟨1245894110590432212130241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830596073726954808086827 1245894110590432212130241)
            ·
              refine ⟨934420582942824159097681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1245894110590432212130241 934420582942824159097681)
              ·
                refine ⟨700815437207118119323261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934420582942824159097681 700815437207118119323261)
                ·
                  refine ⟨262805788952669294746223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700815437207118119323261 262805788952669294746223)
                  ·
                    rfl

theorem cell20_575789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_575789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575789 prefixEnd_575789 := by exact prefixLift 575789
  have htrace : WordTrace (prefixWord ++ tailWord_575789) baseStart_575789 baseEnd_575789 := by
    simpa [prefixWord, tailWord_575789, baseEnd_575789] using wordTrace_append hprefix tailTrace_575789
  have hstable : (prefixWord ++ tailWord_575789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575789).length < 2 ^ (prefixWord ++ tailWord_575789).sum := by decide
  have hdescent : baseEnd_575789 < baseStart_575789 := by decide
  rcases family_descends (prefixWord ++ tailWord_575789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575796 : List Nat := [2, 5, 1, 1, 1, 3, 1, 4, 2]
def baseStart_575796 : Nat := 118140960795 + 575796 * 2 ^ 59
def prefixEnd_575796 : Nat := 4983230072969 + 3 ^ 40 * 575796 * 2
def baseEnd_575796 : Nat := 262808983943408381512861

theorem tailTrace_575796 : CollatzResearch.WordTrace tailWord_575796 prefixEnd_575796 262808983943408381512861 := by
  unfold tailWord_575796
  simp only [CollatzResearch.WordTrace]
  refine ⟨10500502710998452486405621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14000670281331269981874161 10500502710998452486405621)
  ·
    refine ⟨984422129156104920600527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10500502710998452486405621 984422129156104920600527)
    ·
      refine ⟨1476633193734157380900791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 984422129156104920600527 1476633193734157380900791)
      ·
        refine ⟨2214949790601236071351187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1476633193734157380900791 2214949790601236071351187)
        ·
          refine ⟨3322424685901854107026781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2214949790601236071351187 3322424685901854107026781)
          ·
            refine ⟨1245909257213195290135043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3322424685901854107026781 1245909257213195290135043)
            ·
              refine ⟨1868863885819792935202565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1245909257213195290135043 1868863885819792935202565)
              ·
                refine ⟨350411978591211175350481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1868863885819792935202565 350411978591211175350481)
                ·
                  refine ⟨262808983943408381512861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350411978591211175350481 262808983943408381512861)
                  ·
                    rfl

theorem cell20_575796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_575796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575796 prefixEnd_575796 := by exact prefixLift 575796
  have htrace : WordTrace (prefixWord ++ tailWord_575796) baseStart_575796 baseEnd_575796 := by
    simpa [prefixWord, tailWord_575796, baseEnd_575796] using wordTrace_append hprefix tailTrace_575796
  have hstable : (prefixWord ++ tailWord_575796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575796).length < 2 ^ (prefixWord ++ tailWord_575796).sum := by decide
  have hdescent : baseEnd_575796 < baseStart_575796 := by decide
  rcases family_descends (prefixWord ++ tailWord_575796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575848 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_575848 : Nat := 118140960795 + 575848 * 2 ^ 59
def prefixEnd_575848 : Nat := 4983230072969 + 3 ^ 40 * 575848 * 2
def baseEnd_575848 : Nat := 262832718160327311779315

theorem tailTrace_575848 : CollatzResearch.WordTrace tailWord_575848 prefixEnd_575848 262832718160327311779315 := by
  unfold tailWord_575848
  simp only [CollatzResearch.WordTrace]
  refine ⟨10501451008904258926852099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14001934678539011902469465 10501451008904258926852099)
  ·
    refine ⟨15752176513356388390278149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10501451008904258926852099 15752176513356388390278149)
    ·
      refine ⟨2953533096254322823177153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15752176513356388390278149 2953533096254322823177153)
      ·
        refine ⟨2215149822190742117382865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2953533096254322823177153 2215149822190742117382865)
        ·
          refine ⟨1661362366643056588037149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2215149822190742117382865 1661362366643056588037149)
          ·
            refine ⟨623010887491146220513931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1661362366643056588037149 623010887491146220513931)
            ·
              refine ⟨934516331236719330770897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623010887491146220513931 934516331236719330770897)
              ·
                refine ⟨700887248427539498078173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 934516331236719330770897 700887248427539498078173)
                ·
                  refine ⟨262832718160327311779315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 700887248427539498078173 262832718160327311779315)
                  ·
                    rfl

theorem cell20_575848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_575848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575848 prefixEnd_575848 := by exact prefixLift 575848
  have htrace : WordTrace (prefixWord ++ tailWord_575848) baseStart_575848 baseEnd_575848 := by
    simpa [prefixWord, tailWord_575848, baseEnd_575848] using wordTrace_append hprefix tailTrace_575848
  have hstable : (prefixWord ++ tailWord_575848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575848).length < 2 ^ (prefixWord ++ tailWord_575848).sum := by decide
  have hdescent : baseEnd_575848 < baseStart_575848 := by decide
  rcases family_descends (prefixWord ++ tailWord_575848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575883 : List Nat := [1, 1, 1, 1, 4, 4, 4, 4]
def baseStart_575883 : Nat := 118140960795 + 575883 * 2 ^ 59
def prefixEnd_575883 : Nat := 4983230072969 + 3 ^ 40 * 575883 * 2
def baseEnd_575883 : Nat := 87616231038007581870835

theorem tailTrace_575883 : CollatzResearch.WordTrace tailWord_575883 prefixEnd_575883 87616231038007581870835 := by
  unfold tailWord_575883
  simp only [CollatzResearch.WordTrace]
  refine ⟨21004178572681718831228303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14002785715121145887485535 21004178572681718831228303)
  ·
    refine ⟨31506267859022578246842455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21004178572681718831228303 31506267859022578246842455)
    ·
      refine ⟨47259401788533867370263683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31506267859022578246842455 47259401788533867370263683)
      ·
        refine ⟨70889102682800801055395525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47259401788533867370263683 70889102682800801055395525)
        ·
          refine ⟨13291706753025150197886661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70889102682800801055395525 13291706753025150197886661)
          ·
            refine ⟨2492195016192215662103749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13291706753025150197886661 2492195016192215662103749)
            ·
              refine ⟨467286565536040436644453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2492195016192215662103749 467286565536040436644453)
              ·
                refine ⟨87616231038007581870835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467286565536040436644453 87616231038007581870835)
                ·
                  rfl

theorem cell20_575883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4].length) (baseStart_575883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575883 prefixEnd_575883 := by exact prefixLift 575883
  have htrace : WordTrace (prefixWord ++ tailWord_575883) baseStart_575883 baseEnd_575883 := by
    simpa [prefixWord, tailWord_575883, baseEnd_575883] using wordTrace_append hprefix tailTrace_575883
  have hstable : (prefixWord ++ tailWord_575883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575883).length < 2 ^ (prefixWord ++ tailWord_575883).sum := by decide
  have hdescent : baseEnd_575883 < baseStart_575883 := by decide
  rcases family_descends (prefixWord ++ tailWord_575883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575904 : List Nat := [2, 1, 1, 4, 1, 3, 8]
def baseStart_575904 : Nat := 118140960795 + 575904 * 2 ^ 59
def prefixEnd_575904 : Nat := 4983230072969 + 3 ^ 40 * 575904 * 2
def baseEnd_575904 : Nat := 29206475342915556212491

theorem tailTrace_575904 : CollatzResearch.WordTrace tailWord_575904 prefixEnd_575904 29206475342915556212491 := by
  unfold tailWord_575904
  simp only [CollatzResearch.WordTrace]
  refine ⟨10502472252802819708871383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14003296337070426278495177 10502472252802819708871383)
  ·
    refine ⟨15753708379204229563307075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10502472252802819708871383 15753708379204229563307075)
    ·
      refine ⟨23630562568806344344960613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15753708379204229563307075 23630562568806344344960613)
      ·
        refine ⟨4430730481651189564680115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23630562568806344344960613 4430730481651189564680115)
        ·
          refine ⟨6646095722476784347020173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4430730481651189564680115 6646095722476784347020173)
          ·
            refine ⟨2492285895928794130132565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6646095722476784347020173 2492285895928794130132565)
            ·
              refine ⟨29206475342915556212491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2492285895928794130132565 29206475342915556212491)
              ·
                rfl

theorem cell20_575904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 8].length) (baseStart_575904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575904 prefixEnd_575904 := by exact prefixLift 575904
  have htrace : WordTrace (prefixWord ++ tailWord_575904) baseStart_575904 baseEnd_575904 := by
    simpa [prefixWord, tailWord_575904, baseEnd_575904] using wordTrace_append hprefix tailTrace_575904
  have hstable : (prefixWord ++ tailWord_575904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575904).length < 2 ^ (prefixWord ++ tailWord_575904).sum := by decide
  have hdescent : baseEnd_575904 < baseStart_575904 := by decide
  rcases family_descends (prefixWord ++ tailWord_575904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575921 : List Nat := [1, 2, 2, 4, 1, 3, 2, 5]
def baseStart_575921 : Nat := 118140960795 + 575921 * 2 ^ 59
def prefixEnd_575921 : Nat := 4983230072969 + 3 ^ 40 * 575921 * 2
def baseEnd_575921 : Nat := 87622012449821167448561

theorem tailTrace_575921 : CollatzResearch.WordTrace tailWord_575921 prefixEnd_575921 87622012449821167448561 := by
  unfold tailWord_575921
  simp only [CollatzResearch.WordTrace]
  refine ⟨21005564546544051321111617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14003709697696034214074411 21005564546544051321111617)
  ·
    refine ⟨15754173409908038490833713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21005564546544051321111617 15754173409908038490833713)
    ·
      refine ⟨11815630057431028868125285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15754173409908038490833713 11815630057431028868125285)
      ·
        refine ⟨2215430635768317912773491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11815630057431028868125285 2215430635768317912773491)
        ·
          refine ⟨3323145953652476869160237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2215430635768317912773491 3323145953652476869160237)
          ·
            refine ⟨1246179732619678825935089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3323145953652476869160237 1246179732619678825935089)
            ·
              refine ⟨934634799464759119451317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246179732619678825935089 934634799464759119451317)
              ·
                refine ⟨87622012449821167448561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 934634799464759119451317 87622012449821167448561)
                ·
                  rfl

theorem cell20_575921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_575921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575921 prefixEnd_575921 := by exact prefixLift 575921
  have htrace : WordTrace (prefixWord ++ tailWord_575921) baseStart_575921 baseEnd_575921 := by
    simpa [prefixWord, tailWord_575921, baseEnd_575921] using wordTrace_append hprefix tailTrace_575921
  have hstable : (prefixWord ++ tailWord_575921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575921).length < 2 ^ (prefixWord ++ tailWord_575921).sum := by decide
  have hdescent : baseEnd_575921 < baseStart_575921 := by decide
  rcases family_descends (prefixWord ++ tailWord_575921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575990 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_575990 : Nat := 118140960795 + 575990 * 2 ^ 59
def prefixEnd_575990 : Nat := 4983230072969 + 3 ^ 40 * 575990 * 2
def baseEnd_575990 : Nat := 262897530829605929045401

theorem tailTrace_575990 : CollatzResearch.WordTrace tailWord_575990 prefixEnd_575990 262897530829605929045401 := by
  unfold tailWord_575990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313005073955879756585839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14005387455529384070248949 1313005073955879756585839)
  ·
    refine ⟨1969507610933819634878759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1313005073955879756585839 1969507610933819634878759)
    ·
      refine ⟨2954261416400729452318139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1969507610933819634878759 2954261416400729452318139)
      ·
        refine ⟨4431392124601094178477209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954261416400729452318139 4431392124601094178477209)
        ·
          refine ⟨3323544093450820633857907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4431392124601094178477209 3323544093450820633857907)
          ·
            refine ⟨4985316140176230950786861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323544093450820633857907 4985316140176230950786861)
            ·
              refine ⟨1869493552566086606545073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4985316140176230950786861 1869493552566086606545073)
              ·
                refine ⟨1402120164424564954908805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869493552566086606545073 1402120164424564954908805)
                ·
                  refine ⟨262897530829605929045401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402120164424564954908805 262897530829605929045401)
                  ·
                    rfl

theorem cell20_575990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_575990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575990 prefixEnd_575990 := by exact prefixLift 575990
  have htrace : WordTrace (prefixWord ++ tailWord_575990) baseStart_575990 baseEnd_575990 := by
    simpa [prefixWord, tailWord_575990, baseEnd_575990] using wordTrace_append hprefix tailTrace_575990
  have hstable : (prefixWord ++ tailWord_575990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575990).length < 2 ^ (prefixWord ++ tailWord_575990).sum := by decide
  have hdescent : baseEnd_575990 < baseStart_575990 := by decide
  rcases family_descends (prefixWord ++ tailWord_575990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_575997 : List Nat := [1, 4, 1, 1, 1, 3, 5, 4]
def baseStart_575997 : Nat := 118140960795 + 575997 * 2 ^ 59
def prefixEnd_575997 : Nat := 4983230072969 + 3 ^ 40 * 575997 * 2
def baseEnd_575997 : Nat := 87633575273448338604013

theorem tailTrace_575997 : CollatzResearch.WordTrace tailWord_575997 prefixEnd_575997 87633575273448338604013 := by
  unfold tailWord_575997
  simp only [CollatzResearch.WordTrace]
  refine ⟨21008336494268716300878245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14005557662845810867252163 21008336494268716300878245)
  ·
    refine ⟨3939063092675384306414671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21008336494268716300878245 3939063092675384306414671)
    ·
      refine ⟨5908594639013076459622007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3939063092675384306414671 5908594639013076459622007)
      ·
        refine ⟨8862891958519614689433011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5908594639013076459622007 8862891958519614689433011)
        ·
          refine ⟨13294337937779422034149517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8862891958519614689433011 13294337937779422034149517)
          ·
            refine ⟨4985376726667283262806069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13294337937779422034149517 4985376726667283262806069)
            ·
              refine ⟨467379068125057805888069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4985376726667283262806069 467379068125057805888069)
              ·
                refine ⟨87633575273448338604013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467379068125057805888069 87633575273448338604013)
                ·
                  rfl

theorem cell20_575997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 4].length) (baseStart_575997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_575997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_575997 prefixEnd_575997 := by exact prefixLift 575997
  have htrace : WordTrace (prefixWord ++ tailWord_575997) baseStart_575997 baseEnd_575997 := by
    simpa [prefixWord, tailWord_575997, baseEnd_575997] using wordTrace_append hprefix tailTrace_575997
  have hstable : (prefixWord ++ tailWord_575997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_575997).length < 2 ^ (prefixWord ++ tailWord_575997).sum := by decide
  have hdescent : baseEnd_575997 < baseStart_575997 := by decide
  rcases family_descends (prefixWord ++ tailWord_575997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576025 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 5]
def baseStart_576025 : Nat := 118140960795 + 576025 * 2 ^ 59
def prefixEnd_576025 : Nat := 4983230072969 + 3 ^ 40 * 576025 * 2
def baseEnd_576025 : Nat := 262913505783301362878591

theorem tailTrace_576025 : CollatzResearch.WordTrace tailWord_576025 prefixEnd_576025 262913505783301362878591 := by
  unfold tailWord_576025
  simp only [CollatzResearch.WordTrace]
  refine ⟨21009357738167277082897529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14006238492111518055265019 21009357738167277082897529)
  ·
    refine ⟨15757018303625457812173147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21009357738167277082897529 15757018303625457812173147)
    ·
      refine ⟨23635527455438186718259721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15757018303625457812173147 23635527455438186718259721)
      ·
        refine ⟨17726645591578640038694791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23635527455438186718259721 17726645591578640038694791)
        ·
          refine ⟨26589968387367960058042187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17726645591578640038694791 26589968387367960058042187)
          ·
            refine ⟨39884952581051940087063281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26589968387367960058042187 39884952581051940087063281)
            ·
              refine ⟨29913714435788955065297461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39884952581051940087063281 29913714435788955065297461)
              ·
                refine ⟨2804410728355214537371637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29913714435788955065297461 2804410728355214537371637)
                ·
                  refine ⟨262913505783301362878591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2804410728355214537371637 262913505783301362878591)
                  ·
                    rfl

theorem cell20_576025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_576025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576025 prefixEnd_576025 := by exact prefixLift 576025
  have htrace : WordTrace (prefixWord ++ tailWord_576025) baseStart_576025 baseEnd_576025 := by
    simpa [prefixWord, tailWord_576025, baseEnd_576025] using wordTrace_append hprefix tailTrace_576025
  have hstable : (prefixWord ++ tailWord_576025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576025).length < 2 ^ (prefixWord ++ tailWord_576025).sum := by decide
  have hdescent : baseEnd_576025 < baseStart_576025 := by decide
  rcases family_descends (prefixWord ++ tailWord_576025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576028 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_576028 : Nat := 118140960795 + 576028 * 2 ^ 59
def prefixEnd_576028 : Nat := 4983230072969 + 3 ^ 40 * 576028 * 2
def baseEnd_576028 : Nat := 262914875065046685778579

theorem tailTrace_576028 : CollatzResearch.WordTrace tailWord_576028 prefixEnd_576028 262914875065046685778579 := by
  unfold tailWord_576028
  simp only [CollatzResearch.WordTrace]
  refine ⟨10504733578578204297628369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14006311438104272396837825 10504733578578204297628369)
  ·
    refine ⟨7878550183933653223221277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10504733578578204297628369 7878550183933653223221277)
    ·
      refine ⟨2954456318975119958707979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7878550183933653223221277 2954456318975119958707979)
      ·
        refine ⟨4431684478462679938061969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954456318975119958707979 4431684478462679938061969)
        ·
          refine ⟨3323763358847009953546477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4431684478462679938061969 3323763358847009953546477)
          ·
            refine ⟨1246411259567628732579929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3323763358847009953546477 1246411259567628732579929)
            ·
              refine ⟨934808444675721549434947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246411259567628732579929 934808444675721549434947)
              ·
                refine ⟨1402212667013582324152421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 934808444675721549434947 1402212667013582324152421)
                ·
                  refine ⟨262914875065046685778579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402212667013582324152421 262914875065046685778579)
                  ·
                    rfl

theorem cell20_576028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_576028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576028 prefixEnd_576028 := by exact prefixLift 576028
  have htrace : WordTrace (prefixWord ++ tailWord_576028) baseStart_576028 baseEnd_576028 := by
    simpa [prefixWord, tailWord_576028, baseEnd_576028] using wordTrace_append hprefix tailTrace_576028
  have hstable : (prefixWord ++ tailWord_576028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576028).length < 2 ^ (prefixWord ++ tailWord_576028).sum := by decide
  have hdescent : baseEnd_576028 < baseStart_576028 := by decide
  rcases family_descends (prefixWord ++ tailWord_576028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576049 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 4]
def baseStart_576049 : Nat := 118140960795 + 576049 * 2 ^ 59
def prefixEnd_576049 : Nat := 4983230072969 + 3 ^ 40 * 576049 * 2
def baseEnd_576049 : Nat := 262924460037263946078493

theorem tailTrace_576049 : CollatzResearch.WordTrace tailWord_576049 prefixEnd_576049 262924460037263946078493 := by
  unfold tailWord_576049
  simp only [CollatzResearch.WordTrace]
  refine ⟨21010233090080329181771201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14006822060053552787847467 21010233090080329181771201)
  ·
    refine ⟨15757674817560246886328401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21010233090080329181771201 15757674817560246886328401)
    ·
      refine ⟨11818256113170185164746301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15757674817560246886328401 11818256113170185164746301)
      ·
        refine ⟨4431846042438819436779863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11818256113170185164746301 4431846042438819436779863)
        ·
          refine ⟨6647769063658229155169795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4431846042438819436779863 6647769063658229155169795)
          ·
            refine ⟨9971653595487343732754693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6647769063658229155169795 9971653595487343732754693)
            ·
              refine ⟨1869685049153876949891505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9971653595487343732754693 1869685049153876949891505)
              ·
                refine ⟨1402263786865407712418629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1869685049153876949891505 1402263786865407712418629)
                ·
                  refine ⟨262924460037263946078493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1402263786865407712418629 262924460037263946078493)
                  ·
                    rfl

theorem cell20_576049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_576049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576049 prefixEnd_576049 := by exact prefixLift 576049
  have htrace : WordTrace (prefixWord ++ tailWord_576049) baseStart_576049 baseEnd_576049 := by
    simpa [prefixWord, tailWord_576049, baseEnd_576049] using wordTrace_append hprefix tailTrace_576049
  have hstable : (prefixWord ++ tailWord_576049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576049).length < 2 ^ (prefixWord ++ tailWord_576049).sum := by decide
  have hdescent : baseEnd_576049 < baseStart_576049 := by decide
  rcases family_descends (prefixWord ++ tailWord_576049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576056 : List Nat := [2, 1, 2, 1, 4, 1, 3, 6]
def baseStart_576056 : Nat := 118140960795 + 576056 * 2 ^ 59
def prefixEnd_576056 : Nat := 4983230072969 + 3 ^ 40 * 576056 * 2
def baseEnd_576056 : Nat := 87642551676001010948377

theorem tailTrace_576056 : CollatzResearch.WordTrace tailWord_576056 prefixEnd_576056 87642551676001010948377 := by
  unfold tailWord_576056
  simp only [CollatzResearch.WordTrace]
  refine ⟨10505244200527484688638011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14006992267369979584850681 10505244200527484688638011)
  ·
    refine ⟨15757866300791227032957017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10505244200527484688638011 15757866300791227032957017)
    ·
      refine ⟨11818399725593420274717763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15757866300791227032957017 11818399725593420274717763)
      ·
        refine ⟨17727599588390130412076645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11818399725593420274717763 17727599588390130412076645)
        ·
          refine ⟨3323924922823149452264371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17727599588390130412076645 3323924922823149452264371)
          ·
            refine ⟨4985887384234724178396557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3323924922823149452264371 4985887384234724178396557)
            ·
              refine ⟨1869707769088021566898709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4985887384234724178396557 1869707769088021566898709)
              ·
                refine ⟨87642551676001010948377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1869707769088021566898709 87642551676001010948377)
                ·
                  rfl

theorem cell20_576056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_576056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576056 prefixEnd_576056 := by exact prefixLift 576056
  have htrace : WordTrace (prefixWord ++ tailWord_576056) baseStart_576056 baseEnd_576056 := by
    simpa [prefixWord, tailWord_576056, baseEnd_576056] using wordTrace_append hprefix tailTrace_576056
  have hstable : (prefixWord ++ tailWord_576056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576056).length < 2 ^ (prefixWord ++ tailWord_576056).sum := by decide
  have hdescent : baseEnd_576056 < baseStart_576056 := by decide
  rcases family_descends (prefixWord ++ tailWord_576056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576063 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 7]
def baseStart_576063 : Nat := 118140960795 + 576063 * 2 ^ 59
def prefixEnd_576063 : Nat := 4983230072969 + 3 ^ 40 * 576063 * 2
def baseEnd_576063 : Nat := 262930850018742119611769

theorem tailTrace_576063 : CollatzResearch.WordTrace tailWord_576063 prefixEnd_576063 262930850018742119611769 := by
  unfold tailWord_576063
  simp only [CollatzResearch.WordTrace]
  refine ⟨21010743712029609572780843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14007162474686406381853895 21010743712029609572780843)
  ·
    refine ⟨31516115568044414359171265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21010743712029609572780843 31516115568044414359171265)
    ·
      refine ⟨23637086676033310769378449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31516115568044414359171265 23637086676033310769378449)
      ·
        refine ⟨17727815007024983077033837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23637086676033310769378449 17727815007024983077033837)
        ·
          refine ⟨6647930627634368653887689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17727815007024983077033837 6647930627634368653887689)
          ·
            refine ⟨4985947970725776490415767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6647930627634368653887689 4985947970725776490415767)
            ·
              refine ⟨7478921956088664735623651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4985947970725776490415767 7478921956088664735623651)
              ·
                refine ⟨11218382934132997103435477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7478921956088664735623651 11218382934132997103435477)
                ·
                  refine ⟨262930850018742119611769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11218382934132997103435477 262930850018742119611769)
                  ·
                    rfl

theorem cell20_576063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_576063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576063 prefixEnd_576063 := by exact prefixLift 576063
  have htrace : WordTrace (prefixWord ++ tailWord_576063) baseStart_576063 baseEnd_576063 := by
    simpa [prefixWord, tailWord_576063, baseEnd_576063] using wordTrace_append hprefix tailTrace_576063
  have hstable : (prefixWord ++ tailWord_576063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576063).length < 2 ^ (prefixWord ++ tailWord_576063).sum := by decide
  have hdescent : baseEnd_576063 < baseStart_576063 := by decide
  rcases family_descends (prefixWord ++ tailWord_576063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576097 : List Nat := [1, 2, 3, 1, 1, 4, 4, 1, 3]
def baseStart_576097 : Nat := 118140960795 + 576097 * 2 ^ 59
def prefixEnd_576097 : Nat := 4983230072969 + 3 ^ 40 * 576097 * 2
def baseEnd_576097 : Nat := 262946368545189112478297

theorem tailTrace_576097 : CollatzResearch.WordTrace tailWord_576097 prefixEnd_576097 262946368545189112478297 := by
  unfold tailWord_576097
  simp only [CollatzResearch.WordTrace]
  refine ⟨21011983793906433379518545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14007989195937622253012363 21011983793906433379518545)
  ·
    refine ⟨15758987845429825034638909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21011983793906433379518545 15758987845429825034638909)
    ·
      refine ⟨5909620442036184387989591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15758987845429825034638909 5909620442036184387989591)
      ·
        refine ⟨8864430663054276581984387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5909620442036184387989591 8864430663054276581984387)
        ·
          refine ⟨13296645994581414872976581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8864430663054276581984387 13296645994581414872976581)
          ·
            refine ⟨2493121123984015288683109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13296645994581414872976581 2493121123984015288683109)
            ·
              refine ⟨467460210747002866628083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2493121123984015288683109 467460210747002866628083)
              ·
                refine ⟨701190316120504299942125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 467460210747002866628083 701190316120504299942125)
                ·
                  refine ⟨262946368545189112478297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701190316120504299942125 262946368545189112478297)
                  ·
                    rfl

theorem cell20_576097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_576097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576097 prefixEnd_576097 := by exact prefixLift 576097
  have htrace : WordTrace (prefixWord ++ tailWord_576097) baseStart_576097 baseEnd_576097 := by
    simpa [prefixWord, tailWord_576097, baseEnd_576097] using wordTrace_append hprefix tailTrace_576097
  have hstable : (prefixWord ++ tailWord_576097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576097).length < 2 ^ (prefixWord ++ tailWord_576097).sum := by decide
  have hdescent : baseEnd_576097 < baseStart_576097 := by decide
  rcases family_descends (prefixWord ++ tailWord_576097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576130 : List Nat := [3, 4, 3, 1, 2, 1, 2, 2, 2]
def baseStart_576130 : Nat := 118140960795 + 576130 * 2 ^ 59
def prefixEnd_576130 : Nat := 4983230072969 + 3 ^ 40 * 576130 * 2
def baseEnd_576130 : Nat := 262961430644387664378163

theorem tailTrace_576130 : CollatzResearch.WordTrace tailWord_576130 prefixEnd_576130 262961430644387664378163 := by
  unfold tailWord_576130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5253296850696720003867461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14008791601857920010313229 5253296850696720003867461)
  ·
    refine ⟨984993159505635000725149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5253296850696720003867461 984993159505635000725149)
    ·
      refine ⟨369372434814613125271931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 984993159505635000725149 369372434814613125271931)
      ·
        refine ⟨554058652221919687907897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 369372434814613125271931 554058652221919687907897)
        ·
          refine ⟨415543989166439765930923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 554058652221919687907897 415543989166439765930923)
          ·
            refine ⟨623315983749659648896385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 415543989166439765930923 623315983749659648896385)
            ·
              refine ⟨467486987812244736672289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623315983749659648896385 467486987812244736672289)
              ·
                refine ⟨350615240859183552504217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 467486987812244736672289 350615240859183552504217)
                ·
                  refine ⟨262961430644387664378163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350615240859183552504217 262961430644387664378163)
                  ·
                    rfl

theorem cell20_576130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_576130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576130 prefixEnd_576130 := by exact prefixLift 576130
  have htrace : WordTrace (prefixWord ++ tailWord_576130) baseStart_576130 baseEnd_576130 := by
    simpa [prefixWord, tailWord_576130, baseEnd_576130] using wordTrace_append hprefix tailTrace_576130
  have hstable : (prefixWord ++ tailWord_576130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576130).length < 2 ^ (prefixWord ++ tailWord_576130).sum := by decide
  have hdescent : baseEnd_576130 < baseStart_576130 := by decide
  rcases family_descends (prefixWord ++ tailWord_576130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576132 : List Nat := [2, 3, 2, 1, 3, 9]
def baseStart_576132 : Nat := 118140960795 + 576132 * 2 ^ 59
def prefixEnd_576132 : Nat := 4983230072969 + 3 ^ 40 * 576132 * 2
def baseEnd_576132 : Nat := 9739346055514242455981

theorem tailTrace_576132 : CollatzResearch.WordTrace tailWord_576132 prefixEnd_576132 9739346055514242455981 := by
  unfold tailWord_576132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10506630174389817178521325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14008840232519756238028433 10506630174389817178521325)
  ·
    refine ⟨3939986315396181441945497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10506630174389817178521325 3939986315396181441945497)
    ·
      refine ⟨2954989736547136081459123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3939986315396181441945497 2954989736547136081459123)
      ·
        refine ⟨4432484604820704122188685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2954989736547136081459123 4432484604820704122188685)
        ·
          refine ⟨1662181726807764045820757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4432484604820704122188685 1662181726807764045820757)
          ·
            refine ⟨9739346055514242455981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1662181726807764045820757 9739346055514242455981)
            ·
              rfl

theorem cell20_576132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 9].length) (baseStart_576132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576132 prefixEnd_576132 := by exact prefixLift 576132
  have htrace : WordTrace (prefixWord ++ tailWord_576132) baseStart_576132 baseEnd_576132 := by
    simpa [prefixWord, tailWord_576132, baseEnd_576132] using wordTrace_append hprefix tailTrace_576132
  have hstable : (prefixWord ++ tailWord_576132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576132).length < 2 ^ (prefixWord ++ tailWord_576132).sum := by decide
  have hdescent : baseEnd_576132 < baseStart_576132 := by decide
  rcases family_descends (prefixWord ++ tailWord_576132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576225 : List Nat := [1, 2, 3, 1, 4, 1, 4, 4]
def baseStart_576225 : Nat := 118140960795 + 576225 * 2 ^ 59
def prefixEnd_576225 : Nat := 4983230072969 + 3 ^ 40 * 576225 * 2
def baseEnd_576225 : Nat := 87668263744329852070369

theorem tailTrace_576225 : CollatzResearch.WordTrace tailWord_576225 prefixEnd_576225 87668263744329852070369 := by
  unfold tailWord_576225
  simp only [CollatzResearch.WordTrace]
  refine ⟨21016652337442711240178129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14011101558295140826785419 21016652337442711240178129)
  ·
    refine ⟨15762489253082033430133597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21016652337442711240178129 15762489253082033430133597)
    ·
      refine ⟨5910933469905762536300099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15762489253082033430133597 5910933469905762536300099)
      ·
        refine ⟨8866400204858643804450149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5910933469905762536300099 8866400204858643804450149)
        ·
          refine ⟨1662450038410995713334403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8866400204858643804450149 1662450038410995713334403)
          ·
            refine ⟨2493675057616493570001605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662450038410995713334403 2493675057616493570001605)
            ·
              refine ⟨467564073303092544375301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2493675057616493570001605 467564073303092544375301)
              ·
                refine ⟨87668263744329852070369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467564073303092544375301 87668263744329852070369)
                ·
                  rfl

theorem cell20_576225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 4].length) (baseStart_576225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576225 prefixEnd_576225 := by exact prefixLift 576225
  have htrace : WordTrace (prefixWord ++ tailWord_576225) baseStart_576225 baseEnd_576225 := by
    simpa [prefixWord, tailWord_576225, baseEnd_576225] using wordTrace_append hprefix tailTrace_576225
  have hstable : (prefixWord ++ tailWord_576225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576225).length < 2 ^ (prefixWord ++ tailWord_576225).sum := by decide
  have hdescent : baseEnd_576225 < baseStart_576225 := by decide
  rcases family_descends (prefixWord ++ tailWord_576225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576253 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_576253 : Nat := 118140960795 + 576253 * 2 ^ 59
def prefixEnd_576253 : Nat := 4983230072969 + 3 ^ 40 * 576253 * 2
def baseEnd_576253 : Nat := 263017571195945903277659

theorem tailTrace_576253 : CollatzResearch.WordTrace tailWord_576253 prefixEnd_576253 263017571195945903277659 := by
  unfold tailWord_576253
  simp only [CollatzResearch.WordTrace]
  refine ⟨21017673581341272022197413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14011782387560848014798275 21017673581341272022197413)
  ·
    refine ⟨3940813796501488504162015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21017673581341272022197413 3940813796501488504162015)
    ·
      refine ⟨5911220694752232756243023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3940813796501488504162015 5911220694752232756243023)
      ·
        refine ⟨8866831042128349134364535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5911220694752232756243023 8866831042128349134364535)
        ·
          refine ⟨13300246563192523701546803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8866831042128349134364535 13300246563192523701546803)
          ·
            refine ⟨19950369844788785552320205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13300246563192523701546803 19950369844788785552320205)
            ·
              refine ⟨7481388691795794582120077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19950369844788785552320205 7481388691795794582120077)
              ·
                refine ⟨2805520759423422968295029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7481388691795794582120077 2805520759423422968295029)
                ·
                  refine ⟨263017571195945903277659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2805520759423422968295029 263017571195945903277659)
                  ·
                    rfl

theorem cell20_576253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_576253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576253 prefixEnd_576253 := by exact prefixLift 576253
  have htrace : WordTrace (prefixWord ++ tailWord_576253) baseStart_576253 baseEnd_576253 := by
    simpa [prefixWord, tailWord_576253, baseEnd_576253] using wordTrace_append hprefix tailTrace_576253
  have hstable : (prefixWord ++ tailWord_576253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576253).length < 2 ^ (prefixWord ++ tailWord_576253).sum := by decide
  have hdescent : baseEnd_576253 < baseStart_576253 := by decide
  rcases family_descends (prefixWord ++ tailWord_576253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576263 : List Nat := [1, 1, 4, 4, 1, 2, 2, 5]
def baseStart_576263 : Nat := 118140960795 + 576263 * 2 ^ 59
def prefixEnd_576263 : Nat := 4983230072969 + 3 ^ 40 * 576263 * 2
def baseEnd_576263 : Nat := 87674045156143437648095

theorem tailTrace_576263 : CollatzResearch.WordTrace tailWord_576263 prefixEnd_576263 87674045156143437648095 := by
  unfold tailWord_576263
  simp only [CollatzResearch.WordTrace]
  refine ⟨21018038311305043730061443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14012025540870029153374295 21018038311305043730061443)
  ·
    refine ⟨31527057466957565595092165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21018038311305043730061443 31527057466957565595092165)
    ·
      refine ⟨5911323275054543549079781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31527057466957565595092165 5911323275054543549079781)
      ·
        refine ⟨1108373114072726915452459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5911323275054543549079781 1108373114072726915452459)
        ·
          refine ⟨1662559671109090373178689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108373114072726915452459 1662559671109090373178689)
          ·
            refine ⟨1246919753331817779884017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1662559671109090373178689 1246919753331817779884017)
            ·
              refine ⟨935189814998863334913013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1246919753331817779884017 935189814998863334913013)
              ·
                refine ⟨87674045156143437648095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 935189814998863334913013 87674045156143437648095)
                ·
                  rfl

theorem cell20_576263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_576263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576263 prefixEnd_576263 := by exact prefixLift 576263
  have htrace : WordTrace (prefixWord ++ tailWord_576263) baseStart_576263 baseEnd_576263 := by
    simpa [prefixWord, tailWord_576263, baseEnd_576263] using wordTrace_append hprefix tailTrace_576263
  have hstable : (prefixWord ++ tailWord_576263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576263).length < 2 ^ (prefixWord ++ tailWord_576263).sum := by decide
  have hdescent : baseEnd_576263 < baseStart_576263 := by decide
  rcases family_descends (prefixWord ++ tailWord_576263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576284 : List Nat := [2, 2, 3, 1, 1, 3, 2, 6]
def baseStart_576284 : Nat := 118140960795 + 576284 * 2 ^ 59
def prefixEnd_576284 : Nat := 4983230072969 + 3 ^ 40 * 576284 * 2
def baseEnd_576284 : Nat := 87677240146882524414733

theorem tailTrace_576284 : CollatzResearch.WordTrace tailWord_576284 prefixEnd_576284 87677240146882524414733 := by
  unfold tailWord_576284
  simp only [CollatzResearch.WordTrace]
  refine ⟨10509402122114482158287953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14012536162819309544383937 10509402122114482158287953)
  ·
    refine ⟨7882051591585861618715965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10509402122114482158287953 7882051591585861618715965)
    ·
      refine ⟨2955769346844698107018487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7882051591585861618715965 2955769346844698107018487)
      ·
        refine ⟨4433654020267047160527731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2955769346844698107018487 4433654020267047160527731)
        ·
          refine ⟨6650481030400570740791597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4433654020267047160527731 6650481030400570740791597)
          ·
            refine ⟨2493930386400214027796849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6650481030400570740791597 2493930386400214027796849)
            ·
              refine ⟨1870447789800160520847637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2493930386400214027796849 1870447789800160520847637)
              ·
                refine ⟨87677240146882524414733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1870447789800160520847637 87677240146882524414733)
                ·
                  rfl

theorem cell20_576284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_576284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576284 prefixEnd_576284 := by exact prefixLift 576284
  have htrace : WordTrace (prefixWord ++ tailWord_576284) baseStart_576284 baseEnd_576284 := by
    simpa [prefixWord, tailWord_576284, baseEnd_576284] using wordTrace_append hprefix tailTrace_576284
  have hstable : (prefixWord ++ tailWord_576284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576284).length < 2 ^ (prefixWord ++ tailWord_576284).sum := by decide
  have hdescent : baseEnd_576284 < baseStart_576284 := by decide
  rcases family_descends (prefixWord ++ tailWord_576284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576301 : List Nat := [1, 5, 3, 2, 9]
def baseStart_576301 : Nat := 118140960795 + 576301 * 2 ^ 59
def prefixEnd_576301 : Nat := 4983230072969 + 3 ^ 40 * 576301 * 2
def baseEnd_576301 : Nat := 3247400983998408267623

theorem tailTrace_576301 : CollatzResearch.WordTrace tailWord_576301 prefixEnd_576301 3247400983998408267623 := by
  unfold tailWord_576301
  simp only [CollatzResearch.WordTrace]
  refine ⟨21019424285167376219944757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14012949523444917479963171 21019424285167376219944757)
  ·
    refine ⟨1970571026734441520619821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21019424285167376219944757 1970571026734441520619821)
    ·
      refine ⟨738964135025415570232433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1970571026734441520619821 738964135025415570232433)
      ·
        refine ⟨554223101269061677674325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738964135025415570232433 554223101269061677674325)
        ·
          refine ⟨3247400983998408267623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 554223101269061677674325 3247400983998408267623)
          ·
            rfl

theorem cell20_576301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 9].length) (baseStart_576301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576301 prefixEnd_576301 := by exact prefixLift 576301
  have htrace : WordTrace (prefixWord ++ tailWord_576301) baseStart_576301 baseEnd_576301 := by
    simpa [prefixWord, tailWord_576301, baseEnd_576301] using wordTrace_append hprefix tailTrace_576301
  have hstable : (prefixWord ++ tailWord_576301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576301).length < 2 ^ (prefixWord ++ tailWord_576301).sum := by decide
  have hdescent : baseEnd_576301 < baseStart_576301 := by decide
  rcases family_descends (prefixWord ++ tailWord_576301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576318 : List Nat := [4, 2, 1, 2, 3, 2, 1, 5]
def baseStart_576318 : Nat := 118140960795 + 576318 * 2 ^ 59
def prefixEnd_576318 : Nat := 4983230072969 + 3 ^ 40 * 576318 * 2
def baseEnd_576318 : Nat := 87682412989031522036909

theorem tailTrace_576318 : CollatzResearch.WordTrace tailWord_576318 prefixEnd_576318 87682412989031522036909 := by
  unfold tailWord_576318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627505540763223515414201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14013362884070525415542405 2627505540763223515414201)
  ·
    refine ⟨1970629155572417636560651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2627505540763223515414201 1970629155572417636560651)
    ·
      refine ⟨2955943733358626454840977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1970629155572417636560651 2955943733358626454840977)
      ·
        refine ⟨2216957800018969841130733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2955943733358626454840977 2216957800018969841130733)
        ·
          refine ⟨831359175007113690424025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2216957800018969841130733 831359175007113690424025)
          ·
            refine ⟨623519381255335267818019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 831359175007113690424025 623519381255335267818019)
            ·
              refine ⟨935279071883002901727029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 623519381255335267818019 935279071883002901727029)
              ·
                refine ⟨87682412989031522036909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 935279071883002901727029 87682412989031522036909)
                ·
                  rfl

theorem cell20_576318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_576318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576318 prefixEnd_576318 := by exact prefixLift 576318
  have htrace : WordTrace (prefixWord ++ tailWord_576318) baseStart_576318 baseEnd_576318 := by
    simpa [prefixWord, tailWord_576318, baseEnd_576318] using wordTrace_append hprefix tailTrace_576318
  have hstable : (prefixWord ++ tailWord_576318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576318).length < 2 ^ (prefixWord ++ tailWord_576318).sum := by decide
  have hdescent : baseEnd_576318 < baseStart_576318 := by decide
  rcases family_descends (prefixWord ++ tailWord_576318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576336 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 6]
def baseStart_576336 : Nat := 118140960795 + 576336 * 2 ^ 59
def prefixEnd_576336 : Nat := 4983230072969 + 3 ^ 40 * 576336 * 2
def baseEnd_576336 : Nat := 263055454657566503510653

theorem tailTrace_576336 : CollatzResearch.WordTrace tailWord_576336 prefixEnd_576336 263055454657566503510653 := by
  unfold tailWord_576336
  simp only [CollatzResearch.WordTrace]
  refine ⟨10510350420020288598734431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14013800560027051464979241 10510350420020288598734431)
  ·
    refine ⟨15765525630030432898101647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10510350420020288598734431 15765525630030432898101647)
    ·
      refine ⟨23648288445045649347152471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15765525630030432898101647 23648288445045649347152471)
      ·
        refine ⟨35472432667568474020728707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23648288445045649347152471 35472432667568474020728707)
        ·
          refine ⟨53208649001352711031093061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35472432667568474020728707 53208649001352711031093061)
          ·
            refine ⟨9976621687753633318329949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53208649001352711031093061 9976621687753633318329949)
            ·
              refine ⟨3741233132907612494373731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9976621687753633318329949 3741233132907612494373731)
              ·
                refine ⟨5611849699361418741560597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3741233132907612494373731 5611849699361418741560597)
                ·
                  refine ⟨263055454657566503510653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5611849699361418741560597 263055454657566503510653)
                  ·
                    rfl

theorem cell20_576336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_576336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576336 prefixEnd_576336 := by exact prefixLift 576336
  have htrace : WordTrace (prefixWord ++ tailWord_576336) baseStart_576336 baseEnd_576336 := by
    simpa [prefixWord, tailWord_576336, baseEnd_576336] using wordTrace_append hprefix tailTrace_576336
  have hstable : (prefixWord ++ tailWord_576336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576336).length < 2 ^ (prefixWord ++ tailWord_576336).sum := by decide
  have hdescent : baseEnd_576336 < baseStart_576336 := by decide
  rcases family_descends (prefixWord ++ tailWord_576336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576360 : List Nat := [2, 1, 4, 2, 1, 3, 7]
def baseStart_576360 : Nat := 118140960795 + 576360 * 2 ^ 59
def prefixEnd_576360 : Nat := 4983230072969 + 3 ^ 40 * 576360 * 2
def baseEnd_576360 : Nat := 29229600990169898523395

theorem tailTrace_576360 : CollatzResearch.WordTrace tailWord_576360 prefixEnd_576360 29229600990169898523395 := by
  unfold tailWord_576360
  simp only [CollatzResearch.WordTrace]
  refine ⟨10510788095976814648171267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14014384127969086197561689 10510788095976814648171267)
  ·
    refine ⟨15766182143965221972256901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10510788095976814648171267 15766182143965221972256901)
    ·
      refine ⟨2956159151993479119798169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15766182143965221972256901 2956159151993479119798169)
      ·
        refine ⟨2217119363995109339848627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2956159151993479119798169 2217119363995109339848627)
        ·
          refine ⟨3325679045992664009772941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217119363995109339848627 3325679045992664009772941)
          ·
            refine ⟨1247129642247249003664853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3325679045992664009772941 1247129642247249003664853)
            ·
              refine ⟨29229600990169898523395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1247129642247249003664853 29229600990169898523395)
              ·
                rfl

theorem cell20_576360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 7].length) (baseStart_576360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576360 prefixEnd_576360 := by exact prefixLift 576360
  have htrace : WordTrace (prefixWord ++ tailWord_576360) baseStart_576360 baseEnd_576360 := by
    simpa [prefixWord, tailWord_576360, baseEnd_576360] using wordTrace_append hprefix tailTrace_576360
  have hstable : (prefixWord ++ tailWord_576360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576360).length < 2 ^ (prefixWord ++ tailWord_576360).sum := by decide
  have hdescent : baseEnd_576360 < baseStart_576360 := by decide
  rcases family_descends (prefixWord ++ tailWord_576360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576370 : List Nat := [3, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_576370 : Nat := 118140960795 + 576370 * 2 ^ 59
def prefixEnd_576370 : Nat := 4983230072969 + 3 ^ 40 * 576370 * 2
def baseEnd_576370 : Nat := 263070973184013496377181

theorem tailTrace_576370 : CollatzResearch.WordTrace tailWord_576370 prefixEnd_576370 263070973184013496377181 := by
  unfold tailWord_576370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255485230479350251051641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14014627281278267336137709 5255485230479350251051641)
  ·
    refine ⟨3941613922859512688288731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5255485230479350251051641 3941613922859512688288731)
    ·
      refine ⟨5912420884289269032433097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3941613922859512688288731 5912420884289269032433097)
      ·
        refine ⟨4434315663216951774324823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5912420884289269032433097 4434315663216951774324823)
        ·
          refine ⟨6651473494825427661487235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4434315663216951774324823 6651473494825427661487235)
          ·
            refine ⟨9977210242238141492230853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6651473494825427661487235 9977210242238141492230853)
            ·
              refine ⟨1870726920419651529793285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9977210242238141492230853 1870726920419651529793285)
              ·
                refine ⟨350761297578684661836241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1870726920419651529793285 350761297578684661836241)
                ·
                  refine ⟨263070973184013496377181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350761297578684661836241 263070973184013496377181)
                  ·
                    rfl

theorem cell20_576370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_576370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576370 prefixEnd_576370 := by exact prefixLift 576370
  have htrace : WordTrace (prefixWord ++ tailWord_576370) baseStart_576370 baseEnd_576370 := by
    simpa [prefixWord, tailWord_576370, baseEnd_576370] using wordTrace_append hprefix tailTrace_576370
  have hstable : (prefixWord ++ tailWord_576370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576370).length < 2 ^ (prefixWord ++ tailWord_576370).sum := by decide
  have hdescent : baseEnd_576370 < baseStart_576370 := by decide
  rcases family_descends (prefixWord ++ tailWord_576370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576391 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_576391 : Nat := 118140960795 + 576391 * 2 ^ 59
def prefixEnd_576391 : Nat := 4983230072969 + 3 ^ 40 * 576391 * 2
def baseEnd_576391 : Nat := 263080558156230756677095

theorem tailTrace_576391 : CollatzResearch.WordTrace tailWord_576391 prefixEnd_576391 263080558156230756677095 := by
  unfold tailWord_576391
  simp only [CollatzResearch.WordTrace]
  refine ⟨21022706854841321590721027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14015137903227547727147351 21022706854841321590721027)
  ·
    refine ⟨31534060282261982386081541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21022706854841321590721027 31534060282261982386081541)
    ·
      refine ⟨5912636302924121697390289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31534060282261982386081541 5912636302924121697390289)
      ·
        refine ⟨4434477227193091273042717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5912636302924121697390289 4434477227193091273042717)
        ·
          refine ⟨1662928960197409227391019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4434477227193091273042717 1662928960197409227391019)
          ·
            refine ⟨2494393440296113841086529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1662928960197409227391019 2494393440296113841086529)
            ·
              refine ⟨1870795080222085380814897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2494393440296113841086529 1870795080222085380814897)
              ·
                refine ⟨1403096310166564035611173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1870795080222085380814897 1403096310166564035611173)
                ·
                  refine ⟨263080558156230756677095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1403096310166564035611173 263080558156230756677095)
                  ·
                    rfl

theorem cell20_576391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_576391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576391 prefixEnd_576391 := by exact prefixLift 576391
  have htrace : WordTrace (prefixWord ++ tailWord_576391) baseStart_576391 baseEnd_576391 := by
    simpa [prefixWord, tailWord_576391, baseEnd_576391] using wordTrace_append hprefix tailTrace_576391
  have hstable : (prefixWord ++ tailWord_576391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576391).length < 2 ^ (prefixWord ++ tailWord_576391).sum := by decide
  have hdescent : baseEnd_576391 < baseStart_576391 := by decide
  rcases family_descends (prefixWord ++ tailWord_576391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576394 : List Nat := [3, 1, 2, 4, 1, 3, 2, 4]
def baseStart_576394 : Nat := 118140960795 + 576394 * 2 ^ 59
def prefixEnd_576394 : Nat := 4983230072969 + 3 ^ 40 * 576394 * 2
def baseEnd_576394 : Nat := 87693975812658693192361

theorem tailTrace_576394 : CollatzResearch.WordTrace tailWord_576394 prefixEnd_576394 87693975812658693192361 := by
  unfold tailWord_576394
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255704068457613275770059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14015210849220302068720157 5255704068457613275770059)
  ·
    refine ⟨7883556102686419913655089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5255704068457613275770059 7883556102686419913655089)
    ·
      refine ⟨5912667077014814935241317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7883556102686419913655089 5912667077014814935241317)
      ·
        refine ⟨1108625076940277800357747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5912667077014814935241317 1108625076940277800357747)
        ·
          refine ⟨1662937615410416700536621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108625076940277800357747 1662937615410416700536621)
          ·
            refine ⟨623601605778906262701233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1662937615410416700536621 623601605778906262701233)
            ·
              refine ⟨467701204334179697025925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 623601605778906262701233 467701204334179697025925)
              ·
                refine ⟨87693975812658693192361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467701204334179697025925 87693975812658693192361)
                ·
                  rfl

theorem cell20_576394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_576394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576394 prefixEnd_576394 := by exact prefixLift 576394
  have htrace : WordTrace (prefixWord ++ tailWord_576394) baseStart_576394 baseEnd_576394 := by
    simpa [prefixWord, tailWord_576394, baseEnd_576394] using wordTrace_append hprefix tailTrace_576394
  have hstable : (prefixWord ++ tailWord_576394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576394).length < 2 ^ (prefixWord ++ tailWord_576394).sum := by decide
  have hdescent : baseEnd_576394 < baseStart_576394 := by decide
  rcases family_descends (prefixWord ++ tailWord_576394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576405 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 5]
def baseStart_576405 : Nat := 118140960795 + 576405 * 2 ^ 59
def prefixEnd_576405 : Nat := 4983230072969 + 3 ^ 40 * 576405 * 2
def baseEnd_576405 : Nat := 263086948137708930210371

theorem tailTrace_576405 : CollatzResearch.WordTrace tailWord_576405 prefixEnd_576405 263086948137708930210371 := by
  unfold tailWord_576405
  simp only [CollatzResearch.WordTrace]
  refine ⟨21023217476790601981730669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14015478317860401321153779 21023217476790601981730669)
  ·
    refine ⟨7883706553796475743149001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21023217476790601981730669 7883706553796475743149001)
    ·
      refine ⟨5912779915347356807361751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7883706553796475743149001 5912779915347356807361751)
      ·
        refine ⟨8869169873021035211042627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5912779915347356807361751 8869169873021035211042627)
        ·
          refine ⟨13303754809531552816563941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8869169873021035211042627 13303754809531552816563941)
          ·
            refine ⟨2494454026787166153105739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13303754809531552816563941 2494454026787166153105739)
            ·
              refine ⟨3741681040180749229658609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494454026787166153105739 3741681040180749229658609)
              ·
                refine ⟨2806260780135561922243957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3741681040180749229658609 2806260780135561922243957)
                ·
                  refine ⟨263086948137708930210371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2806260780135561922243957 263086948137708930210371)
                  ·
                    rfl

theorem cell20_576405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_576405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576405 prefixEnd_576405 := by exact prefixLift 576405
  have htrace : WordTrace (prefixWord ++ tailWord_576405) baseStart_576405 baseEnd_576405 := by
    simpa [prefixWord, tailWord_576405, baseEnd_576405] using wordTrace_append hprefix tailTrace_576405
  have hstable : (prefixWord ++ tailWord_576405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576405).length < 2 ^ (prefixWord ++ tailWord_576405).sum := by decide
  have hdescent : baseEnd_576405 < baseStart_576405 := by decide
  rcases family_descends (prefixWord ++ tailWord_576405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576419 : List Nat := [1, 1, 1, 4, 1, 2, 10]
def baseStart_576419 : Nat := 118140960795 + 576419 * 2 ^ 59
def prefixEnd_576419 : Nat := 4983230072969 + 3 ^ 40 * 576419 * 2
def baseEnd_576419 : Nat := 29232593124354122638183

theorem tailTrace_576419 : CollatzResearch.WordTrace tailWord_576419 prefixEnd_576419 29232593124354122638183 := by
  unfold tailWord_576419
  simp only [CollatzResearch.WordTrace]
  refine ⟨21023728098739882372740311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14015818732493254915160207 21023728098739882372740311)
  ·
    refine ⟨31535592148109823559110467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21023728098739882372740311 31535592148109823559110467)
    ·
      refine ⟨47303388222164735338665701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31535592148109823559110467 47303388222164735338665701)
      ·
        refine ⟨8869385291655887875999819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47303388222164735338665701 8869385291655887875999819)
        ·
          refine ⟨13304077937483831813999729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8869385291655887875999819 13304077937483831813999729)
          ·
            refine ⟨9978058453112873860499797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13304077937483831813999729 9978058453112873860499797)
            ·
              refine ⟨29232593124354122638183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9978058453112873860499797 29232593124354122638183)
              ·
                rfl

theorem cell20_576419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_576419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576419 prefixEnd_576419 := by exact prefixLift 576419
  have htrace : WordTrace (prefixWord ++ tailWord_576419) baseStart_576419 baseEnd_576419 := by
    simpa [prefixWord, tailWord_576419, baseEnd_576419] using wordTrace_append hprefix tailTrace_576419
  have hstable : (prefixWord ++ tailWord_576419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576419).length < 2 ^ (prefixWord ++ tailWord_576419).sum := by decide
  have hdescent : baseEnd_576419 < baseStart_576419 := by decide
  rcases family_descends (prefixWord ++ tailWord_576419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576477 : List Nat := [1, 4, 3, 1, 2, 2, 2, 2, 3]
def baseStart_576477 : Nat := 118140960795 + 576477 * 2 ^ 59
def prefixEnd_576477 : Nat := 4983230072969 + 3 ^ 40 * 576477 * 2
def baseEnd_576477 : Nat := 263119810899596679810077

theorem tailTrace_576477 : CollatzResearch.WordTrace tailWord_576477 prefixEnd_576477 263119810899596679810077 := by
  unfold tailWord_576477
  simp only [CollatzResearch.WordTrace]
  refine ⟨21025843532529758278351685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14017229021686505518901123 21025843532529758278351685)
  ·
    refine ⟨3942345662349329677190941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21025843532529758278351685 3942345662349329677190941)
    ·
      refine ⟨1478379623380998628946603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3942345662349329677190941 1478379623380998628946603)
      ·
        refine ⟨2217569435071497943419905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1478379623380998628946603 2217569435071497943419905)
        ·
          refine ⟨1663177076303623457564929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2217569435071497943419905 1663177076303623457564929)
          ·
            refine ⟨1247382807227717593173697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663177076303623457564929 1247382807227717593173697)
            ·
              refine ⟨935537105420788194880273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247382807227717593173697 935537105420788194880273)
              ·
                refine ⟨701652829065591146160205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935537105420788194880273 701652829065591146160205)
                ·
                  refine ⟨263119810899596679810077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701652829065591146160205 263119810899596679810077)
                  ·
                    rfl

theorem cell20_576477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_576477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576477 prefixEnd_576477 := by exact prefixLift 576477
  have htrace : WordTrace (prefixWord ++ tailWord_576477) baseStart_576477 baseEnd_576477 := by
    simpa [prefixWord, tailWord_576477, baseEnd_576477] using wordTrace_append hprefix tailTrace_576477
  have hstable : (prefixWord ++ tailWord_576477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576477).length < 2 ^ (prefixWord ++ tailWord_576477).sum := by decide
  have hdescent : baseEnd_576477 < baseStart_576477 := by decide
  rcases family_descends (prefixWord ++ tailWord_576477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576501 : List Nat := [1, 3, 5, 2, 1, 1, 1, 2, 4]
def baseStart_576501 : Nat := 118140960795 + 576501 * 2 ^ 59
def prefixEnd_576501 : Nat := 4983230072969 + 3 ^ 40 * 576501 * 2
def baseEnd_576501 : Nat := 263130765153559263009979

theorem tailTrace_576501 : CollatzResearch.WordTrace tailWord_576501 prefixEnd_576501 263130765153559263009979 := by
  unfold tailWord_576501
  simp only [CollatzResearch.WordTrace]
  refine ⟨21026718884442810377225357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14017812589628540251483571 21026718884442810377225357)
  ·
    refine ⟨7885019581666053891459509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21026718884442810377225357 7885019581666053891459509)
    ·
      refine ⟨739220585781192552324329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7885019581666053891459509 739220585781192552324329)
      ·
        refine ⟨554415439335894414243247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 739220585781192552324329 554415439335894414243247)
        ·
          refine ⟨831623159003841621364871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554415439335894414243247 831623159003841621364871)
          ·
            refine ⟨1247434738505762432047307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831623159003841621364871 1247434738505762432047307)
            ·
              refine ⟨1871152107758643648070961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247434738505762432047307 1871152107758643648070961)
              ·
                refine ⟨1403364080818982736053221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871152107758643648070961 1403364080818982736053221)
                ·
                  refine ⟨263130765153559263009979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1403364080818982736053221 263130765153559263009979)
                  ·
                    rfl

theorem cell20_576501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_576501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576501 prefixEnd_576501 := by exact prefixLift 576501
  have htrace : WordTrace (prefixWord ++ tailWord_576501) baseStart_576501 baseEnd_576501 := by
    simpa [prefixWord, tailWord_576501, baseEnd_576501] using wordTrace_append hprefix tailTrace_576501
  have hstable : (prefixWord ++ tailWord_576501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576501).length < 2 ^ (prefixWord ++ tailWord_576501).sum := by decide
  have hdescent : baseEnd_576501 < baseStart_576501 := by decide
  rcases family_descends (prefixWord ++ tailWord_576501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576519 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 5]
def baseStart_576519 : Nat := 118140960795 + 576519 * 2 ^ 59
def prefixEnd_576519 : Nat := 4983230072969 + 3 ^ 40 * 576519 * 2
def baseEnd_576519 : Nat := 263138980844031200409905

theorem tailTrace_576519 : CollatzResearch.WordTrace tailWord_576519 prefixEnd_576519 263138980844031200409905 := by
  unfold tailWord_576519
  simp only [CollatzResearch.WordTrace]
  refine ⟨21027375398377599451380611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14018250265585066300920407 21027375398377599451380611)
  ·
    refine ⟨31541063097566399177070917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21027375398377599451380611 31541063097566399177070917)
    ·
      refine ⟨5913949330793699845700797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31541063097566399177070917 5913949330793699845700797)
      ·
        refine ⟨2217730999047637442137799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5913949330793699845700797 2217730999047637442137799)
        ·
          refine ⟨3326596498571456163206699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217730999047637442137799 3326596498571456163206699)
          ·
            refine ⟨4989894747857184244810049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3326596498571456163206699 4989894747857184244810049)
            ·
              refine ⟨3742421060892888183607537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4989894747857184244810049 3742421060892888183607537)
              ·
                refine ⟨2806815795669666137705653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3742421060892888183607537 2806815795669666137705653)
                ·
                  refine ⟨263138980844031200409905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2806815795669666137705653 263138980844031200409905)
                  ·
                    rfl

theorem cell20_576519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 5].length) (baseStart_576519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576519 prefixEnd_576519 := by exact prefixLift 576519
  have htrace : WordTrace (prefixWord ++ tailWord_576519) baseStart_576519 baseEnd_576519 := by
    simpa [prefixWord, tailWord_576519, baseEnd_576519] using wordTrace_append hprefix tailTrace_576519
  have hstable : (prefixWord ++ tailWord_576519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576519).length < 2 ^ (prefixWord ++ tailWord_576519).sum := by decide
  have hdescent : baseEnd_576519 < baseStart_576519 := by decide
  rcases family_descends (prefixWord ++ tailWord_576519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576522 : List Nat := [3, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_576522 : Nat := 118140960795 + 576522 * 2 ^ 59
def prefixEnd_576522 : Nat := 4983230072969 + 3 ^ 40 * 576522 * 2
def baseEnd_576522 : Nat := 263140350125776523309893

theorem tailTrace_576522 : CollatzResearch.WordTrace tailWord_576522 prefixEnd_576522 263140350125776523309893 := by
  unfold tailWord_576522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5256871204341682740934955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14018323211577820642493213 5256871204341682740934955)
  ·
    refine ⟨7885306806512524111402433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5256871204341682740934955 7885306806512524111402433)
    ·
      refine ⟨5913980104884393083551825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7885306806512524111402433 5913980104884393083551825)
      ·
        refine ⟨4435485078663294812663869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5913980104884393083551825 4435485078663294812663869)
        ·
          refine ⟨1663306904498735554748951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4435485078663294812663869 1663306904498735554748951)
          ·
            refine ⟨2494960356748103332123427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663306904498735554748951 2494960356748103332123427)
            ·
              refine ⟨3742440535122154998185141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494960356748103332123427 3742440535122154998185141)
              ·
                refine ⟨350853800167702031079857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3742440535122154998185141 350853800167702031079857)
                ·
                  refine ⟨263140350125776523309893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350853800167702031079857 263140350125776523309893)
                  ·
                    rfl

theorem cell20_576522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_576522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576522 prefixEnd_576522 := by exact prefixLift 576522
  have htrace : WordTrace (prefixWord ++ tailWord_576522) baseStart_576522 baseEnd_576522 := by
    simpa [prefixWord, tailWord_576522, baseEnd_576522] using wordTrace_append hprefix tailTrace_576522
  have hstable : (prefixWord ++ tailWord_576522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576522).length < 2 ^ (prefixWord ++ tailWord_576522).sum := by decide
  have hdescent : baseEnd_576522 < baseStart_576522 := by decide
  rcases family_descends (prefixWord ++ tailWord_576522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576536 : List Nat := [2, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_576536 : Nat := 118140960795 + 576536 * 2 ^ 59
def prefixEnd_576536 : Nat := 4983230072969 + 3 ^ 40 * 576536 * 2
def baseEnd_576536 : Nat := 263146740107254696843169

theorem tailTrace_576536 : CollatzResearch.WordTrace tailWord_576536 prefixEnd_576536 263146740107254696843169 := by
  unfold tailWord_576536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10513997719658005677374731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14018663626210674236499641 10513997719658005677374731)
  ·
    refine ⟨15770996579487008516062097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10513997719658005677374731 15770996579487008516062097)
    ·
      refine ⟨11828247434615256387046573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15770996579487008516062097 11828247434615256387046573)
      ·
        refine ⟨4435592787980721145142465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11828247434615256387046573 4435592787980721145142465)
        ·
          refine ⟨3326694590985540858856849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4435592787980721145142465 3326694590985540858856849)
          ·
            refine ⟨2495020943239155644142637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3326694590985540858856849 2495020943239155644142637)
            ·
              refine ⟨935632853714683366553489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2495020943239155644142637 935632853714683366553489)
              ·
                refine ⟨701724640286012524915117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935632853714683366553489 701724640286012524915117)
                ·
                  refine ⟨263146740107254696843169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701724640286012524915117 263146740107254696843169)
                  ·
                    rfl

theorem cell20_576536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_576536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576536 prefixEnd_576536 := by exact prefixLift 576536
  have htrace : WordTrace (prefixWord ++ tailWord_576536) baseStart_576536 baseEnd_576536 := by
    simpa [prefixWord, tailWord_576536, baseEnd_576536] using wordTrace_append hprefix tailTrace_576536
  have hstable : (prefixWord ++ tailWord_576536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576536).length < 2 ^ (prefixWord ++ tailWord_576536).sum := by decide
  have hdescent : baseEnd_576536 < baseStart_576536 := by decide
  rcases family_descends (prefixWord ++ tailWord_576536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576543 : List Nat := [1, 1, 2, 4, 1, 4, 2, 1, 4]
def baseStart_576543 : Nat := 118140960795 + 576543 * 2 ^ 59
def prefixEnd_576543 : Nat := 4983230072969 + 3 ^ 40 * 576543 * 2
def baseEnd_576543 : Nat := 263149935097993783609807

theorem tailTrace_576543 : CollatzResearch.WordTrace tailWord_576543 prefixEnd_576543 263149935097993783609807 := by
  unfold tailWord_576543
  simp only [CollatzResearch.WordTrace]
  refine ⟨21028250750290651550254283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14018833833527101033502855 21028250750290651550254283)
  ·
    refine ⟨31542376125435977325381425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21028250750290651550254283 31542376125435977325381425)
    ·
      refine ⟨23656782094076982994036069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31542376125435977325381425 23656782094076982994036069)
      ·
        refine ⟨4435646642639434311381763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23656782094076982994036069 4435646642639434311381763)
        ·
          refine ⟨6653469963959151467072645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4435646642639434311381763 6653469963959151467072645)
          ·
            refine ⟨1247525618242340900076121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6653469963959151467072645 1247525618242340900076121)
            ·
              refine ⟨935644213681755675057091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1247525618242340900076121 935644213681755675057091)
              ·
                refine ⟨1403466320522633512585637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 935644213681755675057091 1403466320522633512585637)
                ·
                  refine ⟨263149935097993783609807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1403466320522633512585637 263149935097993783609807)
                  ·
                    rfl

theorem cell20_576543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 4].length) (baseStart_576543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576543 prefixEnd_576543 := by exact prefixLift 576543
  have htrace : WordTrace (prefixWord ++ tailWord_576543) baseStart_576543 baseEnd_576543 := by
    simpa [prefixWord, tailWord_576543, baseEnd_576543] using wordTrace_append hprefix tailTrace_576543
  have hstable : (prefixWord ++ tailWord_576543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576543).length < 2 ^ (prefixWord ++ tailWord_576543).sum := by decide
  have hdescent : baseEnd_576543 < baseStart_576543 := by decide
  rcases family_descends (prefixWord ++ tailWord_576543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576574 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_576574 : Nat := 118140960795 + 576574 * 2 ^ 59
def prefixEnd_576574 : Nat := 4983230072969 + 3 ^ 40 * 576574 * 2
def baseEnd_576574 : Nat := 263164084342695453576347

theorem tailTrace_576574 : CollatzResearch.WordTrace tailWord_576574 prefixEnd_576574 263164084342695453576347 := by
  unfold tailWord_576574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2628672676647292980579097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14019587608785562563088517 2628672676647292980579097)
  ·
    refine ⟨1971504507485469735434323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2628672676647292980579097 1971504507485469735434323)
    ·
      refine ⟨2957256761228204603151485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971504507485469735434323 2957256761228204603151485)
      ·
        refine ⟨1108971285460576726181807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2957256761228204603151485 1108971285460576726181807)
        ·
          refine ⟨1663456928190865089272711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1108971285460576726181807 1663456928190865089272711)
          ·
            refine ⟨2495185392286297633909067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663456928190865089272711 2495185392286297633909067)
            ·
              refine ⟨3742778088429446450863601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2495185392286297633909067 3742778088429446450863601)
              ·
                refine ⟨2807083566322084838147701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3742778088429446450863601 2807083566322084838147701)
                ·
                  refine ⟨263164084342695453576347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2807083566322084838147701 263164084342695453576347)
                  ·
                    rfl

theorem cell20_576574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_576574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576574 prefixEnd_576574 := by exact prefixLift 576574
  have htrace : WordTrace (prefixWord ++ tailWord_576574) baseStart_576574 baseEnd_576574 := by
    simpa [prefixWord, tailWord_576574, baseEnd_576574] using wordTrace_append hprefix tailTrace_576574
  have hstable : (prefixWord ++ tailWord_576574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576574).length < 2 ^ (prefixWord ++ tailWord_576574).sum := by decide
  have hdescent : baseEnd_576574 < baseStart_576574 := by decide
  rcases family_descends (prefixWord ++ tailWord_576574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576602 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_576602 : Nat := 118140960795 + 576602 * 2 ^ 59
def prefixEnd_576602 : Nat := 4983230072969 + 3 ^ 40 * 576602 * 2
def baseEnd_576602 : Nat := 263176864305651800642899

theorem tailTrace_576602 : CollatzResearch.WordTrace tailWord_576602 prefixEnd_576602 263176864305651800642899 := by
  unfold tailWord_576602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5257600664269226156663015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14020268438051269751101373 5257600664269226156663015)
  ·
    refine ⟨7886400996403839234994523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5257600664269226156663015 7886400996403839234994523)
    ·
      refine ⟨11829601494605758852491785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7886400996403839234994523 11829601494605758852491785)
      ·
        refine ⟨8872201120954319139368839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11829601494605758852491785 8872201120954319139368839)
        ·
          refine ⟨13308301681431478709053259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8872201120954319139368839 13308301681431478709053259)
          ·
            refine ⟨19962452522147218063579889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13308301681431478709053259 19962452522147218063579889)
            ·
              refine ⟨14971839391610413547684917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19962452522147218063579889 14971839391610413547684917)
              ·
                refine ⟨1403609942963476270095461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14971839391610413547684917 1403609942963476270095461)
                ·
                  refine ⟨263176864305651800642899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1403609942963476270095461 263176864305651800642899)
                  ·
                    rfl

theorem cell20_576602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_576602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576602 prefixEnd_576602 := by exact prefixLift 576602
  have htrace : WordTrace (prefixWord ++ tailWord_576602) baseStart_576602 baseEnd_576602 := by
    simpa [prefixWord, tailWord_576602, baseEnd_576602] using wordTrace_append hprefix tailTrace_576602
  have hstable : (prefixWord ++ tailWord_576602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576602).length < 2 ^ (prefixWord ++ tailWord_576602).sum := by decide
  have hdescent : baseEnd_576602 < baseStart_576602 := by decide
  rcases family_descends (prefixWord ++ tailWord_576602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576609 : List Nat := [1, 2, 3, 1, 1, 2, 3, 7]
def baseStart_576609 : Nat := 118140960795 + 576609 * 2 ^ 59
def prefixEnd_576609 : Nat := 4983230072969 + 3 ^ 40 * 576609 * 2
def baseEnd_576609 : Nat := 87726686432130295803179

theorem tailTrace_576609 : CollatzResearch.WordTrace tailWord_576609 prefixEnd_576609 87726686432130295803179 := by
  unfold tailWord_576609
  simp only [CollatzResearch.WordTrace]
  refine ⟨21030657968051544822156881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14020438645367696548104587 21030657968051544822156881)
  ·
    refine ⟨15772993476038658616617661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21030657968051544822156881 15772993476038658616617661)
    ·
      refine ⟨5914872553514496981231623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15772993476038658616617661 5914872553514496981231623)
      ·
        refine ⟨8872308830271745471847435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5914872553514496981231623 8872308830271745471847435)
        ·
          refine ⟨13308463245407618207771153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8872308830271745471847435 13308463245407618207771153)
          ·
            refine ⟨9981347434055713655828365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13308463245407618207771153 9981347434055713655828365)
            ·
              refine ⟨3743005287770892620935637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9981347434055713655828365 3743005287770892620935637)
              ·
                refine ⟨87726686432130295803179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3743005287770892620935637 87726686432130295803179)
                ·
                  rfl

theorem cell20_576609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 7].length) (baseStart_576609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576609 prefixEnd_576609 := by exact prefixLift 576609
  have htrace : WordTrace (prefixWord ++ tailWord_576609) baseStart_576609 baseEnd_576609 := by
    simpa [prefixWord, tailWord_576609, baseEnd_576609] using wordTrace_append hprefix tailTrace_576609
  have hstable : (prefixWord ++ tailWord_576609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576609).length < 2 ^ (prefixWord ++ tailWord_576609).sum := by decide
  have hdescent : baseEnd_576609 < baseStart_576609 := by decide
  rcases family_descends (prefixWord ++ tailWord_576609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576650 : List Nat := [3, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_576650 : Nat := 118140960795 + 576650 * 2 ^ 59
def prefixEnd_576650 : Nat := 4983230072969 + 3 ^ 40 * 576650 * 2
def baseEnd_576650 : Nat := 263198772813576967042703

theorem tailTrace_576650 : CollatzResearch.WordTrace tailWord_576650 prefixEnd_576650 263198772813576967042703 := by
  unfold tailWord_576650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258038340225752206099851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14021435573935339216266269 5258038340225752206099851)
  ·
    refine ⟨7887057510338628309149777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5258038340225752206099851 7887057510338628309149777)
    ·
      refine ⟨5915293132753971231862333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7887057510338628309149777 5915293132753971231862333)
      ·
        refine ⟨2218234924782739211948375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5915293132753971231862333 2218234924782739211948375)
        ·
          refine ⟨3327352387174108817922563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2218234924782739211948375 3327352387174108817922563)
          ·
            refine ⟨4991028580761163226883845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3327352387174108817922563 4991028580761163226883845)
            ·
              refine ⟨935817858892718105040721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4991028580761163226883845 935817858892718105040721)
              ·
                refine ⟨701863394169538578780541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935817858892718105040721 701863394169538578780541)
                ·
                  refine ⟨263198772813576967042703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701863394169538578780541 263198772813576967042703)
                  ·
                    rfl

theorem cell20_576650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_576650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576650 prefixEnd_576650 := by exact prefixLift 576650
  have htrace : WordTrace (prefixWord ++ tailWord_576650) baseStart_576650 baseEnd_576650 := by
    simpa [prefixWord, tailWord_576650, baseEnd_576650] using wordTrace_append hprefix tailTrace_576650
  have hstable : (prefixWord ++ tailWord_576650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576650).length < 2 ^ (prefixWord ++ tailWord_576650).sum := by decide
  have hdescent : baseEnd_576650 < baseStart_576650 := by decide
  rcases family_descends (prefixWord ++ tailWord_576650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576664 : List Nat := [2, 1, 2, 4, 2, 1, 3, 5]
def baseStart_576664 : Nat := 118140960795 + 576664 * 2 ^ 59
def prefixEnd_576664 : Nat := 4983230072969 + 3 ^ 40 * 576664 * 2
def baseEnd_576664 : Nat := 87735054265018380191993

theorem tailTrace_576664 : CollatzResearch.WordTrace tailWord_576664 prefixEnd_576664 87735054265018380191993 := by
  unfold tailWord_576664
  simp only [CollatzResearch.WordTrace]
  refine ⟨10516331991426144607704523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14021775988568192810272697 10516331991426144607704523)
  ·
    refine ⟨15774497987139216911556785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10516331991426144607704523 15774497987139216911556785)
    ·
      refine ⟨11830873490354412683667589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15774497987139216911556785 11830873490354412683667589)
      ·
        refine ⟨2218288779441452378187673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11830873490354412683667589 2218288779441452378187673)
        ·
          refine ⟨1663716584581089283640755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2218288779441452378187673 1663716584581089283640755)
          ·
            refine ⟨2495574876871633925461133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663716584581089283640755 2495574876871633925461133)
            ·
              refine ⟨935840578826862722047925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2495574876871633925461133 935840578826862722047925)
              ·
                refine ⟨87735054265018380191993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 935840578826862722047925 87735054265018380191993)
                ·
                  rfl

theorem cell20_576664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_576664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576664 prefixEnd_576664 := by exact prefixLift 576664
  have htrace : WordTrace (prefixWord ++ tailWord_576664) baseStart_576664 baseEnd_576664 := by
    simpa [prefixWord, tailWord_576664, baseEnd_576664] using wordTrace_append hprefix tailTrace_576664
  have hstable : (prefixWord ++ tailWord_576664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576664).length < 2 ^ (prefixWord ++ tailWord_576664).sum := by decide
  have hdescent : baseEnd_576664 < baseStart_576664 := by decide
  rcases family_descends (prefixWord ++ tailWord_576664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576674 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_576674 : Nat := 118140960795 + 576674 * 2 ^ 59
def prefixEnd_576674 : Nat := 4983230072969 + 3 ^ 40 * 576674 * 2
def baseEnd_576674 : Nat := 263209727067539550242605

theorem tailTrace_576674 : CollatzResearch.WordTrace tailWord_576674 prefixEnd_576674 263209727067539550242605 := by
  unfold tailWord_576674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5258257178204015230818269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14022019141877373948848717 5258257178204015230818269)
  ·
    refine ⟨1971846441826505711556851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5258257178204015230818269 1971846441826505711556851)
    ·
      refine ⟨2957769662739758567335277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971846441826505711556851 2957769662739758567335277)
      ·
        refine ⟨1109163623527409462750729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2957769662739758567335277 1109163623527409462750729)
        ·
          refine ⟨831872717645557097063047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109163623527409462750729 831872717645557097063047)
          ·
            refine ⟨1247809076468335645594571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 831872717645557097063047 1247809076468335645594571)
            ·
              refine ⟨1871713614702503468391857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247809076468335645594571 1871713614702503468391857)
              ·
                refine ⟨1403785211026877601293893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1871713614702503468391857 1403785211026877601293893)
                ·
                  refine ⟨263209727067539550242605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1403785211026877601293893 263209727067539550242605)
                  ·
                    rfl

theorem cell20_576674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_576674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576674 prefixEnd_576674 := by exact prefixLift 576674
  have htrace : WordTrace (prefixWord ++ tailWord_576674) baseStart_576674 baseEnd_576674 := by
    simpa [prefixWord, tailWord_576674, baseEnd_576674] using wordTrace_append hprefix tailTrace_576674
  have hstable : (prefixWord ++ tailWord_576674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576674).length < 2 ^ (prefixWord ++ tailWord_576674).sum := by decide
  have hdescent : baseEnd_576674 < baseStart_576674 := by decide
  rcases family_descends (prefixWord ++ tailWord_576674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576702 : List Nat := [4, 2, 1, 1, 3, 2, 7]
def baseStart_576702 : Nat := 118140960795 + 576702 * 2 ^ 59
def prefixEnd_576702 : Nat := 4983230072969 + 3 ^ 40 * 576702 * 2
def baseEnd_576702 : Nat := 29246945225610655256573

theorem tailTrace_576702 : CollatzResearch.WordTrace tailWord_576702 prefixEnd_576702 29246945225610655256573 := by
  unfold tailWord_576702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629256244589327713161545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14022699971143081136861573 2629256244589327713161545)
  ·
    refine ⟨1971942183441995784871159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2629256244589327713161545 1971942183441995784871159)
    ·
      refine ⟨2957913275162993677306739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971942183441995784871159 2957913275162993677306739)
      ·
        refine ⟨4436869912744490515960109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957913275162993677306739 4436869912744490515960109)
        ·
          refine ⟨1663826217279183943485041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4436869912744490515960109 1663826217279183943485041)
          ·
            refine ⟨1247869662959387957613781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1663826217279183943485041 1247869662959387957613781)
            ·
              refine ⟨29246945225610655256573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1247869662959387957613781 29246945225610655256573)
              ·
                rfl

theorem cell20_576702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 7].length) (baseStart_576702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576702 prefixEnd_576702 := by exact prefixLift 576702
  have htrace : WordTrace (prefixWord ++ tailWord_576702) baseStart_576702 baseEnd_576702 := by
    simpa [prefixWord, tailWord_576702, baseEnd_576702] using wordTrace_append hprefix tailTrace_576702
  have hstable : (prefixWord ++ tailWord_576702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576702).length < 2 ^ (prefixWord ++ tailWord_576702).sum := by decide
  have hdescent : baseEnd_576702 < baseStart_576702 := by decide
  rcases family_descends (prefixWord ++ tailWord_576702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576705 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 3]
def baseStart_576705 : Nat := 118140960795 + 576705 * 2 ^ 59
def prefixEnd_576705 : Nat := 4983230072969 + 3 ^ 40 * 576705 * 2
def baseEnd_576705 : Nat := 263223876312241220209145

theorem tailTrace_576705 : CollatzResearch.WordTrace tailWord_576705 prefixEnd_576705 263223876312241220209145 := by
  unfold tailWord_576705
  simp only [CollatzResearch.WordTrace]
  refine ⟨21034159375703753217651569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14022772917135835478434379 21034159375703753217651569)
  ·
    refine ⟨15775619531777814913238677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21034159375703753217651569 15775619531777814913238677)
    ·
      refine ⟨739482165552085074058063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15775619531777814913238677 739482165552085074058063)
      ·
        refine ⟨1109223248328127611087095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739482165552085074058063 1109223248328127611087095)
        ·
          refine ⟨1663834872492191416630643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109223248328127611087095 1663834872492191416630643)
          ·
            refine ⟨2495752308738287124945965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1663834872492191416630643 2495752308738287124945965)
            ·
              refine ⟨935907115776857671854737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2495752308738287124945965 935907115776857671854737)
              ·
                refine ⟨701930336832643253891053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 935907115776857671854737 701930336832643253891053)
                ·
                  refine ⟨263223876312241220209145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 701930336832643253891053 263223876312241220209145)
                  ·
                    rfl

theorem cell20_576705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_576705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576705 prefixEnd_576705 := by exact prefixLift 576705
  have htrace : WordTrace (prefixWord ++ tailWord_576705) baseStart_576705 baseEnd_576705 := by
    simpa [prefixWord, tailWord_576705, baseEnd_576705] using wordTrace_append hprefix tailTrace_576705
  have hstable : (prefixWord ++ tailWord_576705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576705).length < 2 ^ (prefixWord ++ tailWord_576705).sum := by decide
  have hdescent : baseEnd_576705 < baseStart_576705 := by decide
  rcases family_descends (prefixWord ++ tailWord_576705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576740 : List Nat := [2, 3, 1, 1, 1, 2, 6, 4]
def baseStart_576740 : Nat := 118140960795 + 576740 * 2 ^ 59
def prefixEnd_576740 : Nat := 4983230072969 + 3 ^ 40 * 576740 * 2
def baseEnd_576740 : Nat := 87746617088645551347445

theorem tailTrace_576740 : CollatzResearch.WordTrace tailWord_576740 prefixEnd_576740 87746617088645551347445 := by
  unfold tailWord_576740
  simp only [CollatzResearch.WordTrace]
  refine ⟨10517717965288477097587837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14023623953717969463450449 10517717965288477097587837)
  ·
    refine ⟨3944144236983178911595439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10517717965288477097587837 3944144236983178911595439)
    ·
      refine ⟨5916216355474768367393159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3944144236983178911595439 5916216355474768367393159)
      ·
        refine ⟨8874324533212152551089739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5916216355474768367393159 8874324533212152551089739)
        ·
          refine ⟨13311486799818228826634609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8874324533212152551089739 13311486799818228826634609)
          ·
            refine ⟨9983615099863671619975957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13311486799818228826634609 9983615099863671619975957)
            ·
              refine ⟨467981957806109607186373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9983615099863671619975957 467981957806109607186373)
              ·
                refine ⟨87746617088645551347445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 467981957806109607186373 87746617088645551347445)
                ·
                  rfl

theorem cell20_576740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_576740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576740 prefixEnd_576740 := by exact prefixLift 576740
  have htrace : WordTrace (prefixWord ++ tailWord_576740) baseStart_576740 baseEnd_576740 := by
    simpa [prefixWord, tailWord_576740, baseEnd_576740] using wordTrace_append hprefix tailTrace_576740
  have hstable : (prefixWord ++ tailWord_576740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576740).length < 2 ^ (prefixWord ++ tailWord_576740).sum := by decide
  have hdescent : baseEnd_576740 < baseStart_576740 := by decide
  rcases family_descends (prefixWord ++ tailWord_576740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576750 : List Nat := [4, 1, 2, 1, 1, 1, 5, 3, 2]
def baseStart_576750 : Nat := 118140960795 + 576750 * 2 ^ 59
def prefixEnd_576750 : Nat := 4983230072969 + 3 ^ 40 * 576750 * 2
def baseEnd_576750 : Nat := 263244415538421063708961

theorem tailTrace_576750 : CollatzResearch.WordTrace tailWord_576750 prefixEnd_576750 263244415538421063708961 := by
  unfold tailWord_576750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629475082567590737879963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14023867107027150602026469 2629475082567590737879963)
  ·
    refine ⟨3944212623851386106819945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2629475082567590737879963 3944212623851386106819945)
    ·
      refine ⟨2958159467888539580114959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3944212623851386106819945 2958159467888539580114959)
      ·
        refine ⟨4437239201832809370172439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2958159467888539580114959 4437239201832809370172439)
        ·
          refine ⟨6655858802749214055258659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4437239201832809370172439 6655858802749214055258659)
          ·
            refine ⟨9983788204123821082887989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6655858802749214055258659 9983788204123821082887989)
            ·
              refine ⟨935980144136608226520749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9983788204123821082887989 935980144136608226520749)
              ·
                refine ⟨350992554051228084945281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 935980144136608226520749 350992554051228084945281)
                ·
                  refine ⟨263244415538421063708961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 350992554051228084945281 263244415538421063708961)
                  ·
                    rfl

theorem cell20_576750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_576750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576750 prefixEnd_576750 := by exact prefixLift 576750
  have htrace : WordTrace (prefixWord ++ tailWord_576750) baseStart_576750 baseEnd_576750 := by
    simpa [prefixWord, tailWord_576750, baseEnd_576750] using wordTrace_append hprefix tailTrace_576750
  have hstable : (prefixWord ++ tailWord_576750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576750).length < 2 ^ (prefixWord ++ tailWord_576750).sum := by decide
  have hdescent : baseEnd_576750 < baseStart_576750 := by decide
  rcases family_descends (prefixWord ++ tailWord_576750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576771 : List Nat := [1, 1, 1, 3, 2, 6, 1, 1, 4]
def baseStart_576771 : Nat := 118140960795 + 576771 * 2 ^ 59
def prefixEnd_576771 : Nat := 4983230072969 + 3 ^ 40 * 576771 * 2
def baseEnd_576771 : Nat := 263254000510638324008875

theorem tailTrace_576771 : CollatzResearch.WordTrace tailWord_576771 prefixEnd_576771 263254000510638324008875 := by
  unfold tailWord_576771
  simp only [CollatzResearch.WordTrace]
  refine ⟨21036566593464646489554167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14024377728976430993036111 21036566593464646489554167)
  ·
    refine ⟨31554849890196969734331251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21036566593464646489554167 31554849890196969734331251)
    ·
      refine ⟨47332274835295454601496877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31554849890196969734331251 47332274835295454601496877)
      ·
        refine ⟨17749603063235795475561329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47332274835295454601496877 17749603063235795475561329)
        ·
          refine ⟨13312202297426846606670997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17749603063235795475561329 13312202297426846606670997)
          ·
            refine ⟨624009482691883434687703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13312202297426846606670997 624009482691883434687703)
            ·
              refine ⟨936014224037825152031555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624009482691883434687703 936014224037825152031555)
              ·
                refine ⟨1404021336056737728047333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 936014224037825152031555 1404021336056737728047333)
                ·
                  refine ⟨263254000510638324008875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404021336056737728047333 263254000510638324008875)
                  ·
                    rfl

theorem cell20_576771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_576771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576771 prefixEnd_576771 := by exact prefixLift 576771
  have htrace : WordTrace (prefixWord ++ tailWord_576771) baseStart_576771 baseEnd_576771 := by
    simpa [prefixWord, tailWord_576771, baseEnd_576771] using wordTrace_append hprefix tailTrace_576771
  have hstable : (prefixWord ++ tailWord_576771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576771).length < 2 ^ (prefixWord ++ tailWord_576771).sum := by decide
  have hdescent : baseEnd_576771 < baseStart_576771 := by decide
  rcases family_descends (prefixWord ++ tailWord_576771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576785 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 3]
def baseStart_576785 : Nat := 118140960795 + 576785 * 2 ^ 59
def prefixEnd_576785 : Nat := 4983230072969 + 3 ^ 40 * 576785 * 2
def baseEnd_576785 : Nat := 263260390492116497542151

theorem tailTrace_576785 : CollatzResearch.WordTrace tailWord_576785 prefixEnd_576785 263260390492116497542151 := by
  unfold tailWord_576785
  simp only [CollatzResearch.WordTrace]
  refine ⟨21037077215413926880563809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14024718143609284587042539 21037077215413926880563809)
  ·
    refine ⟨15777807911560445160422857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21037077215413926880563809 15777807911560445160422857)
    ·
      refine ⟨11833355933670333870317143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15777807911560445160422857 11833355933670333870317143)
      ·
        refine ⟨17750033900505500805475715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11833355933670333870317143 17750033900505500805475715)
        ·
          refine ⟨26625050850758251208213573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17750033900505500805475715 26625050850758251208213573)
          ·
            refine ⟨4992197034517172101540045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26625050850758251208213573 4992197034517172101540045)
            ·
              refine ⟨1872073887943939538077517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4992197034517172101540045 1872073887943939538077517)
              ·
                refine ⟨702027707978977326779069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1872073887943939538077517 702027707978977326779069)
                ·
                  refine ⟨263260390492116497542151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702027707978977326779069 263260390492116497542151)
                  ·
                    rfl

theorem cell20_576785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_576785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576785 prefixEnd_576785 := by exact prefixLift 576785
  have htrace : WordTrace (prefixWord ++ tailWord_576785) baseStart_576785 baseEnd_576785 := by
    simpa [prefixWord, tailWord_576785, baseEnd_576785] using wordTrace_append hprefix tailTrace_576785
  have hstable : (prefixWord ++ tailWord_576785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576785).length < 2 ^ (prefixWord ++ tailWord_576785).sum := by decide
  have hdescent : baseEnd_576785 < baseStart_576785 := by decide
  rcases family_descends (prefixWord ++ tailWord_576785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576822 : List Nat := [5, 1, 2, 3, 1, 1, 1, 4, 2]
def baseStart_576822 : Nat := 118140960795 + 576822 * 2 ^ 59
def prefixEnd_576822 : Nat := 4983230072969 + 3 ^ 40 * 576822 * 2
def baseEnd_576822 : Nat := 263277278300308813308667

theorem tailTrace_576822 : CollatzResearch.WordTrace tailWord_576822 prefixEnd_576822 263277278300308813308667 := by
  unfold tailWord_576822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1314901669767492637478795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14025617810853254799773813 1314901669767492637478795)
  ·
    refine ⟨1972352504651238956218193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1314901669767492637478795 1972352504651238956218193)
    ·
      refine ⟨1479264378488429217163645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1972352504651238956218193 1479264378488429217163645)
      ·
        refine ⟨554724141933160956436367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1479264378488429217163645 554724141933160956436367)
        ·
          refine ⟨832086212899741434654551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 554724141933160956436367 832086212899741434654551)
          ·
            refine ⟨1248129319349612151981827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832086212899741434654551 1248129319349612151981827)
            ·
              refine ⟨1872193979024418227972741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248129319349612151981827 1872193979024418227972741)
              ·
                refine ⟨351036371067078417744889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1872193979024418227972741 351036371067078417744889)
                ·
                  refine ⟨263277278300308813308667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351036371067078417744889 263277278300308813308667)
                  ·
                    rfl

theorem cell20_576822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_576822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576822 prefixEnd_576822 := by exact prefixLift 576822
  have htrace : WordTrace (prefixWord ++ tailWord_576822) baseStart_576822 baseEnd_576822 := by
    simpa [prefixWord, tailWord_576822, baseEnd_576822] using wordTrace_append hprefix tailTrace_576822
  have hstable : (prefixWord ++ tailWord_576822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576822).length < 2 ^ (prefixWord ++ tailWord_576822).sum := by decide
  have hdescent : baseEnd_576822 < baseStart_576822 := by decide
  rcases family_descends (prefixWord ++ tailWord_576822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576833 : List Nat := [1, 2, 5, 2, 1, 3, 1, 5]
def baseStart_576833 : Nat := 118140960795 + 576833 * 2 ^ 59
def prefixEnd_576833 : Nat := 4983230072969 + 3 ^ 40 * 576833 * 2
def baseEnd_576833 : Nat := 87760766333347221313985

theorem tailTrace_576833 : CollatzResearch.WordTrace tailWord_576833 prefixEnd_576833 87760766333347221313985 := by
  unfold tailWord_576833
  simp only [CollatzResearch.WordTrace]
  refine ⟨21038827919240031078311153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14025885279493354052207435 21038827919240031078311153)
  ·
    refine ⟨15779120939430023308733365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21038827919240031078311153 15779120939430023308733365)
    ·
      refine ⟨1479292588071564685193753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15779120939430023308733365 1479292588071564685193753)
      ·
        refine ⟨1109469441053673513895315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479292588071564685193753 1109469441053673513895315)
        ·
          refine ⟨1664204161580510270842973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1109469441053673513895315 1664204161580510270842973)
          ·
            refine ⟨624076560592691351566115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1664204161580510270842973 624076560592691351566115)
            ·
              refine ⟨936114840889037027349173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624076560592691351566115 936114840889037027349173)
              ·
                refine ⟨87760766333347221313985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 936114840889037027349173 87760766333347221313985)
                ·
                  rfl

theorem cell20_576833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_576833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576833 prefixEnd_576833 := by exact prefixLift 576833
  have htrace : WordTrace (prefixWord ++ tailWord_576833) baseStart_576833 baseEnd_576833 := by
    simpa [prefixWord, tailWord_576833, baseEnd_576833] using wordTrace_append hprefix tailTrace_576833
  have hstable : (prefixWord ++ tailWord_576833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576833).length < 2 ^ (prefixWord ++ tailWord_576833).sum := by decide
  have hdescent : baseEnd_576833 < baseStart_576833 := by decide
  rcases family_descends (prefixWord ++ tailWord_576833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576864 : List Nat := [2, 1, 1, 3, 4, 2, 2, 3, 2]
def baseStart_576864 : Nat := 118140960795 + 576864 * 2 ^ 59
def prefixEnd_576864 : Nat := 4983230072969 + 3 ^ 40 * 576864 * 2
def baseEnd_576864 : Nat := 263296448244743333908495

theorem tailTrace_576864 : CollatzResearch.WordTrace tailWord_576864 prefixEnd_576864 263296448244743333908495 := by
  unfold tailWord_576864
  simp only [CollatzResearch.WordTrace]
  refine ⟨10519979291063861686344823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14026639054751815581793097 10519979291063861686344823)
  ·
    refine ⟨15779968936595792529517235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10519979291063861686344823 15779968936595792529517235)
    ·
      refine ⟨23669953404893688794275853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15779968936595792529517235 23669953404893688794275853)
      ·
        refine ⟨8876232526835133297853445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23669953404893688794275853 8876232526835133297853445)
        ·
          refine ⟨1664293598781587493347521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8876232526835133297853445 1664293598781587493347521)
          ·
            refine ⟨1248220199086190620010641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1664293598781587493347521 1248220199086190620010641)
            ·
              refine ⟨936165149314642965007981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1248220199086190620010641 936165149314642965007981)
              ·
                refine ⟨351061930992991111877993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 936165149314642965007981 351061930992991111877993)
                ·
                  refine ⟨263296448244743333908495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351061930992991111877993 263296448244743333908495)
                  ·
                    rfl

theorem cell20_576864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 2].length) (baseStart_576864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576864 prefixEnd_576864 := by exact prefixLift 576864
  have htrace : WordTrace (prefixWord ++ tailWord_576864) baseStart_576864 baseEnd_576864 := by
    simpa [prefixWord, tailWord_576864, baseEnd_576864] using wordTrace_append hprefix tailTrace_576864
  have hstable : (prefixWord ++ tailWord_576864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576864).length < 2 ^ (prefixWord ++ tailWord_576864).sum := by decide
  have hdescent : baseEnd_576864 < baseStart_576864 := by decide
  rcases family_descends (prefixWord ++ tailWord_576864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576874 : List Nat := [3, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_576874 : Nat := 118140960795 + 576874 * 2 ^ 59
def prefixEnd_576874 : Nat := 4983230072969 + 3 ^ 40 * 576874 * 2
def baseEnd_576874 : Nat := 263301012517227743575121

theorem tailTrace_576874 : CollatzResearch.WordTrace tailWord_576874 prefixEnd_576874 263301012517227743575121 := by
  unfold tailWord_576874
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260080828022873770138419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14026882208060996720369117 5260080828022873770138419)
  ·
    refine ⟨7890121242034310655207629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5260080828022873770138419 7890121242034310655207629)
    ·
      refine ⟨2958795465762866495702861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7890121242034310655207629 2958795465762866495702861)
      ·
        refine ⟨1109548299661074935888573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2958795465762866495702861 1109548299661074935888573)
        ·
          refine ⟨416080612372903100958215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1109548299661074935888573 416080612372903100958215)
          ·
            refine ⟨624120918559354651437323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416080612372903100958215 624120918559354651437323)
            ·
              refine ⟨936181377839031977155985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624120918559354651437323 936181377839031977155985)
              ·
                refine ⟨702136033379273982866989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 936181377839031977155985 702136033379273982866989)
                ·
                  refine ⟨263301012517227743575121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702136033379273982866989 263301012517227743575121)
                  ·
                    rfl

theorem cell20_576874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_576874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576874 prefixEnd_576874 := by exact prefixLift 576874
  have htrace : WordTrace (prefixWord ++ tailWord_576874) baseStart_576874 baseEnd_576874 := by
    simpa [prefixWord, tailWord_576874, baseEnd_576874] using wordTrace_append hprefix tailTrace_576874
  have hstable : (prefixWord ++ tailWord_576874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576874).length < 2 ^ (prefixWord ++ tailWord_576874).sum := by decide
  have hdescent : baseEnd_576874 < baseStart_576874 := by decide
  rcases family_descends (prefixWord ++ tailWord_576874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576926 : List Nat := [4, 3, 1, 2, 3, 1, 6]
def baseStart_576926 : Nat := 118140960795 + 576926 * 2 ^ 59
def prefixEnd_576926 : Nat := 4983230072969 + 3 ^ 40 * 576926 * 2
def baseEnd_576926 : Nat := 29258305192682963760175

theorem tailTrace_576926 : CollatzResearch.WordTrace tailWord_576926 prefixEnd_576926 29258305192682963760175 := by
  unfold tailWord_576926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2630277488487888495180829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14028146605268738640964421 2630277488487888495180829)
  ·
    refine ⟨986354058182958185692811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2630277488487888495180829 986354058182958185692811)
    ·
      refine ⟨1479531087274437278539217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986354058182958185692811 1479531087274437278539217)
      ·
        refine ⟨1109648315455827958904413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1479531087274437278539217 1109648315455827958904413)
        ·
          refine ⟨416118118295935484589155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1109648315455827958904413 416118118295935484589155)
          ·
            refine ⟨624177177443903226883733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416118118295935484589155 624177177443903226883733)
            ·
              refine ⟨29258305192682963760175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 624177177443903226883733 29258305192682963760175)
              ·
                rfl

theorem cell20_576926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 6].length) (baseStart_576926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576926 prefixEnd_576926 := by exact prefixLift 576926
  have htrace : WordTrace (prefixWord ++ tailWord_576926) baseStart_576926 baseEnd_576926 := by
    simpa [prefixWord, tailWord_576926, baseEnd_576926] using wordTrace_append hprefix tailTrace_576926
  have hstable : (prefixWord ++ tailWord_576926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576926).length < 2 ^ (prefixWord ++ tailWord_576926).sum := by decide
  have hdescent : baseEnd_576926 < baseStart_576926 := by decide
  rcases family_descends (prefixWord ++ tailWord_576926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576930 : List Nat := [3, 3, 1, 2, 1, 4, 6]
def baseStart_576930 : Nat := 118140960795 + 576930 * 2 ^ 59
def prefixEnd_576930 : Nat := 4983230072969 + 3 ^ 40 * 576930 * 2
def baseEnd_576930 : Nat := 29258508049237826412025

theorem tailTrace_576930 : CollatzResearch.WordTrace tailWord_576930 prefixEnd_576930 29258508049237826412025 := by
  unfold tailWord_576930
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260591449972154161148061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14028243866592411096394829 5260591449972154161148061)
  ·
    refine ⟨1972721793739557810430523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5260591449972154161148061 1972721793739557810430523)
    ·
      refine ⟨2959082690609336715645785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1972721793739557810430523 2959082690609336715645785)
      ·
        refine ⟨2219312017957002536734339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2959082690609336715645785 2219312017957002536734339)
        ·
          refine ⟨3328968026935503805101509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219312017957002536734339 3328968026935503805101509)
          ·
            refine ⟨624181505050406963456533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3328968026935503805101509 624181505050406963456533)
            ·
              refine ⟨29258508049237826412025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 624181505050406963456533 29258508049237826412025)
              ·
                rfl

theorem cell20_576930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 6].length) (baseStart_576930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576930 prefixEnd_576930 := by exact prefixLift 576930
  have htrace : WordTrace (prefixWord ++ tailWord_576930) baseStart_576930 baseEnd_576930 := by
    simpa [prefixWord, tailWord_576930, baseEnd_576930] using wordTrace_append hprefix tailTrace_576930
  have hstable : (prefixWord ++ tailWord_576930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576930).length < 2 ^ (prefixWord ++ tailWord_576930).sum := by decide
  have hdescent : baseEnd_576930 < baseStart_576930 := by decide
  rcases family_descends (prefixWord ++ tailWord_576930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576936 : List Nat := [2, 1, 6, 1, 2, 1, 3, 2, 2]
def baseStart_576936 : Nat := 118140960795 + 576936 * 2 ^ 59
def prefixEnd_576936 : Nat := 4983230072969 + 3 ^ 40 * 576936 * 2
def baseEnd_576936 : Nat := 263329311006631083508201

theorem tailTrace_576936 : CollatzResearch.WordTrace tailWord_576936 prefixEnd_576936 263329311006631083508201 := by
  unfold tailWord_576936
  simp only [CollatzResearch.WordTrace]
  refine ⟨10521292318933439834655331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14028389758577919779540441 10521292318933439834655331)
  ·
    refine ⟨15781938478400159751982997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10521292318933439834655331 15781938478400159751982997)
    ·
      refine ⟨739778366175007488374203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15781938478400159751982997 739778366175007488374203)
      ·
        refine ⟨1109667549262511232561305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 739778366175007488374203 1109667549262511232561305)
        ·
          refine ⟨832250661946883424420979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1109667549262511232561305 832250661946883424420979)
          ·
            refine ⟨1248375992920325136631469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 832250661946883424420979 1248375992920325136631469)
            ·
              refine ⟨468140997345121926236801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1248375992920325136631469 468140997345121926236801)
              ·
                refine ⟨351105748008841444677601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468140997345121926236801 351105748008841444677601)
                ·
                  refine ⟨263329311006631083508201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351105748008841444677601 263329311006631083508201)
                  ·
                    rfl

theorem cell20_576936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 2, 2].length) (baseStart_576936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576936 prefixEnd_576936 := by exact prefixLift 576936
  have htrace : WordTrace (prefixWord ++ tailWord_576936) baseStart_576936 baseEnd_576936 := by
    simpa [prefixWord, tailWord_576936, baseEnd_576936] using wordTrace_append hprefix tailTrace_576936
  have hstable : (prefixWord ++ tailWord_576936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576936).length < 2 ^ (prefixWord ++ tailWord_576936).sum := by decide
  have hdescent : baseEnd_576936 < baseStart_576936 := by decide
  rcases family_descends (prefixWord ++ tailWord_576936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576951 : List Nat := [1, 1, 3, 1, 3, 2, 4, 5]
def baseStart_576951 : Nat := 118140960795 + 576951 * 2 ^ 59
def prefixEnd_576951 : Nat := 4983230072969 + 3 ^ 40 * 576951 * 2
def baseEnd_576951 : Nat := 87778719138452566002713

theorem tailTrace_576951 : CollatzResearch.WordTrace tailWord_576951 prefixEnd_576951 87778719138452566002713 := by
  unfold tailWord_576951
  simp only [CollatzResearch.WordTrace]
  refine ⟨21043131732812537231106707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14028754488541691487404471 21043131732812537231106707)
  ·
    refine ⟨31564697599218805846660061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21043131732812537231106707 31564697599218805846660061)
    ·
      refine ⟨11836761599707052192497523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31564697599218805846660061 11836761599707052192497523)
      ·
        refine ⟨17755142399560578288746285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11836761599707052192497523 17755142399560578288746285)
        ·
          refine ⟨6658178399835216858279857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17755142399560578288746285 6658178399835216858279857)
          ·
            refine ⟨4993633799876412643709893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6658178399835216858279857 4993633799876412643709893)
            ·
              refine ⟨936306337476827370695605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4993633799876412643709893 936306337476827370695605)
              ·
                refine ⟨87778719138452566002713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 936306337476827370695605 87778719138452566002713)
                ·
                  rfl

theorem cell20_576951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_576951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576951 prefixEnd_576951 := by exact prefixLift 576951
  have htrace : WordTrace (prefixWord ++ tailWord_576951) baseStart_576951 baseEnd_576951 := by
    simpa [prefixWord, tailWord_576951, baseEnd_576951] using wordTrace_append hprefix tailTrace_576951
  have hstable : (prefixWord ++ tailWord_576951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576951).length < 2 ^ (prefixWord ++ tailWord_576951).sum := by decide
  have hdescent : baseEnd_576951 < baseStart_576951 := by decide
  rcases family_descends (prefixWord ++ tailWord_576951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576989 : List Nat := [1, 4, 3, 1, 1, 10]
def baseStart_576989 : Nat := 118140960795 + 576989 * 2 ^ 59
def prefixEnd_576989 : Nat := 4983230072969 + 3 ^ 40 * 576989 * 2
def baseEnd_576989 : Nat := 9753833394474016842271

theorem tailTrace_576989 : CollatzResearch.WordTrace tailWord_576989 prefixEnd_576989 9753833394474016842271 := by
  unfold tailWord_576989
  simp only [CollatzResearch.WordTrace]
  refine ⟨21044517706674869720990021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14029678471116579813993347 21044517706674869720990021)
  ·
    refine ⟨3945847070001538072685629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21044517706674869720990021 3945847070001538072685629)
    ·
      refine ⟨1479692651250576777257111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3945847070001538072685629 1479692651250576777257111)
      ·
        refine ⟨2219538976875865165885667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479692651250576777257111 2219538976875865165885667)
        ·
          refine ⟨3329308465313797748828501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2219538976875865165885667 3329308465313797748828501)
          ·
            refine ⟨9753833394474016842271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3329308465313797748828501 9753833394474016842271)
            ·
              rfl

theorem cell20_576989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 10].length) (baseStart_576989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576989 prefixEnd_576989 := by exact prefixLift 576989
  have htrace : WordTrace (prefixWord ++ tailWord_576989) baseStart_576989 baseEnd_576989 := by
    simpa [prefixWord, tailWord_576989, baseEnd_576989] using wordTrace_append hprefix tailTrace_576989
  have hstable : (prefixWord ++ tailWord_576989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576989).length < 2 ^ (prefixWord ++ tailWord_576989).sum := by decide
  have hdescent : baseEnd_576989 < baseStart_576989 := by decide
  rcases family_descends (prefixWord ++ tailWord_576989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576995 : List Nat := [1, 1, 1, 6, 2, 3, 2, 2, 2]
def baseStart_576995 : Nat := 118140960795 + 576995 * 2 ^ 59
def prefixEnd_576995 : Nat := 4983230072969 + 3 ^ 40 * 576995 * 2
def baseEnd_576995 : Nat := 263356240214289100541293

theorem tailTrace_576995 : CollatzResearch.WordTrace tailWord_576995 prefixEnd_576995 263356240214289100541293 := by
  unfold tailWord_576995
  simp only [CollatzResearch.WordTrace]
  refine ⟨21044736544653132745708439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14029824363102088497138959 21044736544653132745708439)
  ·
    refine ⟨31567104816979699118562659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21044736544653132745708439 31567104816979699118562659)
    ·
      refine ⟨47350657225469548677843989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31567104816979699118562659 47350657225469548677843989)
      ·
        refine ⟨2219562057443885094273937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47350657225469548677843989 2219562057443885094273937)
        ·
          refine ⟨1664671543082913820705453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2219562057443885094273937 1664671543082913820705453)
          ·
            refine ⟨624251828656092682764545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1664671543082913820705453 624251828656092682764545)
            ·
              refine ⟨468188871492069512073409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624251828656092682764545 468188871492069512073409)
              ·
                refine ⟨351141653619052134055057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 468188871492069512073409 351141653619052134055057)
                ·
                  refine ⟨263356240214289100541293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 351141653619052134055057 263356240214289100541293)
                  ·
                    rfl

theorem cell20_576995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 2, 2].length) (baseStart_576995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576995 prefixEnd_576995 := by exact prefixLift 576995
  have htrace : WordTrace (prefixWord ++ tailWord_576995) baseStart_576995 baseEnd_576995 := by
    simpa [prefixWord, tailWord_576995, baseEnd_576995] using wordTrace_append hprefix tailTrace_576995
  have hstable : (prefixWord ++ tailWord_576995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576995).length < 2 ^ (prefixWord ++ tailWord_576995).sum := by decide
  have hdescent : baseEnd_576995 < baseStart_576995 := by decide
  rcases family_descends (prefixWord ++ tailWord_576995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_576996 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 5]
def baseStart_576996 : Nat := 118140960795 + 576996 * 2 ^ 59
def prefixEnd_576996 : Nat := 4983230072969 + 3 ^ 40 * 576996 * 2
def baseEnd_576996 : Nat := 263356696641537541507955

theorem tailTrace_576996 : CollatzResearch.WordTrace tailWord_576996 prefixEnd_576996 263356696641537541507955 := by
  unfold tailWord_576996
  simp only [CollatzResearch.WordTrace]
  refine ⟨10522386508824754958247421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14029848678433006610996561 10522386508824754958247421)
  ·
    refine ⟨3945894940809283109342783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10522386508824754958247421 3945894940809283109342783)
    ·
      refine ⟨5918842411213924664014175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945894940809283109342783 5918842411213924664014175)
      ·
        refine ⟨8878263616820886996021263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5918842411213924664014175 8878263616820886996021263)
        ·
          refine ⟨13317395425231330494031895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8878263616820886996021263 13317395425231330494031895)
          ·
            refine ⟨19976093137846995741047843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13317395425231330494031895 19976093137846995741047843)
            ·
              refine ⟨29964139706770493611571765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19976093137846995741047843 29964139706770493611571765)
              ·
                refine ⟨2809138097509733776084853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29964139706770493611571765 2809138097509733776084853)
                ·
                  refine ⟨263356696641537541507955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2809138097509733776084853 263356696641537541507955)
                  ·
                    rfl

theorem cell20_576996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_576996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_576996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_576996 prefixEnd_576996 := by exact prefixLift 576996
  have htrace : WordTrace (prefixWord ++ tailWord_576996) baseStart_576996 baseEnd_576996 := by
    simpa [prefixWord, tailWord_576996, baseEnd_576996] using wordTrace_append hprefix tailTrace_576996
  have hstable : (prefixWord ++ tailWord_576996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_576996).length < 2 ^ (prefixWord ++ tailWord_576996).sum := by decide
  have hdescent : baseEnd_576996 < baseStart_576996 := by decide
  rcases family_descends (prefixWord ++ tailWord_576996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577041 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_577041 : Nat := 118140960795 + 577041 * 2 ^ 59
def prefixEnd_577041 : Nat := 4983230072969 + 3 ^ 40 * 577041 * 2
def baseEnd_577041 : Nat := 263377235867717385007771

theorem tailTrace_577041 : CollatzResearch.WordTrace tailWord_577041 prefixEnd_577041 263377235867717385007771 := by
  unfold tailWord_577041
  simp only [CollatzResearch.WordTrace]
  refine ⟨21046414302486482601882977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 14030942868324321734588651 21046414302486482601882977)
  ·
    refine ⟨15784810726864861951412233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21046414302486482601882977 15784810726864861951412233)
    ·
      refine ⟨11838608045148646463559175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15784810726864861951412233 11838608045148646463559175)
      ·
        refine ⟨17757912067722969695338763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11838608045148646463559175 17757912067722969695338763)
        ·
          refine ⟨26636868101584454543008145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17757912067722969695338763 26636868101584454543008145)
          ·
            refine ⟨19977651076188340907256109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26636868101584454543008145 19977651076188340907256109)
            ·
              refine ⟨7491619153570627840221041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19977651076188340907256109 7491619153570627840221041)
              ·
                refine ⟨5618714365177970880165781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7491619153570627840221041 5618714365177970880165781)
                ·
                  refine ⟨263377235867717385007771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5618714365177970880165781 263377235867717385007771)
                  ·
                    rfl

theorem cell20_577041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_577041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577041 prefixEnd_577041 := by exact prefixLift 577041
  have htrace : WordTrace (prefixWord ++ tailWord_577041) baseStart_577041 baseEnd_577041 := by
    simpa [prefixWord, tailWord_577041, baseEnd_577041] using wordTrace_append hprefix tailTrace_577041
  have hstable : (prefixWord ++ tailWord_577041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577041).length < 2 ^ (prefixWord ++ tailWord_577041).sum := by decide
  have hdescent : baseEnd_577041 < baseStart_577041 := by decide
  rcases family_descends (prefixWord ++ tailWord_577041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577058 : List Nat := [3, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_577058 : Nat := 118140960795 + 577058 * 2 ^ 59
def prefixEnd_577058 : Nat := 4983230072969 + 3 ^ 40 * 577058 * 2
def baseEnd_577058 : Nat := 263384995130940881441035

theorem tailTrace_577058 : CollatzResearch.WordTrace tailWord_577058 prefixEnd_577058 263384995130940881441035 := by
  unfold tailWord_577058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5261758585856223626312957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 14031356228949929670167885 5261758585856223626312957)
  ·
    refine ⟨1973159469696083859867359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5261758585856223626312957 1973159469696083859867359)
    ·
      refine ⟨2959739204544125789801039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1973159469696083859867359 2959739204544125789801039)
      ·
        refine ⟨4439608806816188684701559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2959739204544125789801039 4439608806816188684701559)
        ·
          refine ⟨6659413210224283027052339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4439608806816188684701559 6659413210224283027052339)
          ·
            refine ⟨9989119815336424540578509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6659413210224283027052339 9989119815336424540578509)
            ·
              refine ⟨3745919930751159202716941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9989119815336424540578509 3745919930751159202716941)
              ·
                refine ⟨1404719974031684701018853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3745919930751159202716941 1404719974031684701018853)
                ·
                  refine ⟨263384995130940881441035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1404719974031684701018853 263384995130940881441035)
                  ·
                    rfl

theorem cell20_577058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_577058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577058 prefixEnd_577058 := by exact prefixLift 577058
  have htrace : WordTrace (prefixWord ++ tailWord_577058) baseStart_577058 baseEnd_577058 := by
    simpa [prefixWord, tailWord_577058, baseEnd_577058] using wordTrace_append hprefix tailTrace_577058
  have hstable : (prefixWord ++ tailWord_577058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577058).length < 2 ^ (prefixWord ++ tailWord_577058).sum := by decide
  have hdescent : baseEnd_577058 < baseStart_577058 := by decide
  rcases family_descends (prefixWord ++ tailWord_577058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577078 : List Nat := [5, 1, 2, 1, 3, 2, 2, 4]
def baseStart_577078 : Nat := 118140960795 + 577078 * 2 ^ 59
def prefixEnd_577078 : Nat := 4983230072969 + 3 ^ 40 * 577078 * 2
def baseEnd_577078 : Nat := 87798041225303233591429

theorem tailTrace_577078 : CollatzResearch.WordTrace tailWord_577078 prefixEnd_577078 87798041225303233591429 := by
  unfold tailWord_577078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1315485237709527370061243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 14031842535568291947319925 1315485237709527370061243)
  ·
    refine ⟨1973227856564291055091865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1315485237709527370061243 1973227856564291055091865)
    ·
      refine ⟨1479920892423218291318899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1973227856564291055091865 1479920892423218291318899)
      ·
        refine ⟨2219881338634827436978349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1479920892423218291318899 2219881338634827436978349)
        ·
          refine ⟨832455501988060288866881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2219881338634827436978349 832455501988060288866881)
          ·
            refine ⟨624341626491045216650161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 832455501988060288866881 624341626491045216650161)
            ·
              refine ⟨468256219868283912487621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 624341626491045216650161 468256219868283912487621)
              ·
                refine ⟨87798041225303233591429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 468256219868283912487621 87798041225303233591429)
                ·
                  rfl

theorem cell20_577078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_577078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577078 prefixEnd_577078 := by exact prefixLift 577078
  have htrace : WordTrace (prefixWord ++ tailWord_577078) baseStart_577078 baseEnd_577078 := by
    simpa [prefixWord, tailWord_577078, baseEnd_577078] using wordTrace_append hprefix tailTrace_577078
  have hstable : (prefixWord ++ tailWord_577078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577078).length < 2 ^ (prefixWord ++ tailWord_577078).sum := by decide
  have hdescent : baseEnd_577078 < baseStart_577078 := by decide
  rcases family_descends (prefixWord ++ tailWord_577078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577182 : List Nat := [4, 3, 1, 1, 1, 2, 2, 3, 3]
def baseStart_577182 : Nat := 118140960795 + 577182 * 2 ^ 59
def prefixEnd_577182 : Nat := 4983230072969 + 3 ^ 40 * 577182 * 2
def baseEnd_577182 : Nat := 263441592109747561307195

theorem tailTrace_577182 : CollatzResearch.WordTrace tailWord_577182 prefixEnd_577182 263441592109747561307195 := by
  unfold tailWord_577182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2631444624371957960345725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 14034371329983775788510533 2631444624371957960345725)
  ·
    refine ⟨986791734139484235129647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2631444624371957960345725 986791734139484235129647)
    ·
      refine ⟨1480187601209226352694471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 986791734139484235129647 1480187601209226352694471)
      ·
        refine ⟨2220281401813839529041707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1480187601209226352694471 2220281401813839529041707)
        ·
          refine ⟨3330422102720759293562561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2220281401813839529041707 3330422102720759293562561)
          ·
            refine ⟨2497816577040569470171921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3330422102720759293562561 2497816577040569470171921)
            ·
              refine ⟨1873362432780427102628941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2497816577040569470171921 1873362432780427102628941)
              ·
                refine ⟨702510912292660163485853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1873362432780427102628941 702510912292660163485853)
                ·
                  refine ⟨263441592109747561307195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 702510912292660163485853 263441592109747561307195)
                  ·
                    rfl

theorem cell20_577182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_577182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577182 prefixEnd_577182 := by exact prefixLift 577182
  have htrace : WordTrace (prefixWord ++ tailWord_577182) baseStart_577182 baseEnd_577182 := by
    simpa [prefixWord, tailWord_577182, baseEnd_577182] using wordTrace_append hprefix tailTrace_577182
  have hstable : (prefixWord ++ tailWord_577182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577182).length < 2 ^ (prefixWord ++ tailWord_577182).sum := by decide
  have hdescent : baseEnd_577182 < baseStart_577182 := by decide
  rcases family_descends (prefixWord ++ tailWord_577182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_577200 : List Nat := [2, 1, 1, 1, 2, 1, 4, 8]
def baseStart_577200 : Nat := 118140960795 + 577200 * 2 ^ 59
def prefixEnd_577200 : Nat := 4983230072969 + 3 ^ 40 * 577200 * 2
def baseEnd_577200 : Nat := 87816602600073166235707

theorem tailTrace_577200 : CollatzResearch.WordTrace tailWord_577200 prefixEnd_577200 87816602600073166235707 := by
  unfold tailWord_577200
  simp only [CollatzResearch.WordTrace]
  refine ⟨10526106754455226378460527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 14034809005940301837947369 10526106754455226378460527)
  ·
    refine ⟨15789160131682839567690791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10526106754455226378460527 15789160131682839567690791)
    ·
      refine ⟨23683740197524259351536187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15789160131682839567690791 23683740197524259351536187)
      ·
        refine ⟨35525610296286389027304281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23683740197524259351536187 35525610296286389027304281)
        ·
          refine ⟨26644207722214791770478211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35525610296286389027304281 26644207722214791770478211)
          ·
            refine ⟨39966311583322187655717317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26644207722214791770478211 39966311583322187655717317)
            ·
              refine ⟨7493683421872910185446997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39966311583322187655717317 7493683421872910185446997)
              ·
                refine ⟨87816602600073166235707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7493683421872910185446997 87816602600073166235707)
                ·
                  rfl

theorem cell20_577200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 8].length) (baseStart_577200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_577200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_577200 prefixEnd_577200 := by exact prefixLift 577200
  have htrace : WordTrace (prefixWord ++ tailWord_577200) baseStart_577200 baseEnd_577200 := by
    simpa [prefixWord, tailWord_577200, baseEnd_577200] using wordTrace_append hprefix tailTrace_577200
  have hstable : (prefixWord ++ tailWord_577200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_577200).length < 2 ^ (prefixWord ++ tailWord_577200).sum := by decide
  have hdescent : baseEnd_577200 < baseStart_577200 := by decide
  rcases family_descends (prefixWord ++ tailWord_577200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
