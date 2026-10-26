import V185TrunkScan20Chunk120

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_735201 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 3]
def baseStart_735201 : Nat := 118140960795 + 735201 * 2 ^ 59
def prefixEnd_735201 : Nat := 4983230072969 + 3 ^ 40 * 735201 * 2
def baseEnd_735201 : Nat := 335565769481140672361225

theorem tailTrace_735201 : CollatzResearch.WordTrace tailWord_735201 prefixEnd_735201 335565769481140672361225 := by
  unfold tailWord_735201
  simp only [CollatzResearch.WordTrace]
  refine ⟨26814983409499814179381457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17876655606333209452920971 26814983409499814179381457)
  ·
    refine ⟨20111237557124860634536093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26814983409499814179381457 20111237557124860634536093)
    ·
      refine ⟨7541714083921822737951035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20111237557124860634536093 7541714083921822737951035)
      ·
        refine ⟨11312571125882734106926553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7541714083921822737951035 11312571125882734106926553)
        ·
          refine ⟨8484428344412050580194915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11312571125882734106926553 8484428344412050580194915)
          ·
            refine ⟨12726642516618075870292373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8484428344412050580194915 12726642516618075870292373)
            ·
              refine ⟨596561367966472306419955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12726642516618075870292373 596561367966472306419955)
              ·
                refine ⟨894842051949708459629933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596561367966472306419955 894842051949708459629933)
                ·
                  refine ⟨335565769481140672361225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894842051949708459629933 335565769481140672361225)
                  ·
                    rfl

theorem cell20_735201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_735201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735201 prefixEnd_735201 := by exact prefixLift 735201
  have htrace : WordTrace (prefixWord ++ tailWord_735201) baseStart_735201 baseEnd_735201 := by
    simpa [prefixWord, tailWord_735201, baseEnd_735201] using wordTrace_append hprefix tailTrace_735201
  have hstable : (prefixWord ++ tailWord_735201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735201).length < 2 ^ (prefixWord ++ tailWord_735201).sum := by decide
  have hdescent : baseEnd_735201 < baseStart_735201 := by decide
  rcases family_descends (prefixWord ++ tailWord_735201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735239 : List Nat := [1, 1, 4, 3, 1, 3, 2, 2, 3]
def baseStart_735239 : Nat := 118140960795 + 735239 * 2 ^ 59
def prefixEnd_735239 : Nat := 4983230072969 + 3 ^ 40 * 735239 * 2
def baseEnd_735239 : Nat := 335583113716581429094403

theorem tailTrace_735239 : CollatzResearch.WordTrace tailWord_735239 prefixEnd_735239 335583113716581429094403 := by
  unfold tailWord_735239
  simp only [CollatzResearch.WordTrace]
  refine ⟨26816369383362146669264771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17877579588908097779509847 26816369383362146669264771)
  ·
    refine ⟨40224554075043220003897157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26816369383362146669264771 40224554075043220003897157)
    ·
      refine ⟨7542103889070603750730717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40224554075043220003897157 7542103889070603750730717)
      ·
        refine ⟨2828288958401476406524019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7542103889070603750730717 2828288958401476406524019)
        ·
          refine ⟨4242433437602214609786029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828288958401476406524019 4242433437602214609786029)
          ·
            refine ⟨1590912539100830478669761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4242433437602214609786029 1590912539100830478669761)
            ·
              refine ⟨1193184404325622859002321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590912539100830478669761 1193184404325622859002321)
              ·
                refine ⟨894888303244217144251741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193184404325622859002321 894888303244217144251741)
                ·
                  refine ⟨335583113716581429094403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894888303244217144251741 335583113716581429094403)
                  ·
                    rfl

theorem cell20_735239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_735239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735239 prefixEnd_735239 := by exact prefixLift 735239
  have htrace : WordTrace (prefixWord ++ tailWord_735239) baseStart_735239 baseEnd_735239 := by
    simpa [prefixWord, tailWord_735239, baseEnd_735239] using wordTrace_append hprefix tailTrace_735239
  have hstable : (prefixWord ++ tailWord_735239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735239).length < 2 ^ (prefixWord ++ tailWord_735239).sum := by decide
  have hdescent : baseEnd_735239 < baseStart_735239 := by decide
  rcases family_descends (prefixWord ++ tailWord_735239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735245 : List Nat := [1, 7, 1, 2, 2, 1, 1, 5]
def baseStart_735245 : Nat := 118140960795 + 735245 * 2 ^ 59
def prefixEnd_735245 : Nat := 4983230072969 + 3 ^ 40 * 735245 * 2
def baseEnd_735245 : Nat := 111861950760024024964793

theorem tailTrace_735245 : CollatzResearch.WordTrace tailWord_735245 prefixEnd_735245 111861950760024024964793 := by
  unfold tailWord_735245
  simp only [CollatzResearch.WordTrace]
  refine ⟨26816588221340409693983189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17877725480893606462655459 26816588221340409693983189)
  ·
    refine ⟨628513786437665852202731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 26816588221340409693983189 628513786437665852202731)
    ·
      refine ⟨942770679656498778304097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628513786437665852202731 942770679656498778304097)
      ·
        refine ⟨707078009742374083728073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 942770679656498778304097 707078009742374083728073)
        ·
          refine ⟨530308507306780562796055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707078009742374083728073 530308507306780562796055)
          ·
            refine ⟨795462760960170844194083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530308507306780562796055 795462760960170844194083)
            ·
              refine ⟨1193194141440256266291125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795462760960170844194083 1193194141440256266291125)
              ·
                refine ⟨111861950760024024964793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1193194141440256266291125 111861950760024024964793)
                ·
                  rfl

theorem cell20_735245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5].length) (baseStart_735245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735245 prefixEnd_735245 := by exact prefixLift 735245
  have htrace : WordTrace (prefixWord ++ tailWord_735245) baseStart_735245 baseEnd_735245 := by
    simpa [prefixWord, tailWord_735245, baseEnd_735245] using wordTrace_append hprefix tailTrace_735245
  have hstable : (prefixWord ++ tailWord_735245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735245).length < 2 ^ (prefixWord ++ tailWord_735245).sum := by decide
  have hdescent : baseEnd_735245 < baseStart_735245 := by decide
  rcases family_descends (prefixWord ++ tailWord_735245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735267 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 4]
def baseStart_735267 : Nat := 118140960795 + 735267 * 2 ^ 59
def prefixEnd_735267 : Nat := 4983230072969 + 3 ^ 40 * 735267 * 2
def baseEnd_735267 : Nat := 335595893679537776160955

theorem tailTrace_735267 : CollatzResearch.WordTrace tailWord_735267 prefixEnd_735267 335595893679537776160955 := by
  unfold tailWord_735267
  simp only [CollatzResearch.WordTrace]
  refine ⟨26817390627260707451284055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17878260418173804967522703 26817390627260707451284055)
  ·
    refine ⟨40226085940891061176926083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26817390627260707451284055 40226085940891061176926083)
    ·
      refine ⟨60339128911336591765389125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40226085940891061176926083 60339128911336591765389125)
      ·
        refine ⟨11313586670875610956010461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60339128911336591765389125 11313586670875610956010461)
        ·
          refine ⟨4242595001578354108503923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11313586670875610956010461 4242595001578354108503923)
          ·
            refine ⟨6363892502367531162755885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242595001578354108503923 6363892502367531162755885)
            ·
              refine ⟨2386459688387824186033457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6363892502367531162755885 2386459688387824186033457)
              ·
                refine ⟨1789844766290868139525093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386459688387824186033457 1789844766290868139525093)
                ·
                  refine ⟨335595893679537776160955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789844766290868139525093 335595893679537776160955)
                  ·
                    rfl

theorem cell20_735267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 4].length) (baseStart_735267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735267 prefixEnd_735267 := by exact prefixLift 735267
  have htrace : WordTrace (prefixWord ++ tailWord_735267) baseStart_735267 baseEnd_735267 := by
    simpa [prefixWord, tailWord_735267, baseEnd_735267] using wordTrace_append hprefix tailTrace_735267
  have hstable : (prefixWord ++ tailWord_735267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735267).length < 2 ^ (prefixWord ++ tailWord_735267).sum := by decide
  have hdescent : baseEnd_735267 < baseStart_735267 := by decide
  rcases family_descends (prefixWord ++ tailWord_735267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735305 : List Nat := [1, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_735305 : Nat := 118140960795 + 735305 * 2 ^ 59
def prefixEnd_735305 : Nat := 4983230072969 + 3 ^ 40 * 735305 * 2
def baseEnd_735305 : Nat := 335613237914978532894133

theorem tailTrace_735305 : CollatzResearch.WordTrace tailWord_735305 prefixEnd_735305 335613237914978532894133 := by
  unfold tailWord_735305
  simp only [CollatzResearch.WordTrace]
  refine ⟨26818776601123039941167369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17879184400748693294111579 26818776601123039941167369)
  ·
    refine ⟨20114082450842279955875527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26818776601123039941167369 20114082450842279955875527)
    ·
      refine ⟨30171123676263419933813291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20114082450842279955875527 30171123676263419933813291)
      ·
        refine ⟨45256685514395129900719937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30171123676263419933813291 45256685514395129900719937)
        ·
          refine ⟨33942514135796347425539953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45256685514395129900719937 33942514135796347425539953)
          ·
            refine ⟨25456885601847260569154965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33942514135796347425539953 25456885601847260569154965)
            ·
              refine ⟨1193291512586590339179139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25456885601847260569154965 1193291512586590339179139)
              ·
                refine ⟨1789937268879885508768709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193291512586590339179139 1789937268879885508768709)
                ·
                  refine ⟨335613237914978532894133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1789937268879885508768709 335613237914978532894133)
                  ·
                    rfl

theorem cell20_735305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_735305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735305 prefixEnd_735305 := by exact prefixLift 735305
  have htrace : WordTrace (prefixWord ++ tailWord_735305) baseStart_735305 baseEnd_735305 := by
    simpa [prefixWord, tailWord_735305, baseEnd_735305] using wordTrace_append hprefix tailTrace_735305
  have hstable : (prefixWord ++ tailWord_735305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735305).length < 2 ^ (prefixWord ++ tailWord_735305).sum := by decide
  have hdescent : baseEnd_735305 < baseStart_735305 := by decide
  rcases family_descends (prefixWord ++ tailWord_735305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735325 : List Nat := [1, 4, 4, 1, 1, 3, 2, 4]
def baseStart_735325 : Nat := 118140960795 + 735325 * 2 ^ 59
def prefixEnd_735325 : Nat := 4983230072969 + 3 ^ 40 * 735325 * 2
def baseEnd_735325 : Nat := 111874122153315784075795

theorem tailTrace_735325 : CollatzResearch.WordTrace tailWord_735325 prefixEnd_735325 111874122153315784075795 := by
  unfold tailWord_735325
  simp only [CollatzResearch.WordTrace]
  refine ⟨26819506061050583356895429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17879670707367055571263619 26819506061050583356895429)
  ·
    refine ⟨5028657386446984379417893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26819506061050583356895429 5028657386446984379417893)
    ·
      refine ⟨942873259958809571140855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5028657386446984379417893 942873259958809571140855)
      ·
        refine ⟨1414309889938214356711283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942873259958809571140855 1414309889938214356711283)
        ·
          refine ⟨2121464834907321535066925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414309889938214356711283 2121464834907321535066925)
          ·
            refine ⟨795549313090245575650097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2121464834907321535066925 795549313090245575650097)
            ·
              refine ⟨596661984817684181737573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795549313090245575650097 596661984817684181737573)
              ·
                refine ⟨111874122153315784075795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596661984817684181737573 111874122153315784075795)
                ·
                  rfl

theorem cell20_735325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 4].length) (baseStart_735325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735325 prefixEnd_735325 := by exact prefixLift 735325
  have htrace : WordTrace (prefixWord ++ tailWord_735325) baseStart_735325 baseEnd_735325 := by
    simpa [prefixWord, tailWord_735325, baseEnd_735325] using wordTrace_append hprefix tailTrace_735325
  have hstable : (prefixWord ++ tailWord_735325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735325).length < 2 ^ (prefixWord ++ tailWord_735325).sum := by decide
  have hdescent : baseEnd_735325 < baseStart_735325 := by decide
  rcases family_descends (prefixWord ++ tailWord_735325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735370 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 3]
def baseStart_735370 : Nat := 118140960795 + 735370 * 2 ^ 59
def prefixEnd_735370 : Nat := 4983230072969 + 3 ^ 40 * 735370 * 2
def baseEnd_735370 : Nat := 335642905686127195727201

theorem tailTrace_735370 : CollatzResearch.WordTrace tailWord_735370 prefixEnd_735370 335642905686127195727201 := by
  unfold tailWord_735370
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705286836471889010570891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17880764897258370694855709 6705286836471889010570891)
  ·
    refine ⟨10057930254707833515856337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6705286836471889010570891 10057930254707833515856337)
    ·
      refine ⟨7543447691030875136892253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10057930254707833515856337 7543447691030875136892253)
      ·
        refine ⟨2828792884136578176334595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7543447691030875136892253 2828792884136578176334595)
        ·
          refine ⟨4243189326204867264501893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828792884136578176334595 4243189326204867264501893)
          ·
            refine ⟨795597998663412612094105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4243189326204867264501893 795597998663412612094105)
            ·
              refine ⟨596698498997559459070579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795597998663412612094105 596698498997559459070579)
              ·
                refine ⟨895047748496339188605869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596698498997559459070579 895047748496339188605869)
                ·
                  refine ⟨335642905686127195727201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895047748496339188605869 335642905686127195727201)
                  ·
                    rfl

theorem cell20_735370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 3].length) (baseStart_735370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735370 prefixEnd_735370 := by exact prefixLift 735370
  have htrace : WordTrace (prefixWord ++ tailWord_735370) baseStart_735370 baseEnd_735370 := by
    simpa [prefixWord, tailWord_735370, baseEnd_735370] using wordTrace_append hprefix tailTrace_735370
  have hstable : (prefixWord ++ tailWord_735370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735370).length < 2 ^ (prefixWord ++ tailWord_735370).sum := by decide
  have hdescent : baseEnd_735370 < baseStart_735370 := by decide
  rcases family_descends (prefixWord ++ tailWord_735370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735388 : List Nat := [2, 2, 3, 2, 1, 1, 1, 8]
def baseStart_735388 : Nat := 118140960795 + 735388 * 2 ^ 59
def prefixEnd_735388 : Nat := 4983230072969 + 3 ^ 40 * 735388 * 2
def baseEnd_735388 : Nat := 111883707125533044375709

theorem tailTrace_735388 : CollatzResearch.WordTrace tailWord_735388 prefixEnd_735388 111883707125533044375709 := by
  unfold tailWord_735388
  simp only [CollatzResearch.WordTrace]
  refine ⟨13410901929911172558219409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17881202573214896744292545 13410901929911172558219409)
  ·
    refine ⟨10058176447433379418664557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13410901929911172558219409 10058176447433379418664557)
    ·
      refine ⟨3771816167787517281999209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10058176447433379418664557 3771816167787517281999209)
      ·
        refine ⟨2828862125840637961499407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3771816167787517281999209 2828862125840637961499407)
        ·
          refine ⟨4243293188760956942249111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828862125840637961499407 4243293188760956942249111)
          ·
            refine ⟨6364939783141435413373667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243293188760956942249111 6364939783141435413373667)
            ·
              refine ⟨9547409674712153120060501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364939783141435413373667 9547409674712153120060501)
              ·
                refine ⟨111883707125533044375709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9547409674712153120060501 111883707125533044375709)
                ·
                  rfl

theorem cell20_735388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_735388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735388 prefixEnd_735388 := by exact prefixLift 735388
  have htrace : WordTrace (prefixWord ++ tailWord_735388) baseStart_735388 baseEnd_735388 := by
    simpa [prefixWord, tailWord_735388, baseEnd_735388] using wordTrace_append hprefix tailTrace_735388
  have hstable : (prefixWord ++ tailWord_735388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735388).length < 2 ^ (prefixWord ++ tailWord_735388).sum := by decide
  have hdescent : baseEnd_735388 < baseStart_735388 := by decide
  rcases family_descends (prefixWord ++ tailWord_735388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735415 : List Nat := [1, 1, 3, 1, 4, 2, 4, 2, 2]
def baseStart_735415 : Nat := 118140960795 + 735415 * 2 ^ 59
def prefixEnd_735415 : Nat := 4983230072969 + 3 ^ 40 * 735415 * 2
def baseEnd_735415 : Nat := 335663444912307039227017

theorem tailTrace_735415 : CollatzResearch.WordTrace tailWord_735415 prefixEnd_735415 335663444912307039227017 := by
  unfold tailWord_735415
  simp only [CollatzResearch.WordTrace]
  refine ⟨26822788630724528727671699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17881859087149685818447799 26822788630724528727671699)
  ·
    refine ⟨40234182946086793091507549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26822788630724528727671699 40234182946086793091507549)
    ·
      refine ⟨15087818604782547409315331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40234182946086793091507549 15087818604782547409315331)
      ·
        refine ⟨22631727907173821113972997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15087818604782547409315331 22631727907173821113972997)
        ·
          refine ⟨4243448982595091458869937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22631727907173821113972997 4243448982595091458869937)
          ·
            refine ⟨3182586736946318594152453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4243448982595091458869937 3182586736946318594152453)
            ·
              refine ⟨596735013177434736403585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3182586736946318594152453 596735013177434736403585)
              ·
                refine ⟨447551259883076052302689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596735013177434736403585 447551259883076052302689)
                ·
                  refine ⟨335663444912307039227017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447551259883076052302689 335663444912307039227017)
                  ·
                    rfl

theorem cell20_735415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 2].length) (baseStart_735415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735415 prefixEnd_735415 := by exact prefixLift 735415
  have htrace : WordTrace (prefixWord ++ tailWord_735415) baseStart_735415 baseEnd_735415 := by
    simpa [prefixWord, tailWord_735415, baseEnd_735415] using wordTrace_append hprefix tailTrace_735415
  have hstable : (prefixWord ++ tailWord_735415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735415).length < 2 ^ (prefixWord ++ tailWord_735415).sum := by decide
  have hdescent : baseEnd_735415 < baseStart_735415 := by decide
  rcases family_descends (prefixWord ++ tailWord_735415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735422 : List Nat := [4, 2, 1, 1, 4, 2, 1, 5]
def baseStart_735422 : Nat := 118140960795 + 735422 * 2 ^ 59
def prefixEnd_735422 : Nat := 4983230072969 + 3 ^ 40 * 735422 * 2
def baseEnd_735422 : Nat := 111888879967682041997885

theorem tailTrace_735422 : CollatzResearch.WordTrace tailWord_735422 prefixEnd_735422 111888879967682041997885 := by
  unfold tailWord_735422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352880492712396115397065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17882029294466112615451013 3352880492712396115397065)
  ·
    refine ⟨2514660369534297086547799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3352880492712396115397065 2514660369534297086547799)
    ·
      refine ⟨3771990554301445629821699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2514660369534297086547799 3771990554301445629821699)
      ·
        refine ⟨5657985831452168444732549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771990554301445629821699 5657985831452168444732549)
        ·
          refine ⟨1060872343397281583387353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5657985831452168444732549 1060872343397281583387353)
          ·
            refine ⟨795654257547961187540515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060872343397281583387353 795654257547961187540515)
            ·
              refine ⟨1193481386321941781310773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795654257547961187540515 1193481386321941781310773)
              ·
                refine ⟨111888879967682041997885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1193481386321941781310773 111888879967682041997885)
                ·
                  rfl

theorem cell20_735422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_735422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735422 prefixEnd_735422 := by exact prefixLift 735422
  have htrace : WordTrace (prefixWord ++ tailWord_735422) baseStart_735422 baseEnd_735422 := by
    simpa [prefixWord, tailWord_735422, baseEnd_735422] using wordTrace_append hprefix tailTrace_735422
  have hstable : (prefixWord ++ tailWord_735422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735422).length < 2 ^ (prefixWord ++ tailWord_735422).sum := by decide
  have hdescent : baseEnd_735422 < baseStart_735422 := by decide
  rcases family_descends (prefixWord ++ tailWord_735422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735453 : List Nat := [1, 4, 3, 2, 1, 1, 1, 5, 2]
def baseStart_735453 : Nat := 118140960795 + 735453 * 2 ^ 59
def prefixEnd_735453 : Nat := 4983230072969 + 3 ^ 40 * 735453 * 2
def baseEnd_735453 : Nat := 335680789147747795960195

theorem tailTrace_735453 : CollatzResearch.WordTrace tailWord_735453 prefixEnd_735453 335680789147747795960195 := by
  unfold tailWord_735453
  simp only [CollatzResearch.WordTrace]
  refine ⟨26824174604586861217555013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17882783069724574145036675 26824174604586861217555013)
  ·
    refine ⟨5029532738360036478291565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26824174604586861217555013 5029532738360036478291565)
    ·
      refine ⟨1886074776885013679359337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5029532738360036478291565 1886074776885013679359337)
      ·
        refine ⟨1414556082663760259519503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1886074776885013679359337 1414556082663760259519503)
        ·
          refine ⟨2121834123995640389279255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414556082663760259519503 2121834123995640389279255)
          ·
            refine ⟨3182751185993460583918883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121834123995640389279255 3182751185993460583918883)
            ·
              refine ⟨4774126778990190875878325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182751185993460583918883 4774126778990190875878325)
              ·
                refine ⟨447574385530330394613593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4774126778990190875878325 447574385530330394613593)
                ·
                  refine ⟨335680789147747795960195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447574385530330394613593 335680789147747795960195)
                  ·
                    rfl

theorem cell20_735453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_735453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735453 prefixEnd_735453 := by exact prefixLift 735453
  have htrace : WordTrace (prefixWord ++ tailWord_735453) baseStart_735453 baseEnd_735453 := by
    simpa [prefixWord, tailWord_735453, baseEnd_735453] using wordTrace_append hprefix tailTrace_735453
  have hstable : (prefixWord ++ tailWord_735453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735453).length < 2 ^ (prefixWord ++ tailWord_735453).sum := by decide
  have hdescent : baseEnd_735453 < baseStart_735453 := by decide
  rcases family_descends (prefixWord ++ tailWord_735453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735464 : List Nat := [2, 1, 4, 1, 2, 3, 7]
def baseStart_735464 : Nat := 118140960795 + 735464 * 2 ^ 59
def prefixEnd_735464 : Nat := 4983230072969 + 3 ^ 40 * 735464 * 2
def baseEnd_735464 : Nat := 37298423316386738510387

theorem tailTrace_735464 : CollatzResearch.WordTrace tailWord_735464 prefixEnd_735464 37298423316386738510387 := by
  unfold tailWord_735464
  simp only [CollatzResearch.WordTrace]
  refine ⟨13412287903773505048102723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17883050538364673397470297 13412287903773505048102723)
  ·
    refine ⟨20118431855660257572154085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13412287903773505048102723 20118431855660257572154085)
    ·
      refine ⟨3772205972936298294778891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20118431855660257572154085 3772205972936298294778891)
      ·
        refine ⟨5658308959404447442168337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3772205972936298294778891 5658308959404447442168337)
        ·
          refine ⟨4243731719553335581626253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5658308959404447442168337 4243731719553335581626253)
          ·
            refine ⟨1591399394832500843109845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4243731719553335581626253 1591399394832500843109845)
            ·
              refine ⟨37298423316386738510387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1591399394832500843109845 37298423316386738510387)
              ·
                rfl

theorem cell20_735464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 7].length) (baseStart_735464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735464 prefixEnd_735464 := by exact prefixLift 735464
  have htrace : WordTrace (prefixWord ++ tailWord_735464) baseStart_735464 baseEnd_735464 := by
    simpa [prefixWord, tailWord_735464, baseEnd_735464] using wordTrace_append hprefix tailTrace_735464
  have hstable : (prefixWord ++ tailWord_735464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735464).length < 2 ^ (prefixWord ++ tailWord_735464).sum := by decide
  have hdescent : baseEnd_735464 < baseStart_735464 := by decide
  rcases family_descends (prefixWord ++ tailWord_735464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735474 : List Nat := [3, 2, 1, 3, 2, 2, 2, 1, 4]
def baseStart_735474 : Nat := 118140960795 + 735474 * 2 ^ 59
def prefixEnd_735474 : Nat := 4983230072969 + 3 ^ 40 * 735474 * 2
def baseEnd_735474 : Nat := 335690374119965056260109

theorem tailTrace_735474 : CollatzResearch.WordTrace tailWord_735474 prefixEnd_735474 335690374119965056260109 := by
  unfold tailWord_735474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6706235134377695451017369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17883293691673854536046317 6706235134377695451017369)
  ·
    refine ⟨5029676350783271588263027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6706235134377695451017369 5029676350783271588263027)
    ·
      refine ⟨7544514526174907382394541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029676350783271588263027 7544514526174907382394541)
      ·
        refine ⟨2829192947315590268397953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7544514526174907382394541 2829192947315590268397953)
        ·
          refine ⟨2121894710486692701298465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2829192947315590268397953 2121894710486692701298465)
          ·
            refine ⟨1591421032865019525973849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2121894710486692701298465 1591421032865019525973849)
            ·
              refine ⟨1193565774648764644480387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591421032865019525973849 1193565774648764644480387)
              ·
                refine ⟨1790348661973146966720581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193565774648764644480387 1790348661973146966720581)
                ·
                  refine ⟨335690374119965056260109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1790348661973146966720581 335690374119965056260109)
                  ·
                    rfl

theorem cell20_735474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_735474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735474 prefixEnd_735474 := by exact prefixLift 735474
  have htrace : WordTrace (prefixWord ++ tailWord_735474) baseStart_735474 baseEnd_735474 := by
    simpa [prefixWord, tailWord_735474, baseEnd_735474] using wordTrace_append hprefix tailTrace_735474
  have hstable : (prefixWord ++ tailWord_735474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735474).length < 2 ^ (prefixWord ++ tailWord_735474).sum := by decide
  have hdescent : baseEnd_735474 < baseStart_735474 := by decide
  rcases family_descends (prefixWord ++ tailWord_735474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735502 : List Nat := [4, 1, 1, 2, 1, 2, 3, 6]
def baseStart_735502 : Nat := 118140960795 + 735502 * 2 ^ 59
def prefixEnd_735502 : Nat := 4983230072969 + 3 ^ 40 * 735502 * 2
def baseEnd_735502 : Nat := 111901051360973801108887

theorem tailTrace_735502 : CollatzResearch.WordTrace tailWord_735502 prefixEnd_735502 111901051360973801108887 := by
  unfold tailWord_735502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3353245222676167823261095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17883974520939561724059173 3353245222676167823261095)
  ·
    refine ⟨5029867834014251734891643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3353245222676167823261095 5029867834014251734891643)
    ·
      refine ⟨7544801751021377602337465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029867834014251734891643 7544801751021377602337465)
      ·
        refine ⟨5658601313266033201753099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7544801751021377602337465 5658601313266033201753099)
        ·
          refine ⟨8487901969899049802629649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5658601313266033201753099 8487901969899049802629649)
          ·
            refine ⟨6365926477424287351972237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8487901969899049802629649 6365926477424287351972237)
            ·
              refine ⟨2387222429034107756989589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6365926477424287351972237 2387222429034107756989589)
              ·
                refine ⟨111901051360973801108887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2387222429034107756989589 111901051360973801108887)
                ·
                  rfl

theorem cell20_735502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_735502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735502 prefixEnd_735502 := by exact prefixLift 735502
  have htrace : WordTrace (prefixWord ++ tailWord_735502) baseStart_735502 baseEnd_735502 := by
    simpa [prefixWord, tailWord_735502, baseEnd_735502] using wordTrace_append hprefix tailTrace_735502
  have hstable : (prefixWord ++ tailWord_735502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735502).length < 2 ^ (prefixWord ++ tailWord_735502).sum := by decide
  have hdescent : baseEnd_735502 < baseStart_735502 := by decide
  rcases family_descends (prefixWord ++ tailWord_735502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735509 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_735509 : Nat := 118140960795 + 735509 * 2 ^ 59
def prefixEnd_735509 : Nat := 4983230072969 + 3 ^ 40 * 735509 * 2
def baseEnd_735509 : Nat := 335706349073660490093299

theorem tailTrace_735509 : CollatzResearch.WordTrace tailWord_735509 prefixEnd_735509 335706349073660490093299 := by
  unfold tailWord_735509
  simp only [CollatzResearch.WordTrace]
  refine ⟨26826217092383982781593581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17884144728255988521062387 26826217092383982781593581)
  ·
    refine ⟨10059831409643993543097593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26826217092383982781593581 10059831409643993543097593)
    ·
      refine ⟨7544873557232995157323195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10059831409643993543097593 7544873557232995157323195)
      ·
        refine ⟨11317310335849492735984793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7544873557232995157323195 11317310335849492735984793)
        ·
          refine ⟨8487982751887119551988595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11317310335849492735984793 8487982751887119551988595)
          ·
            refine ⟨12731974127830679327982893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487982751887119551988595 12731974127830679327982893)
            ·
              refine ⟨4774490297936504747993585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12731974127830679327982893 4774490297936504747993585)
              ·
                refine ⟨3580867723452378560995189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4774490297936504747993585 3580867723452378560995189)
                ·
                  refine ⟨335706349073660490093299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3580867723452378560995189 335706349073660490093299)
                  ·
                    rfl

theorem cell20_735509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_735509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735509 prefixEnd_735509 := by exact prefixLift 735509
  have htrace : WordTrace (prefixWord ++ tailWord_735509) baseStart_735509 baseEnd_735509 := by
    simpa [prefixWord, tailWord_735509, baseEnd_735509] using wordTrace_append hprefix tailTrace_735509
  have hstable : (prefixWord ++ tailWord_735509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735509).length < 2 ^ (prefixWord ++ tailWord_735509).sum := by decide
  have hdescent : baseEnd_735509 < baseStart_735509 := by decide
  rcases family_descends (prefixWord ++ tailWord_735509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735580 : List Nat := [2, 2, 4, 3, 2, 1, 2, 2, 2]
def baseStart_735580 : Nat := 118140960795 + 735580 * 2 ^ 59
def prefixEnd_735580 : Nat := 4983230072969 + 3 ^ 40 * 735580 * 2
def baseEnd_735580 : Nat := 335738755408299798726343

theorem tailTrace_735580 : CollatzResearch.WordTrace tailWord_735580 prefixEnd_735580 335738755408299798726343 := by
  unfold tailWord_735580
  simp only [CollatzResearch.WordTrace]
  refine ⟨13414403337563380953714097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17885871116751174604952129 13414403337563380953714097)
  ·
    refine ⟨10060802503172535715285573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13414403337563380953714097 10060802503172535715285573)
    ·
      refine ⟨1886400469344850446616045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10060802503172535715285573 1886400469344850446616045)
      ·
        refine ⟨707400176004318917481017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1886400469344850446616045 707400176004318917481017)
        ·
          refine ⟨530550132003239188110763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707400176004318917481017 530550132003239188110763)
          ·
            refine ⟨795825198004858782166145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530550132003239188110763 795825198004858782166145)
            ·
              refine ⟨596868898503644086624609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795825198004858782166145 596868898503644086624609)
              ·
                refine ⟨447651673877733064968457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596868898503644086624609 447651673877733064968457)
                ·
                  refine ⟨335738755408299798726343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447651673877733064968457 335738755408299798726343)
                  ·
                    rfl

theorem cell20_735580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_735580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735580 prefixEnd_735580 := by exact prefixLift 735580
  have htrace : WordTrace (prefixWord ++ tailWord_735580) baseStart_735580 baseEnd_735580 := by
    simpa [prefixWord, tailWord_735580, baseEnd_735580] using wordTrace_append hprefix tailTrace_735580
  have hstable : (prefixWord ++ tailWord_735580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735580).length < 2 ^ (prefixWord ++ tailWord_735580).sum := by decide
  have hdescent : baseEnd_735580 < baseStart_735580 := by decide
  rcases family_descends (prefixWord ++ tailWord_735580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735584 : List Nat := [2, 1, 1, 3, 5, 2, 2, 2, 2]
def baseStart_735584 : Nat := 118140960795 + 735584 * 2 ^ 59
def prefixEnd_735584 : Nat := 4983230072969 + 3 ^ 40 * 735584 * 2
def baseEnd_735584 : Nat := 335740581117293562592993

theorem tailTrace_735584 : CollatzResearch.WordTrace tailWord_735584 prefixEnd_735584 335740581117293562592993 := by
  unfold tailWord_735584
  simp only [CollatzResearch.WordTrace]
  refine ⟨13414476283556135295286903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17885968378074847060382537 13414476283556135295286903)
  ·
    refine ⟨20121714425334202942930355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13414476283556135295286903 20121714425334202942930355)
    ·
      refine ⟨30182571638001304414395533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20121714425334202942930355 30182571638001304414395533)
      ·
        refine ⟨11318464364250489155398325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30182571638001304414395533 11318464364250489155398325)
        ·
          refine ⟨1061106034148483358318593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11318464364250489155398325 1061106034148483358318593)
          ·
            refine ⟨795829525611362518738945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1061106034148483358318593 795829525611362518738945)
            ·
              refine ⟨596872144208521889054209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795829525611362518738945 596872144208521889054209)
              ·
                refine ⟨447654108156391416790657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 596872144208521889054209 447654108156391416790657)
                ·
                  refine ⟨335740581117293562592993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447654108156391416790657 335740581117293562592993)
                  ·
                    rfl

theorem cell20_735584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_735584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735584 prefixEnd_735584 := by exact prefixLift 735584
  have htrace : WordTrace (prefixWord ++ tailWord_735584) baseStart_735584 baseEnd_735584 := by
    simpa [prefixWord, tailWord_735584, baseEnd_735584] using wordTrace_append hprefix tailTrace_735584
  have hstable : (prefixWord ++ tailWord_735584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735584).length < 2 ^ (prefixWord ++ tailWord_735584).sum := by decide
  have hdescent : baseEnd_735584 < baseStart_735584 := by decide
  rcases family_descends (prefixWord ++ tailWord_735584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735588 : List Nat := [2, 3, 1, 1, 3, 1, 3, 4, 2]
def baseStart_735588 : Nat := 118140960795 + 735588 * 2 ^ 59
def prefixEnd_735588 : Nat := 4983230072969 + 3 ^ 40 * 735588 * 2
def baseEnd_735588 : Nat := 335742406826287326459643

theorem tailTrace_735588 : CollatzResearch.WordTrace tailWord_735588 prefixEnd_735588 335742406826287326459643 := by
  unfold tailWord_735588
  simp only [CollatzResearch.WordTrace]
  refine ⟨13414549229548889636859709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17886065639398519515812945 13414549229548889636859709)
  ·
    refine ⟨5030455961080833613822391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13414549229548889636859709 5030455961080833613822391)
    ·
      refine ⟨7545683941621250420733587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030455961080833613822391 7545683941621250420733587)
      ·
        refine ⟨11318525912431875631100381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7545683941621250420733587 11318525912431875631100381)
        ·
          refine ⟨4244447217161953361662643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11318525912431875631100381 4244447217161953361662643)
          ·
            refine ⟨6366670825742930042493965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244447217161953361662643 6366670825742930042493965)
            ·
              refine ⟨2387501559653598765935237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6366670825742930042493965 2387501559653598765935237)
              ·
                refine ⟨447656542435049768612857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2387501559653598765935237 447656542435049768612857)
                ·
                  refine ⟨335742406826287326459643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447656542435049768612857 335742406826287326459643)
                  ·
                    rfl

theorem cell20_735588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_735588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735588 prefixEnd_735588 := by exact prefixLift 735588
  have htrace : WordTrace (prefixWord ++ tailWord_735588) baseStart_735588 baseEnd_735588 := by
    simpa [prefixWord, tailWord_735588, baseEnd_735588] using wordTrace_append hprefix tailTrace_735588
  have hstable : (prefixWord ++ tailWord_735588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735588).length < 2 ^ (prefixWord ++ tailWord_735588).sum := by decide
  have hdescent : baseEnd_735588 < baseStart_735588 := by decide
  rcases family_descends (prefixWord ++ tailWord_735588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735599 : List Nat := [1, 1, 2, 1, 3, 1, 2, 9]
def baseStart_735599 : Nat := 118140960795 + 735599 * 2 ^ 59
def prefixEnd_735599 : Nat := 4983230072969 + 3 ^ 40 * 735599 * 2
def baseEnd_735599 : Nat := 111915809175340059030977

theorem tailTrace_735599 : CollatzResearch.WordTrace tailWord_735599 prefixEnd_735599 111915809175340059030977 := by
  unfold tailWord_735599
  simp only [CollatzResearch.WordTrace]
  refine ⟨26829499662057928152369851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17886333108038618768246567 26829499662057928152369851)
  ·
    refine ⟨40244249493086892228554777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26829499662057928152369851 40244249493086892228554777)
    ·
      refine ⟨30183187119815169171416083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40244249493086892228554777 30183187119815169171416083)
      ·
        refine ⟨45274780679722753757124125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30183187119815169171416083 45274780679722753757124125)
        ·
          refine ⟨16978042754896032658921547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45274780679722753757124125 16978042754896032658921547)
          ·
            refine ⟨25467064132344048988382321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16978042754896032658921547 25467064132344048988382321)
            ·
              refine ⟨19100298099258036741286741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25467064132344048988382321 19100298099258036741286741)
              ·
                refine ⟨111915809175340059030977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19100298099258036741286741 111915809175340059030977)
                ·
                  rfl

theorem cell20_735599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_735599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735599 prefixEnd_735599 := by exact prefixLift 735599
  have htrace : WordTrace (prefixWord ++ tailWord_735599) baseStart_735599 baseEnd_735599 := by
    simpa [prefixWord, tailWord_735599, baseEnd_735599] using wordTrace_append hprefix tailTrace_735599
  have hstable : (prefixWord ++ tailWord_735599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735599).length < 2 ^ (prefixWord ++ tailWord_735599).sum := by decide
  have hdescent : baseEnd_735599 < baseStart_735599 := by decide
  rcases family_descends (prefixWord ++ tailWord_735599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735602 : List Nat := [3, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_735602 : Nat := 118140960795 + 735602 * 2 ^ 59
def prefixEnd_735602 : Nat := 4983230072969 + 3 ^ 40 * 735602 * 2
def baseEnd_735602 : Nat := 335748796807765499992919

theorem tailTrace_735602 : CollatzResearch.WordTrace tailWord_735602 prefixEnd_735602 335748796807765499992919 := by
  unfold tailWord_735602
  simp only [CollatzResearch.WordTrace]
  refine ⟨6707402270261764916182265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17886406054031373109819373 6707402270261764916182265)
  ·
    refine ⟨5030551702696323687136699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6707402270261764916182265 5030551702696323687136699)
    ·
      refine ⟨7545827554044485530705049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5030551702696323687136699 7545827554044485530705049)
      ·
        refine ⟨5659370665533364148028787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7545827554044485530705049 5659370665533364148028787)
        ·
          refine ⟨8489055998300046222043181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659370665533364148028787 8489055998300046222043181)
          ·
            refine ⟨3183395999362517333266193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8489055998300046222043181 3183395999362517333266193)
            ·
              refine ⟨2387546999521887999949645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3183395999362517333266193 2387546999521887999949645)
              ·
                refine ⟨895330124820707999981117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2387546999521887999949645 895330124820707999981117)
                ·
                  refine ⟨335748796807765499992919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895330124820707999981117 335748796807765499992919)
                  ·
                    rfl

theorem cell20_735602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_735602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735602 prefixEnd_735602 := by exact prefixLift 735602
  have htrace : WordTrace (prefixWord ++ tailWord_735602) baseStart_735602 baseEnd_735602 := by
    simpa [prefixWord, tailWord_735602, baseEnd_735602] using wordTrace_append hprefix tailTrace_735602
  have hstable : (prefixWord ++ tailWord_735602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735602).length < 2 ^ (prefixWord ++ tailWord_735602).sum := by decide
  have hdescent : baseEnd_735602 < baseStart_735602 := by decide
  rcases family_descends (prefixWord ++ tailWord_735602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735623 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_735623 : Nat := 118140960795 + 735623 * 2 ^ 59
def prefixEnd_735623 : Nat := 4983230072969 + 3 ^ 40 * 735623 * 2
def baseEnd_735623 : Nat := 335758381779982760292833

theorem tailTrace_735623 : CollatzResearch.WordTrace tailWord_735623 prefixEnd_735623 335758381779982760292833 := by
  unfold tailWord_735623
  simp only [CollatzResearch.WordTrace]
  refine ⟨26830375013970980251243523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17886916675980653500829015 26830375013970980251243523)
  ·
    refine ⟨40245562520956470376865285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26830375013970980251243523 40245562520956470376865285)
    ·
      refine ⟨7546042972679338195662241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40245562520956470376865285 7546042972679338195662241)
      ·
        refine ⟨5659532229509503646746681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7546042972679338195662241 5659532229509503646746681)
        ·
          refine ⟨4244649172132127735060011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5659532229509503646746681 4244649172132127735060011)
          ·
            refine ⟨6366973758198191602590017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244649172132127735060011 6366973758198191602590017)
            ·
              refine ⟨4775230318648643701942513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6366973758198191602590017 4775230318648643701942513)
              ·
                refine ⟨3581422738986482776456885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4775230318648643701942513 3581422738986482776456885)
                ·
                  refine ⟨335758381779982760292833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3581422738986482776456885 335758381779982760292833)
                  ·
                    rfl

theorem cell20_735623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_735623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735623 prefixEnd_735623 := by exact prefixLift 735623
  have htrace : WordTrace (prefixWord ++ tailWord_735623) baseStart_735623 baseEnd_735623 := by
    simpa [prefixWord, tailWord_735623, baseEnd_735623] using wordTrace_append hprefix tailTrace_735623
  have hstable : (prefixWord ++ tailWord_735623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735623).length < 2 ^ (prefixWord ++ tailWord_735623).sum := by decide
  have hdescent : baseEnd_735623 < baseStart_735623 := by decide
  rcases family_descends (prefixWord ++ tailWord_735623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735636 : List Nat := [2, 4, 2, 1, 3, 2, 1, 2, 3]
def baseStart_735636 : Nat := 118140960795 + 735636 * 2 ^ 59
def prefixEnd_735636 : Nat := 4983230072969 + 3 ^ 40 * 735636 * 2
def baseEnd_735636 : Nat := 335764315334212492859447

theorem tailTrace_735636 : CollatzResearch.WordTrace tailWord_735636 prefixEnd_735636 335764315334212492859447 := by
  unfold tailWord_735636
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415424581461941735733381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17887232775282588980977841 13415424581461941735733381)
  ·
    refine ⟨2515392109024114075450009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13415424581461941735733381 2515392109024114075450009)
    ·
      refine ⟨1886544081768085556587507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2515392109024114075450009 1886544081768085556587507)
      ·
        refine ⟨2829816122652128334881261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886544081768085556587507 2829816122652128334881261)
        ·
          refine ⟨1061181045994548125580473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2829816122652128334881261 1061181045994548125580473)
          ·
            refine ⟨795885784495911094185355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1061181045994548125580473 795885784495911094185355)
            ·
              refine ⟨1193828676743866641278033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795885784495911094185355 1193828676743866641278033)
              ·
                refine ⟨895371507557899980958525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193828676743866641278033 895371507557899980958525)
                ·
                  refine ⟨335764315334212492859447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895371507557899980958525 335764315334212492859447)
                  ·
                    rfl

theorem cell20_735636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_735636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735636 prefixEnd_735636 := by exact prefixLift 735636
  have htrace : WordTrace (prefixWord ++ tailWord_735636) baseStart_735636 baseEnd_735636 := by
    simpa [prefixWord, tailWord_735636, baseEnd_735636] using wordTrace_append hprefix tailTrace_735636
  have hstable : (prefixWord ++ tailWord_735636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735636).length < 2 ^ (prefixWord ++ tailWord_735636).sum := by decide
  have hdescent : baseEnd_735636 < baseStart_735636 := by decide
  rcases family_descends (prefixWord ++ tailWord_735636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735640 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 5]
def baseStart_735640 : Nat := 118140960795 + 735640 * 2 ^ 59
def prefixEnd_735640 : Nat := 4983230072969 + 3 ^ 40 * 735640 * 2
def baseEnd_735640 : Nat := 335766141043206256726097

theorem tailTrace_735640 : CollatzResearch.WordTrace tailWord_735640 prefixEnd_735640 335766141043206256726097 := by
  unfold tailWord_735640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13415497527454696077306187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17887330036606261436408249 13415497527454696077306187)
  ·
    refine ⟨20123246291182044115959281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13415497527454696077306187 20123246291182044115959281)
    ·
      refine ⟨15092434718386533086969461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20123246291182044115959281 15092434718386533086969461)
      ·
        refine ⟨1414915754848737476903387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15092434718386533086969461 1414915754848737476903387)
        ·
          refine ⟨2122373632273106215355081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414915754848737476903387 2122373632273106215355081)
          ·
            refine ⟨1591780224204829661516311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122373632273106215355081 1591780224204829661516311)
            ·
              refine ⟨2387670336307244492274467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591780224204829661516311 2387670336307244492274467)
              ·
                refine ⟨3581505504460866738411701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387670336307244492274467 3581505504460866738411701)
                ·
                  refine ⟨335766141043206256726097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3581505504460866738411701 335766141043206256726097)
                  ·
                    rfl

theorem cell20_735640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_735640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735640 prefixEnd_735640 := by exact prefixLift 735640
  have htrace : WordTrace (prefixWord ++ tailWord_735640) baseStart_735640 baseEnd_735640 := by
    simpa [prefixWord, tailWord_735640, baseEnd_735640] using wordTrace_append hprefix tailTrace_735640
  have hstable : (prefixWord ++ tailWord_735640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735640).length < 2 ^ (prefixWord ++ tailWord_735640).sum := by decide
  have hdescent : baseEnd_735640 < baseStart_735640 := by decide
  rcases family_descends (prefixWord ++ tailWord_735640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735647 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_735647 : Nat := 118140960795 + 735647 * 2 ^ 59
def prefixEnd_735647 : Nat := 4983230072969 + 3 ^ 40 * 735647 * 2
def baseEnd_735647 : Nat := 335769336033945343492735

theorem tailTrace_735647 : CollatzResearch.WordTrace tailWord_735647 prefixEnd_735647 335769336033945343492735 := by
  unfold tailWord_735647
  simp only [CollatzResearch.WordTrace]
  refine ⟨26831250365884032350117195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17887500243922688233411463 26831250365884032350117195)
  ·
    refine ⟨40246875548826048525175793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26831250365884032350117195 40246875548826048525175793)
    ·
      refine ⟨30185156661619536393881845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40246875548826048525175793 30185156661619536393881845)
      ·
        refine ⟨2829858437026831536926423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30185156661619536393881845 2829858437026831536926423)
        ·
          refine ⟨4244787655540247305389635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829858437026831536926423 4244787655540247305389635)
          ·
            refine ⟨6367181483310370958084453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4244787655540247305389635 6367181483310370958084453)
            ·
              refine ⟨1193846528120694554640835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6367181483310370958084453 1193846528120694554640835)
              ·
                refine ⟨1790769792181041831961253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193846528120694554640835 1790769792181041831961253)
                ·
                  refine ⟨335769336033945343492735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1790769792181041831961253 335769336033945343492735)
                  ·
                    rfl

theorem cell20_735647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_735647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735647 prefixEnd_735647 := by exact prefixLift 735647
  have htrace : WordTrace (prefixWord ++ tailWord_735647) baseStart_735647 baseEnd_735647 := by
    simpa [prefixWord, tailWord_735647, baseEnd_735647] using wordTrace_append hprefix tailTrace_735647
  have hstable : (prefixWord ++ tailWord_735647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735647).length < 2 ^ (prefixWord ++ tailWord_735647).sum := by decide
  have hdescent : baseEnd_735647 < baseStart_735647 := by decide
  rcases family_descends (prefixWord ++ tailWord_735647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735671 : List Nat := [1, 1, 3, 1, 3, 5, 2, 4]
def baseStart_735671 : Nat := 118140960795 + 735671 * 2 ^ 59
def prefixEnd_735671 : Nat := 4983230072969 + 3 ^ 40 * 735671 * 2
def baseEnd_735671 : Nat := 111926763429302642230879

theorem tailTrace_735671 : CollatzResearch.WordTrace tailWord_735671 prefixEnd_735671 111926763429302642230879 := by
  unfold tailWord_735671
  simp only [CollatzResearch.WordTrace]
  refine ⟨26832125717797084448990867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17888083811864722965993911 26832125717797084448990867)
  ·
    refine ⟨40248188576695626673486301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26832125717797084448990867 40248188576695626673486301)
    ·
      refine ⟨15093070716260860002557363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40248188576695626673486301 15093070716260860002557363)
      ·
        refine ⟨22639606074391290003836045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15093070716260860002557363 22639606074391290003836045)
        ·
          refine ⟨8489852277896733751438517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22639606074391290003836045 8489852277896733751438517)
          ·
            refine ⟨795923651052818789197361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8489852277896733751438517 795923651052818789197361)
            ·
              refine ⟨596942738289614091898021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795923651052818789197361 596942738289614091898021)
              ·
                refine ⟨111926763429302642230879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 596942738289614091898021 111926763429302642230879)
                ·
                  rfl

theorem cell20_735671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_735671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735671 prefixEnd_735671 := by exact prefixLift 735671
  have htrace : WordTrace (prefixWord ++ tailWord_735671) baseStart_735671 baseEnd_735671 := by
    simpa [prefixWord, tailWord_735671, baseEnd_735671] using wordTrace_append hprefix tailTrace_735671
  have hstable : (prefixWord ++ tailWord_735671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735671).length < 2 ^ (prefixWord ++ tailWord_735671).sum := by decide
  have hdescent : baseEnd_735671 < baseStart_735671 := by decide
  rcases family_descends (prefixWord ++ tailWord_735671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735698 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_735698 : Nat := 118140960795 + 735698 * 2 ^ 59
def prefixEnd_735698 : Nat := 4983230072969 + 3 ^ 40 * 735698 * 2
def baseEnd_735698 : Nat := 335792613823615832792527

theorem tailTrace_735698 : CollatzResearch.WordTrace tailWord_735698 prefixEnd_735698 335792613823615832792527 := by
  unfold tailWord_735698
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708277622174817015055937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17888740325799512040149165 6708277622174817015055937)
  ·
    refine ⟨5031208216631112761291953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6708277622174817015055937 5031208216631112761291953)
    ·
      refine ⟨3773406162473334570968965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5031208216631112761291953 3773406162473334570968965)
      ·
        refine ⟨707513655463750232056681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3773406162473334570968965 707513655463750232056681)
        ·
          refine ⟨530635241597812674042511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707513655463750232056681 530635241597812674042511)
          ·
            refine ⟨795952862396719011063767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530635241597812674042511 795952862396719011063767)
            ·
              refine ⟨1193929293595078516595651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795952862396719011063767 1193929293595078516595651)
              ·
                refine ⟨1790893940392617774893477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193929293595078516595651 1790893940392617774893477)
                ·
                  refine ⟨335792613823615832792527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1790893940392617774893477 335792613823615832792527)
                  ·
                    rfl

theorem cell20_735698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_735698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735698 prefixEnd_735698 := by exact prefixLift 735698
  have htrace : WordTrace (prefixWord ++ tailWord_735698) baseStart_735698 baseEnd_735698 := by
    simpa [prefixWord, tailWord_735698, baseEnd_735698] using wordTrace_append hprefix tailTrace_735698
  have hstable : (prefixWord ++ tailWord_735698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735698).length < 2 ^ (prefixWord ++ tailWord_735698).sum := by decide
  have hdescent : baseEnd_735698 < baseStart_735698 := by decide
  rcases family_descends (prefixWord ++ tailWord_735698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735751 : List Nat := [1, 1, 4, 3, 11]
def baseStart_735751 : Nat := 118140960795 + 735751 * 2 ^ 59
def prefixEnd_735751 : Nat := 4983230072969 + 3 ^ 40 * 735751 * 2
def baseEnd_735751 : Nat := 4145886474910903753403

theorem tailTrace_735751 : CollatzResearch.WordTrace tailWord_735751 prefixEnd_735751 4145886474910903753403 := by
  unfold tailWord_735751
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835043557507258111903107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17890029038338172074602071 26835043557507258111903107)
  ·
    refine ⟨40252565336260887167854661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26835043557507258111903107 40252565336260887167854661)
    ·
      refine ⟨7547356000548916343972749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40252565336260887167854661 7547356000548916343972749)
      ·
        refine ⟨2830258500205843628989781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7547356000548916343972749 2830258500205843628989781)
        ·
          refine ⟨4145886474910903753403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2830258500205843628989781 4145886474910903753403)
          ·
            rfl

theorem cell20_735751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 11].length) (baseStart_735751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735751 prefixEnd_735751 := by exact prefixLift 735751
  have htrace : WordTrace (prefixWord ++ tailWord_735751) baseStart_735751 baseEnd_735751 := by
    simpa [prefixWord, tailWord_735751, baseEnd_735751] using wordTrace_append hprefix tailTrace_735751
  have hstable : (prefixWord ++ tailWord_735751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735751).length < 2 ^ (prefixWord ++ tailWord_735751).sum := by decide
  have hdescent : baseEnd_735751 < baseStart_735751 := by decide
  rcases family_descends (prefixWord ++ tailWord_735751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735754 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_735754 : Nat := 118140960795 + 735754 * 2 ^ 59
def prefixEnd_735754 : Nat := 4983230072969 + 3 ^ 40 * 735754 * 2
def baseEnd_735754 : Nat := 335818173749528526925631

theorem tailTrace_735754 : CollatzResearch.WordTrace tailWord_735754 prefixEnd_735754 335818173749528526925631 := by
  unfold tailWord_735754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708788244124097406065579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17890101984330926416174877 6708788244124097406065579)
  ·
    refine ⟨10063182366186146109098369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6708788244124097406065579 10063182366186146109098369)
    ·
      refine ⟨7547386774639609581823777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10063182366186146109098369 7547386774639609581823777)
      ·
        refine ⟨5660540080979707186367833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7547386774639609581823777 5660540080979707186367833)
        ·
          refine ⟨4245405060734780389775875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5660540080979707186367833 4245405060734780389775875)
          ·
            refine ⟨6368107591102170584663813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245405060734780389775875 6368107591102170584663813)
            ·
              refine ⟨1194020173331656984624465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6368107591102170584663813 1194020173331656984624465)
              ·
                refine ⟨895515129998742738468349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194020173331656984624465 895515129998742738468349)
                ·
                  refine ⟨335818173749528526925631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895515129998742738468349 335818173749528526925631)
                  ·
                    rfl

theorem cell20_735754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_735754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735754 prefixEnd_735754 := by exact prefixLift 735754
  have htrace : WordTrace (prefixWord ++ tailWord_735754) baseStart_735754 baseEnd_735754 := by
    simpa [prefixWord, tailWord_735754, baseEnd_735754] using wordTrace_append hprefix tailTrace_735754
  have hstable : (prefixWord ++ tailWord_735754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735754).length < 2 ^ (prefixWord ++ tailWord_735754).sum := by decide
  have hdescent : baseEnd_735754 < baseStart_735754 := by decide
  rcases family_descends (prefixWord ++ tailWord_735754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735764 : List Nat := [2, 4, 3, 1, 1, 3, 1, 5]
def baseStart_735764 : Nat := 118140960795 + 735764 * 2 ^ 59
def prefixEnd_735764 : Nat := 4983230072969 + 3 ^ 40 * 735764 * 2
def baseEnd_735764 : Nat := 111940912674004312197419

theorem tailTrace_735764 : CollatzResearch.WordTrace tailWord_735764 prefixEnd_735764 111940912674004312197419 := by
  unfold tailWord_735764
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417758853230080666063173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17890345137640107554750897 13417758853230080666063173)
  ·
    refine ⟨2515829784980640124886845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13417758853230080666063173 2515829784980640124886845)
    ·
      refine ⟨943436169367740046832567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2515829784980640124886845 943436169367740046832567)
      ·
        refine ⟨1415154254051610070248851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943436169367740046832567 1415154254051610070248851)
        ·
          refine ⟨2122731381077415105373277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1415154254051610070248851 2122731381077415105373277)
          ·
            refine ⟨796024267904030664514979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2122731381077415105373277 796024267904030664514979)
            ·
              refine ⟨1194036401856045996772469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796024267904030664514979 1194036401856045996772469)
              ·
                refine ⟨111940912674004312197419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194036401856045996772469 111940912674004312197419)
                ·
                  rfl

theorem cell20_735764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_735764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735764 prefixEnd_735764 := by exact prefixLift 735764
  have htrace : WordTrace (prefixWord ++ tailWord_735764) baseStart_735764 baseEnd_735764 := by
    simpa [prefixWord, tailWord_735764, baseEnd_735764] using wordTrace_append hprefix tailTrace_735764
  have hstable : (prefixWord ++ tailWord_735764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735764).length < 2 ^ (prefixWord ++ tailWord_735764).sum := by decide
  have hdescent : baseEnd_735764 < baseStart_735764 := by decide
  rcases family_descends (prefixWord ++ tailWord_735764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735768 : List Nat := [2, 1, 2, 3, 3, 1, 3, 5]
def baseStart_735768 : Nat := 118140960795 + 735768 * 2 ^ 59
def prefixEnd_735768 : Nat := 4983230072969 + 3 ^ 40 * 735768 * 2
def baseEnd_735768 : Nat := 111941521243668900152969

theorem tailTrace_735768 : CollatzResearch.WordTrace tailWord_735768 prefixEnd_735768 111941521243668900152969 := by
  unfold tailWord_735768
  simp only [CollatzResearch.WordTrace]
  refine ⟨13417831799222835007635979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17890442398963780010181305 13417831799222835007635979)
  ·
    refine ⟨20126747698834252511453969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13417831799222835007635979 20126747698834252511453969)
    ·
      refine ⟨15095060774125689383590477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20126747698834252511453969 15095060774125689383590477)
      ·
        refine ⟨5660647790297133518846429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15095060774125689383590477 5660647790297133518846429)
        ·
          refine ⟨2122742921361425069567411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5660647790297133518846429 2122742921361425069567411)
          ·
            refine ⟨3184114382042137604351117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122742921361425069567411 3184114382042137604351117)
            ·
              refine ⟨1194042893265801601631669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3184114382042137604351117 1194042893265801601631669)
              ·
                refine ⟨111941521243668900152969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194042893265801601631669 111941521243668900152969)
                ·
                  rfl

theorem cell20_735768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_735768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735768 prefixEnd_735768 := by exact prefixLift 735768
  have htrace : WordTrace (prefixWord ++ tailWord_735768) baseStart_735768 baseEnd_735768 := by
    simpa [prefixWord, tailWord_735768, baseEnd_735768] using wordTrace_append hprefix tailTrace_735768
  have hstable : (prefixWord ++ tailWord_735768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735768).length < 2 ^ (prefixWord ++ tailWord_735768).sum := by decide
  have hdescent : baseEnd_735768 < baseStart_735768 := by decide
  rcases family_descends (prefixWord ++ tailWord_735768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735809 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 3]
def baseStart_735809 : Nat := 118140960795 + 735809 * 2 ^ 59
def prefixEnd_735809 : Nat := 4983230072969 + 3 ^ 40 * 735809 * 2
def baseEnd_735809 : Nat := 335843277248192780092073

theorem tailTrace_735809 : CollatzResearch.WordTrace tailWord_735809 prefixEnd_735809 335843277248192780092073 := by
  unfold tailWord_735809
  simp only [CollatzResearch.WordTrace]
  refine ⟨26837158991297134017514481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17891439327531422678342987 26837158991297134017514481)
  ·
    refine ⟨20127869243472850513135861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26837158991297134017514481 20127869243472850513135861)
    ·
      refine ⟨1886987741575579735606487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20127869243472850513135861 1886987741575579735606487)
      ·
        refine ⟨2830481612363369603409731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886987741575579735606487 2830481612363369603409731)
        ·
          refine ⟨4245722418545054405114597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830481612363369603409731 4245722418545054405114597)
          ·
            refine ⟨796072953477197700958987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4245722418545054405114597 796072953477197700958987)
            ·
              refine ⟨1194109430215796551438481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796072953477197700958987 1194109430215796551438481)
              ·
                refine ⟨895582072661847413578861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194109430215796551438481 895582072661847413578861)
                ·
                  refine ⟨335843277248192780092073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895582072661847413578861 335843277248192780092073)
                  ·
                    rfl

theorem cell20_735809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_735809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735809 prefixEnd_735809 := by exact prefixLift 735809
  have htrace : WordTrace (prefixWord ++ tailWord_735809) baseStart_735809 baseEnd_735809 := by
    simpa [prefixWord, tailWord_735809, baseEnd_735809] using wordTrace_append hprefix tailTrace_735809
  have hstable : (prefixWord ++ tailWord_735809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735809).length < 2 ^ (prefixWord ++ tailWord_735809).sum := by decide
  have hdescent : baseEnd_735809 < baseStart_735809 := by decide
  rcases family_descends (prefixWord ++ tailWord_735809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735812 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 4]
def baseStart_735812 : Nat := 118140960795 + 735812 * 2 ^ 59
def prefixEnd_735812 : Nat := 4983230072969 + 3 ^ 40 * 735812 * 2
def baseEnd_735812 : Nat := 335844646529938102992061

theorem tailTrace_735812 : CollatzResearch.WordTrace tailWord_735812 prefixEnd_735812 335844646529938102992061 := by
  unfold tailWord_735812
  simp only [CollatzResearch.WordTrace]
  refine ⟨13418634205143132764936845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17891512273524177019915793 13418634205143132764936845)
  ·
    refine ⟨5031987826928674786851317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13418634205143132764936845 5031987826928674786851317)
    ·
      refine ⟨471748858774563261267311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5031987826928674786851317 471748858774563261267311)
      ·
        refine ⟨707623288161844891900967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471748858774563261267311 707623288161844891900967)
        ·
          refine ⟨1061434932242767337851451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 707623288161844891900967 1061434932242767337851451)
          ·
            refine ⟨1592152398364151006777177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061434932242767337851451 1592152398364151006777177)
            ·
              refine ⟨1194114298773113255082883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592152398364151006777177 1194114298773113255082883)
              ·
                refine ⟨1791171448159669882624325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194114298773113255082883 1791171448159669882624325)
                ·
                  refine ⟨335844646529938102992061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791171448159669882624325 335844646529938102992061)
                  ·
                    rfl

theorem cell20_735812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_735812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735812 prefixEnd_735812 := by exact prefixLift 735812
  have htrace : WordTrace (prefixWord ++ tailWord_735812) baseStart_735812 baseEnd_735812 := by
    simpa [prefixWord, tailWord_735812, baseEnd_735812] using wordTrace_append hprefix tailTrace_735812
  have hstable : (prefixWord ++ tailWord_735812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735812).length < 2 ^ (prefixWord ++ tailWord_735812).sum := by decide
  have hdescent : baseEnd_735812 < baseStart_735812 := by decide
  rcases family_descends (prefixWord ++ tailWord_735812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735813 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 5]
def baseStart_735813 : Nat := 118140960795 + 735813 * 2 ^ 59
def prefixEnd_735813 : Nat := 4983230072969 + 3 ^ 40 * 735813 * 2
def baseEnd_735813 : Nat := 335845102957186543958723

theorem tailTrace_735813 : CollatzResearch.WordTrace tailWord_735813 prefixEnd_735813 335845102957186543958723 := by
  unfold tailWord_735813
  simp only [CollatzResearch.WordTrace]
  refine ⟨26837304883282642700660093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17891536588855095133773395 26837304883282642700660093)
  ·
    refine ⟨10063989331230991012747535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26837304883282642700660093 10063989331230991012747535)
    ·
      refine ⟨15095983996846486519121303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10063989331230991012747535 15095983996846486519121303)
      ·
        refine ⟨22643975995269729778681955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15095983996846486519121303 22643975995269729778681955)
        ·
          refine ⟨33965963992904594668022933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22643975995269729778681955 33965963992904594668022933)
          ·
            refine ⟨1592154562167402875063575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33965963992904594668022933 1592154562167402875063575)
            ·
              refine ⟨2388231843251104312595363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592154562167402875063575 2388231843251104312595363)
              ·
                refine ⟨3582347764876656468893045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388231843251104312595363 3582347764876656468893045)
                ·
                  refine ⟨335845102957186543958723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3582347764876656468893045 335845102957186543958723)
                  ·
                    rfl

theorem cell20_735813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_735813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735813 prefixEnd_735813 := by exact prefixLift 735813
  have htrace : WordTrace (prefixWord ++ tailWord_735813) baseStart_735813 baseEnd_735813 := by
    simpa [prefixWord, tailWord_735813, baseEnd_735813] using wordTrace_append hprefix tailTrace_735813
  have hstable : (prefixWord ++ tailWord_735813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735813).length < 2 ^ (prefixWord ++ tailWord_735813).sum := by decide
  have hdescent : baseEnd_735813 < baseStart_735813 := by decide
  rcases family_descends (prefixWord ++ tailWord_735813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735861 : List Nat := [1, 3, 4, 2, 2, 2, 6]
def baseStart_735861 : Nat := 118140960795 + 735861 * 2 ^ 59
def prefixEnd_735861 : Nat := 4983230072969 + 3 ^ 40 * 735861 * 2
def baseEnd_735861 : Nat := 37318556829456856706503

theorem tailTrace_735861 : CollatzResearch.WordTrace tailWord_735861 prefixEnd_735861 37318556829456856706503 := by
  unfold tailWord_735861
  simp only [CollatzResearch.WordTrace]
  refine ⟨26839055587108746898407437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17892703724739164598938291 26839055587108746898407437)
  ·
    refine ⟨10064645845165780086902789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26839055587108746898407437 10064645845165780086902789)
    ·
      refine ⟨1887121095968583766294273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10064645845165780086902789 1887121095968583766294273)
      ·
        refine ⟨1415340821976437824720705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1887121095968583766294273 1415340821976437824720705)
        ·
          refine ⟨1061505616482328368540529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415340821976437824720705 1061505616482328368540529)
          ·
            refine ⟨796129212361746276405397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1061505616482328368540529 796129212361746276405397)
            ·
              refine ⟨37318556829456856706503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 796129212361746276405397 37318556829456856706503)
              ·
                rfl

theorem cell20_735861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 6].length) (baseStart_735861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735861 prefixEnd_735861 := by exact prefixLift 735861
  have htrace : WordTrace (prefixWord ++ tailWord_735861) baseStart_735861 baseEnd_735861 := by
    simpa [prefixWord, tailWord_735861, baseEnd_735861] using wordTrace_append hprefix tailTrace_735861
  have hstable : (prefixWord ++ tailWord_735861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735861).length < 2 ^ (prefixWord ++ tailWord_735861).sum := by decide
  have hdescent : baseEnd_735861 < baseStart_735861 := by decide
  rcases family_descends (prefixWord ++ tailWord_735861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735865 : List Nat := [1, 2, 1, 3, 3, 2, 8]
def baseStart_735865 : Nat := 118140960795 + 735865 * 2 ^ 59
def prefixEnd_735865 : Nat := 4983230072969 + 3 ^ 40 * 735865 * 2
def baseEnd_735865 : Nat := 37318759686011719358353

theorem tailTrace_735865 : CollatzResearch.WordTrace tailWord_735865 prefixEnd_735865 37318759686011719358353 := by
  unfold tailWord_735865
  simp only [CollatzResearch.WordTrace]
  refine ⟨26839201479094255581553049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17892800986062837054368699 26839201479094255581553049)
  ·
    refine ⟨20129401109320691686164787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26839201479094255581553049 20129401109320691686164787)
    ·
      refine ⟨30194101663981037529247181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20129401109320691686164787 30194101663981037529247181)
      ·
        refine ⟨11322788123992889073467693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30194101663981037529247181 11322788123992889073467693)
        ·
          refine ⟨4246045546497333402550385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11322788123992889073467693 4246045546497333402550385)
          ·
            refine ⟨3184534159873000051912789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4246045546497333402550385 3184534159873000051912789)
            ·
              refine ⟨37318759686011719358353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3184534159873000051912789 37318759686011719358353)
              ·
                rfl

theorem cell20_735865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 8].length) (baseStart_735865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735865 prefixEnd_735865 := by exact prefixLift 735865
  have htrace : WordTrace (prefixWord ++ tailWord_735865) baseStart_735865 baseEnd_735865 := by
    simpa [prefixWord, tailWord_735865, baseEnd_735865] using wordTrace_append hprefix tailTrace_735865
  have hstable : (prefixWord ++ tailWord_735865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735865).length < 2 ^ (prefixWord ++ tailWord_735865).sum := by decide
  have hdescent : baseEnd_735865 < baseStart_735865 := by decide
  rcases family_descends (prefixWord ++ tailWord_735865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735875 : List Nat := [1, 1, 1, 3, 3, 1, 2, 6, 2]
def baseStart_735875 : Nat := 118140960795 + 735875 * 2 ^ 59
def prefixEnd_735875 : Nat := 4983230072969 + 3 ^ 40 * 735875 * 2
def baseEnd_735875 : Nat := 335873401446589883891803

theorem tailTrace_735875 : CollatzResearch.WordTrace tailWord_735875 prefixEnd_735875 335873401446589883891803 := by
  unfold tailWord_735875
  simp only [CollatzResearch.WordTrace]
  refine ⟨26839566209058027289417079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17893044139372018192944719 26839566209058027289417079)
  ·
    refine ⟨40259349313587040934125619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26839566209058027289417079 40259349313587040934125619)
    ·
      refine ⟨60389023970380561401188429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40259349313587040934125619 60389023970380561401188429)
      ·
        refine ⟨22645883988892710525445661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60389023970380561401188429 22645883988892710525445661)
        ·
          refine ⟨8492206495834766447042123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22645883988892710525445661 8492206495834766447042123)
          ·
            refine ⟨12738309743752149670563185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8492206495834766447042123 12738309743752149670563185)
            ·
              refine ⟨9553732307814112252922389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12738309743752149670563185 9553732307814112252922389)
              ·
                refine ⟨447831201928786511855737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9553732307814112252922389 447831201928786511855737)
                ·
                  refine ⟨335873401446589883891803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447831201928786511855737 335873401446589883891803)
                  ·
                    rfl

theorem cell20_735875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 2].length) (baseStart_735875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735875 prefixEnd_735875 := by exact prefixLift 735875
  have htrace : WordTrace (prefixWord ++ tailWord_735875) baseStart_735875 baseEnd_735875 := by
    simpa [prefixWord, tailWord_735875, baseEnd_735875] using wordTrace_append hprefix tailTrace_735875
  have hstable : (prefixWord ++ tailWord_735875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735875).length < 2 ^ (prefixWord ++ tailWord_735875).sum := by decide
  have hdescent : baseEnd_735875 < baseStart_735875 := by decide
  rcases family_descends (prefixWord ++ tailWord_735875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735896 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_735896 : Nat := 118140960795 + 735896 * 2 ^ 59
def prefixEnd_735896 : Nat := 4983230072969 + 3 ^ 40 * 735896 * 2
def baseEnd_735896 : Nat := 335882986418807144191717

theorem tailTrace_735896 : CollatzResearch.WordTrace tailWord_735896 prefixEnd_735896 335882986418807144191717 := by
  unfold tailWord_735896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13420166070990973937965771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17893554761321298583954361 13420166070990973937965771)
  ·
    refine ⟨20130249106486460906948657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13420166070990973937965771 20130249106486460906948657)
    ·
      refine ⟨15097686829864845680211493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20130249106486460906948657 15097686829864845680211493)
      ·
        refine ⟨2830816280599658565039655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15097686829864845680211493 2830816280599658565039655)
        ·
          refine ⟨4246224420899487847559483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830816280599658565039655 4246224420899487847559483)
          ·
            refine ⟨6369336631349231771339225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4246224420899487847559483 6369336631349231771339225)
            ·
              refine ⟨4777002473511923828504419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6369336631349231771339225 4777002473511923828504419)
              ·
                refine ⟨7165503710267885742756629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777002473511923828504419 7165503710267885742756629)
                ·
                  refine ⟨335882986418807144191717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7165503710267885742756629 335882986418807144191717)
                  ·
                    rfl

theorem cell20_735896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_735896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735896 prefixEnd_735896 := by exact prefixLift 735896
  have htrace : WordTrace (prefixWord ++ tailWord_735896) baseStart_735896 baseEnd_735896 := by
    simpa [prefixWord, tailWord_735896, baseEnd_735896] using wordTrace_append hprefix tailTrace_735896
  have hstable : (prefixWord ++ tailWord_735896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735896).length < 2 ^ (prefixWord ++ tailWord_735896).sum := by decide
  have hdescent : baseEnd_735896 < baseStart_735896 := by decide
  rcases family_descends (prefixWord ++ tailWord_735896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735926 : List Nat := [5, 1, 3, 1, 2, 1, 1, 4, 2]
def baseStart_735926 : Nat := 118140960795 + 735926 * 2 ^ 59
def prefixEnd_735926 : Nat := 4983230072969 + 3 ^ 40 * 735926 * 2
def baseEnd_735926 : Nat := 335896679236260373191595

theorem tailTrace_735926 : CollatzResearch.WordTrace tailWord_735926 prefixEnd_735926 335896679236260373191595 := by
  unfold tailWord_735926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677589145742078937470227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17894284221248841999682421 1677589145742078937470227)
  ·
    refine ⟨2516383718613118406205341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1677589145742078937470227 2516383718613118406205341)
    ·
      refine ⟨943643894479919402327003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2516383718613118406205341 943643894479919402327003)
      ·
        refine ⟨1415465841719879103490505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943643894479919402327003 1415465841719879103490505)
        ·
          refine ⟨1061599381289909327617879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415465841719879103490505 1061599381289909327617879)
          ·
            refine ⟨1592399071934863991426819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061599381289909327617879 1592399071934863991426819)
            ·
              refine ⟨2388598607902295987140229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592399071934863991426819 2388598607902295987140229)
              ·
                refine ⟨447862238981680497588793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2388598607902295987140229 447862238981680497588793)
                ·
                  refine ⟨335896679236260373191595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447862238981680497588793 335896679236260373191595)
                  ·
                    rfl

theorem cell20_735926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_735926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735926 prefixEnd_735926 := by exact prefixLift 735926
  have htrace : WordTrace (prefixWord ++ tailWord_735926) baseStart_735926 baseEnd_735926 := by
    simpa [prefixWord, tailWord_735926, baseEnd_735926] using wordTrace_append hprefix tailTrace_735926
  have hstable : (prefixWord ++ tailWord_735926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735926).length < 2 ^ (prefixWord ++ tailWord_735926).sum := by decide
  have hdescent : baseEnd_735926 < baseStart_735926 := by decide
  rcases family_descends (prefixWord ++ tailWord_735926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_735982 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_735982 : Nat := 118140960795 + 735982 * 2 ^ 59
def prefixEnd_735982 : Nat := 4983230072969 + 3 ^ 40 * 735982 * 2
def baseEnd_735982 : Nat := 335922239162173067324699

theorem tailTrace_735982 : CollatzResearch.WordTrace tailWord_735982 prefixEnd_735982 335922239162173067324699 := by
  unfold tailWord_735982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355433602458798070445275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17895645879780256375708133 3355433602458798070445275)
  ·
    refine ⟨5033150403688197105667913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3355433602458798070445275 5033150403688197105667913)
    ·
      refine ⟨3774862802766147829250935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5033150403688197105667913 3774862802766147829250935)
      ·
        refine ⟨5662294204149221743876403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3774862802766147829250935 5662294204149221743876403)
        ·
          refine ⟨8493441306223832615814605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662294204149221743876403 8493441306223832615814605)
          ·
            refine ⟨3185040489833937230930477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8493441306223832615814605 3185040489833937230930477)
            ·
              refine ⟨1194390183687726461598929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3185040489833937230930477 1194390183687726461598929)
              ·
                refine ⟨895792637765794846199197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194390183687726461598929 895792637765794846199197)
                ·
                  refine ⟨335922239162173067324699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895792637765794846199197 335922239162173067324699)
                  ·
                    rfl

theorem cell20_735982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_735982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_735982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_735982 prefixEnd_735982 := by exact prefixLift 735982
  have htrace : WordTrace (prefixWord ++ tailWord_735982) baseStart_735982 baseEnd_735982 := by
    simpa [prefixWord, tailWord_735982, baseEnd_735982] using wordTrace_append hprefix tailTrace_735982
  have hstable : (prefixWord ++ tailWord_735982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_735982).length < 2 ^ (prefixWord ++ tailWord_735982).sum := by decide
  have hdescent : baseEnd_735982 < baseStart_735982 := by decide
  rcases family_descends (prefixWord ++ tailWord_735982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736010 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_736010 : Nat := 118140960795 + 736010 * 2 ^ 59
def prefixEnd_736010 : Nat := 4983230072969 + 3 ^ 40 * 736010 * 2
def baseEnd_736010 : Nat := 335935019125129414391251

theorem tailTrace_736010 : CollatzResearch.WordTrace tailWord_736010 prefixEnd_736010 335935019125129414391251 := by
  unfold tailWord_736010
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711122515892236336395371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17896326709045963563720989 6711122515892236336395371)
  ·
    refine ⟨10066683773838354504593057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6711122515892236336395371 10066683773838354504593057)
    ·
      refine ⟨7550012830378765878444793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10066683773838354504593057 7550012830378765878444793)
      ·
        refine ⟨5662509622784074408833595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7550012830378765878444793 5662509622784074408833595)
        ·
          refine ⟨8493764434176111613250393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662509622784074408833595 8493764434176111613250393)
          ·
            refine ⟨6370323325632083709937795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8493764434176111613250393 6370323325632083709937795)
            ·
              refine ⟨9555484988448125564906693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6370323325632083709937795 9555484988448125564906693)
              ·
                refine ⟨1791653435334023543420005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9555484988448125564906693 1791653435334023543420005)
                ·
                  refine ⟨335935019125129414391251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1791653435334023543420005 335935019125129414391251)
                  ·
                    rfl

theorem cell20_736010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_736010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736010 prefixEnd_736010 := by exact prefixLift 736010
  have htrace : WordTrace (prefixWord ++ tailWord_736010) baseStart_736010 baseEnd_736010 := by
    simpa [prefixWord, tailWord_736010, baseEnd_736010] using wordTrace_append hprefix tailTrace_736010
  have hstable : (prefixWord ++ tailWord_736010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736010).length < 2 ^ (prefixWord ++ tailWord_736010).sum := by decide
  have hdescent : baseEnd_736010 < baseStart_736010 := by decide
  rcases family_descends (prefixWord ++ tailWord_736010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736023 : List Nat := [1, 1, 3, 4, 3, 2, 1, 3, 2]
def baseStart_736023 : Nat := 118140960795 + 736023 * 2 ^ 59
def prefixEnd_736023 : Nat := 4983230072969 + 3 ^ 40 * 736023 * 2
def baseEnd_736023 : Nat := 335940952679359146957865

theorem tailTrace_736023 : CollatzResearch.WordTrace tailWord_736023 prefixEnd_736023 335940952679359146957865 := by
  unfold tailWord_736023
  simp only [CollatzResearch.WordTrace]
  refine ⟨26844964212521848565804723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17896642808347899043869815 26844964212521848565804723)
  ·
    refine ⟨40267446318782772848707085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26844964212521848565804723 40267446318782772848707085)
    ·
      refine ⟨15100292369543539818265157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40267446318782772848707085 15100292369543539818265157)
      ·
        refine ⟨2831304819289413715924717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15100292369543539818265157 2831304819289413715924717)
        ·
          refine ⟨1061739307233530143471769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2831304819289413715924717 1061739307233530143471769)
          ·
            refine ⟨796304480425147607603827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1061739307233530143471769 796304480425147607603827)
            ·
              refine ⟨1194456720637721411405741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796304480425147607603827 1194456720637721411405741)
              ·
                refine ⟨447921270239145529277153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1194456720637721411405741 447921270239145529277153)
                ·
                  refine ⟨335940952679359146957865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447921270239145529277153 335940952679359146957865)
                  ·
                    rfl

theorem cell20_736023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 2].length) (baseStart_736023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736023 prefixEnd_736023 := by exact prefixLift 736023
  have htrace : WordTrace (prefixWord ++ tailWord_736023) baseStart_736023 baseEnd_736023 := by
    simpa [prefixWord, tailWord_736023, baseEnd_736023] using wordTrace_append hprefix tailTrace_736023
  have hstable : (prefixWord ++ tailWord_736023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736023).length < 2 ^ (prefixWord ++ tailWord_736023).sum := by decide
  have hdescent : baseEnd_736023 < baseStart_736023 := by decide
  rcases family_descends (prefixWord ++ tailWord_736023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736034 : List Nat := [3, 3, 1, 1, 2, 4, 6]
def baseStart_736034 : Nat := 118140960795 + 736034 * 2 ^ 59
def prefixEnd_736034 : Nat := 4983230072969 + 3 ^ 40 * 736034 * 2
def baseEnd_736034 : Nat := 37327330375454666399017

theorem tailTrace_736034 : CollatzResearch.WordTrace tailWord_736034 prefixEnd_736034 37327330375454666399017 := by
  unfold tailWord_736034
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711341353870499361113789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17896910276987998296303437 6711341353870499361113789)
  ·
    refine ⟨2516753007701437260417671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6711341353870499361113789 2516753007701437260417671)
    ·
      refine ⟨3775129511552155890626507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2516753007701437260417671 3775129511552155890626507)
      ·
        refine ⟨5662694267328233835939761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3775129511552155890626507 5662694267328233835939761)
        ·
          refine ⟨4247020700496175376954821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5662694267328233835939761 4247020700496175376954821)
          ·
            refine ⟨796316381343032883179029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4247020700496175376954821 796316381343032883179029)
            ·
              refine ⟨37327330375454666399017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 796316381343032883179029 37327330375454666399017)
              ·
                rfl

theorem cell20_736034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 6].length) (baseStart_736034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736034 prefixEnd_736034 := by exact prefixLift 736034
  have htrace : WordTrace (prefixWord ++ tailWord_736034) baseStart_736034 baseEnd_736034 := by
    simpa [prefixWord, tailWord_736034, baseEnd_736034] using wordTrace_append hprefix tailTrace_736034
  have hstable : (prefixWord ++ tailWord_736034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736034).length < 2 ^ (prefixWord ++ tailWord_736034).sum := by decide
  have hdescent : baseEnd_736034 < baseStart_736034 := by decide
  rcases family_descends (prefixWord ++ tailWord_736034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736044 : List Nat := [2, 2, 1, 1, 1, 4, 5, 2, 2]
def baseStart_736044 : Nat := 118140960795 + 736044 * 2 ^ 59
def prefixEnd_736044 : Nat := 4983230072969 + 3 ^ 40 * 736044 * 2
def baseEnd_736044 : Nat := 335950537651576407257779

theorem tailTrace_736044 : CollatzResearch.WordTrace tailWord_736044 prefixEnd_736044 335950537651576407257779 := by
  unfold tailWord_736044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422865072722884576159593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17897153430297179434879457 13422865072722884576159593)
  ·
    refine ⟨10067148804542163432119695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13422865072722884576159593 10067148804542163432119695)
    ·
      refine ⟨15100723206813245148179543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10067148804542163432119695 15100723206813245148179543)
      ·
        refine ⟨22651084810219867722269315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15100723206813245148179543 22651084810219867722269315)
        ·
          refine ⟨33976627215329801583403973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22651084810219867722269315 33976627215329801583403973)
          ·
            refine ⟨6370617602874337796888245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33976627215329801583403973 6370617602874337796888245)
            ·
              refine ⟨597245400269469168458273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6370617602874337796888245 597245400269469168458273)
              ·
                refine ⟨447934050202101876343705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597245400269469168458273 447934050202101876343705)
                ·
                  refine ⟨335950537651576407257779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447934050202101876343705 335950537651576407257779)
                  ·
                    rfl

theorem cell20_736044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2, 2].length) (baseStart_736044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736044 prefixEnd_736044 := by exact prefixLift 736044
  have htrace : WordTrace (prefixWord ++ tailWord_736044) baseStart_736044 baseEnd_736044 := by
    simpa [prefixWord, tailWord_736044, baseEnd_736044] using wordTrace_append hprefix tailTrace_736044
  have hstable : (prefixWord ++ tailWord_736044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736044).length < 2 ^ (prefixWord ++ tailWord_736044).sum := by decide
  have hdescent : baseEnd_736044 < baseStart_736044 := by decide
  rcases family_descends (prefixWord ++ tailWord_736044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736055 : List Nat := [1, 1, 3, 1, 2, 1, 6, 5]
def baseStart_736055 : Nat := 118140960795 + 736055 * 2 ^ 59
def prefixEnd_736055 : Nat := 4983230072969 + 3 ^ 40 * 736055 * 2
def baseEnd_736055 : Nat := 111985186117103085963689

theorem tailTrace_736055 : CollatzResearch.WordTrace tailWord_736055 prefixEnd_736055 111985186117103085963689 := by
  unfold tailWord_736055
  simp only [CollatzResearch.WordTrace]
  refine ⟨26846131348405918030969619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17897420898937278687313079 26846131348405918030969619)
  ·
    refine ⟨40269197022608877046454429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26846131348405918030969619 40269197022608877046454429)
    ·
      refine ⟨15100948883478328892420411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40269197022608877046454429 15100948883478328892420411)
      ·
        refine ⟨22651423325217493338630617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15100948883478328892420411 22651423325217493338630617)
        ·
          refine ⟨16988567493913120003972963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22651423325217493338630617 16988567493913120003972963)
          ·
            refine ⟨25482851240869680005959445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16988567493913120003972963 25482851240869680005959445)
            ·
              refine ⟨1194508651915766250279349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25482851240869680005959445 1194508651915766250279349)
              ·
                refine ⟨111985186117103085963689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1194508651915766250279349 111985186117103085963689)
                ·
                  rfl

theorem cell20_736055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_736055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736055 prefixEnd_736055 := by exact prefixLift 736055
  have htrace : WordTrace (prefixWord ++ tailWord_736055) baseStart_736055 baseEnd_736055 := by
    simpa [prefixWord, tailWord_736055, baseEnd_736055] using wordTrace_append hprefix tailTrace_736055
  have hstable : (prefixWord ++ tailWord_736055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736055).length < 2 ^ (prefixWord ++ tailWord_736055).sum := by decide
  have hdescent : baseEnd_736055 < baseStart_736055 := by decide
  rcases family_descends (prefixWord ++ tailWord_736055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736058 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_736058 : Nat := 118140960795 + 736058 * 2 ^ 59
def prefixEnd_736058 : Nat := 4983230072969 + 3 ^ 40 * 736058 * 2
def baseEnd_736058 : Nat := 335956927633054580791055

theorem tailTrace_736058 : CollatzResearch.WordTrace tailWord_736058 prefixEnd_736058 335956927633054580791055 := by
  unfold tailWord_736058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6711560191848762385832207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17897493844930033028885885 6711560191848762385832207)
  ·
    refine ⟨10067340287773143578748311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6711560191848762385832207 10067340287773143578748311)
    ·
      refine ⟨15101010431659715368122467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10067340287773143578748311 15101010431659715368122467)
      ·
        refine ⟨22651515647489573052183701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15101010431659715368122467 22651515647489573052183701)
        ·
          refine ⟨1061789795976073736821111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22651515647489573052183701 1061789795976073736821111)
          ·
            refine ⟨1592684693964110605231667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061789795976073736821111 1592684693964110605231667)
            ·
              refine ⟨2389027040946165907847501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592684693964110605231667 2389027040946165907847501)
              ·
                refine ⟨895885140354812215442813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2389027040946165907847501 895885140354812215442813)
                ·
                  refine ⟨335956927633054580791055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 895885140354812215442813 335956927633054580791055)
                  ·
                    rfl

theorem cell20_736058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_736058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736058 prefixEnd_736058 := by exact prefixLift 736058
  have htrace : WordTrace (prefixWord ++ tailWord_736058) baseStart_736058 baseEnd_736058 := by
    simpa [prefixWord, tailWord_736058, baseEnd_736058] using wordTrace_append hprefix tailTrace_736058
  have hstable : (prefixWord ++ tailWord_736058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736058).length < 2 ^ (prefixWord ++ tailWord_736058).sum := by decide
  have hdescent : baseEnd_736058 < baseStart_736058 := by decide
  rcases family_descends (prefixWord ++ tailWord_736058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736099 : List Nat := [1, 1, 1, 5, 3, 3, 2, 2, 2]
def baseStart_736099 : Nat := 118140960795 + 736099 * 2 ^ 59
def prefixEnd_736099 : Nat := 4983230072969 + 3 ^ 40 * 736099 * 2
def baseEnd_736099 : Nat := 335975641150240660424221

theorem tailTrace_736099 : CollatzResearch.WordTrace tailWord_736099 prefixEnd_736099 335975641150240660424221 := by
  unfold tailWord_736099
  simp only [CollatzResearch.WordTrace]
  refine ⟨26847736160246513545571351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17898490773497675697047567 26847736160246513545571351)
  ·
    refine ⟨40271604240369770318357027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26847736160246513545571351 40271604240369770318357027)
    ·
      refine ⟨60407406360554655477535541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40271604240369770318357027 60407406360554655477535541)
      ·
        refine ⟨5663194346301998951018957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60407406360554655477535541 5663194346301998951018957)
        ·
          refine ⟨2123697879863249606632109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5663194346301998951018957 2123697879863249606632109)
          ·
            refine ⟨796386704948718602487041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2123697879863249606632109 796386704948718602487041)
            ·
              refine ⟨597290028711538951865281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796386704948718602487041 597290028711538951865281)
              ·
                refine ⟨447967521533654213898961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597290028711538951865281 447967521533654213898961)
                ·
                  refine ⟨335975641150240660424221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 447967521533654213898961 335975641150240660424221)
                  ·
                    rfl

theorem cell20_736099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 2, 2].length) (baseStart_736099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736099 prefixEnd_736099 := by exact prefixLift 736099
  have htrace : WordTrace (prefixWord ++ tailWord_736099) baseStart_736099 baseEnd_736099 := by
    simpa [prefixWord, tailWord_736099, baseEnd_736099] using wordTrace_append hprefix tailTrace_736099
  have hstable : (prefixWord ++ tailWord_736099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736099).length < 2 ^ (prefixWord ++ tailWord_736099).sum := by decide
  have hdescent : baseEnd_736099 < baseStart_736099 := by decide
  rcases family_descends (prefixWord ++ tailWord_736099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736145 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_736145 : Nat := 118140960795 + 736145 * 2 ^ 59
def prefixEnd_736145 : Nat := 4983230072969 + 3 ^ 40 * 736145 * 2
def baseEnd_736145 : Nat := 335996636803668944890699

theorem tailTrace_736145 : CollatzResearch.WordTrace tailWord_736145 prefixEnd_736145 335996636803668944890699 := by
  unfold tailWord_736145
  simp only [CollatzResearch.WordTrace]
  refine ⟨26849413918079863401745889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17899609278719908934497259 26849413918079863401745889)
  ·
    refine ⟨20137060438559897551309417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26849413918079863401745889 20137060438559897551309417)
    ·
      refine ⟨15102795328919923163482063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20137060438559897551309417 15102795328919923163482063)
      ·
        refine ⟨22654192993379884745223095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15102795328919923163482063 22654192993379884745223095)
        ·
          refine ⟨33981289490069827117834643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22654192993379884745223095 33981289490069827117834643)
          ·
            refine ⟨50971934235104740676751965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33981289490069827117834643 50971934235104740676751965)
            ·
              refine ⟨19114475338164277753781987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50971934235104740676751965 19114475338164277753781987)
              ·
                refine ⟨28671713007246416630672981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19114475338164277753781987 28671713007246416630672981)
                ·
                  refine ⟨335996636803668944890699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28671713007246416630672981 335996636803668944890699)
                  ·
                    rfl

theorem cell20_736145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_736145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736145 prefixEnd_736145 := by exact prefixLift 736145
  have htrace : WordTrace (prefixWord ++ tailWord_736145) baseStart_736145 baseEnd_736145 := by
    simpa [prefixWord, tailWord_736145, baseEnd_736145] using wordTrace_append hprefix tailTrace_736145
  have hstable : (prefixWord ++ tailWord_736145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736145).length < 2 ^ (prefixWord ++ tailWord_736145).sum := by decide
  have hdescent : baseEnd_736145 < baseStart_736145 := by decide
  rcases family_descends (prefixWord ++ tailWord_736145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736207 : List Nat := [1, 1, 2, 1, 1, 8, 6]
def baseStart_736207 : Nat := 118140960795 + 736207 * 2 ^ 59
def prefixEnd_736207 : Nat := 4983230072969 + 3 ^ 40 * 736207 * 2
def baseEnd_736207 : Nat := 37336103921452476091531

theorem tailTrace_736207 : CollatzResearch.WordTrace tailWord_736207 prefixEnd_736207 37336103921452476091531 := by
  unfold tailWord_736207
  simp only [CollatzResearch.WordTrace]
  refine ⟨26851675243855247990502875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17901116829236831993668583 26851675243855247990502875)
  ·
    refine ⟨40277512865782871985754313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26851675243855247990502875 40277512865782871985754313)
    ·
      refine ⟨30208134649337153989315735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40277512865782871985754313 30208134649337153989315735)
      ·
        refine ⟨45312201974005730983973603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30208134649337153989315735 45312201974005730983973603)
        ·
          refine ⟨67968302961008596475960405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45312201974005730983973603 67968302961008596475960405)
          ·
            refine ⟨796503550324319489952661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 67968302961008596475960405 796503550324319489952661)
            ·
              refine ⟨37336103921452476091531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 796503550324319489952661 37336103921452476091531)
              ·
                rfl

theorem cell20_736207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 6].length) (baseStart_736207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736207 prefixEnd_736207 := by exact prefixLift 736207
  have htrace : WordTrace (prefixWord ++ tailWord_736207) baseStart_736207 baseEnd_736207 := by
    simpa [prefixWord, tailWord_736207, baseEnd_736207] using wordTrace_append hprefix tailTrace_736207
  have hstable : (prefixWord ++ tailWord_736207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736207).length < 2 ^ (prefixWord ++ tailWord_736207).sum := by decide
  have hdescent : baseEnd_736207 < baseStart_736207 := by decide
  rcases family_descends (prefixWord ++ tailWord_736207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736213 : List Nat := [1, 3, 2, 3, 3, 1, 3, 2, 2]
def baseStart_736213 : Nat := 118140960795 + 736213 * 2 ^ 59
def prefixEnd_736213 : Nat := 4983230072969 + 3 ^ 40 * 736213 * 2
def baseEnd_736213 : Nat := 336027673856562930623755

theorem tailTrace_736213 : CollatzResearch.WordTrace tailWord_736213 prefixEnd_736213 336027673856562930623755 := by
  unfold tailWord_736213
  simp only [CollatzResearch.WordTrace]
  refine ⟨26851894081833511015221293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17901262721222340676814195 26851894081833511015221293)
  ·
    refine ⟨10069460280687566630707985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26851894081833511015221293 10069460280687566630707985)
    ·
      refine ⟨7552095210515674973030989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10069460280687566630707985 7552095210515674973030989)
      ·
        refine ⟨2832035703943378114886621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7552095210515674973030989 2832035703943378114886621)
        ·
          refine ⟨1062013388978766793082483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2832035703943378114886621 1062013388978766793082483)
          ·
            refine ⟨1593020083468150189623725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062013388978766793082483 1593020083468150189623725)
            ·
              refine ⟨597382531300556321108897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593020083468150189623725 597382531300556321108897)
              ·
                refine ⟨448036898475417240831673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597382531300556321108897 448036898475417240831673)
                ·
                  refine ⟨336027673856562930623755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448036898475417240831673 336027673856562930623755)
                  ·
                    rfl

theorem cell20_736213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_736213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736213 prefixEnd_736213 := by exact prefixLift 736213
  have htrace : WordTrace (prefixWord ++ tailWord_736213) baseStart_736213 baseEnd_736213 := by
    simpa [prefixWord, tailWord_736213, baseEnd_736213] using wordTrace_append hprefix tailTrace_736213
  have hstable : (prefixWord ++ tailWord_736213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736213).length < 2 ^ (prefixWord ++ tailWord_736213).sum := by decide
  have hdescent : baseEnd_736213 < baseStart_736213 := by decide
  rcases family_descends (prefixWord ++ tailWord_736213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736217 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 4]
def baseStart_736217 : Nat := 118140960795 + 736217 * 2 ^ 59
def prefixEnd_736217 : Nat := 4983230072969 + 3 ^ 40 * 736217 * 2
def baseEnd_736217 : Nat := 336029499565556694490405

theorem tailTrace_736217 : CollatzResearch.WordTrace tailWord_736217 prefixEnd_736217 336029499565556694490405 := by
  unfold tailWord_736217
  simp only [CollatzResearch.WordTrace]
  refine ⟨26852039973819019698366905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17901359982546013132244603 26852039973819019698366905)
  ·
    refine ⟨20139029980364264773775179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26852039973819019698366905 20139029980364264773775179)
    ·
      refine ⟨30208544970546397160662769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20139029980364264773775179 30208544970546397160662769)
      ·
        refine ⟨22656408727909797870497077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30208544970546397160662769 22656408727909797870497077)
        ·
          refine ⟨2124038318241543550359101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22656408727909797870497077 2124038318241543550359101)
          ·
            refine ⟨796514369340578831384663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2124038318241543550359101 796514369340578831384663)
            ·
              refine ⟨1194771554010868247076995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796514369340578831384663 1194771554010868247076995)
              ·
                refine ⟨1792157331016302370615493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194771554010868247076995 1792157331016302370615493)
                ·
                  refine ⟨336029499565556694490405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792157331016302370615493 336029499565556694490405)
                  ·
                    rfl

theorem cell20_736217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_736217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736217 prefixEnd_736217 := by exact prefixLift 736217
  have htrace : WordTrace (prefixWord ++ tailWord_736217) baseStart_736217 baseEnd_736217 := by
    simpa [prefixWord, tailWord_736217, baseEnd_736217] using wordTrace_append hprefix tailTrace_736217
  have hstable : (prefixWord ++ tailWord_736217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736217).length < 2 ^ (prefixWord ++ tailWord_736217).sum := by decide
  have hdescent : baseEnd_736217 < baseStart_736217 := by decide
  rcases family_descends (prefixWord ++ tailWord_736217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736310 : List Nat := [5, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_736310 : Nat := 118140960795 + 736310 * 2 ^ 59
def prefixEnd_736310 : Nat := 4983230072969 + 3 ^ 40 * 736310 * 2
def baseEnd_736310 : Nat := 336071947299661704390025

theorem tailTrace_736310 : CollatzResearch.WordTrace tailWord_736310 prefixEnd_736310 336071947299661704390025 := by
  unfold tailWord_736310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1678464497655131036343899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17903621308321397721001589 1678464497655131036343899)
  ·
    refine ⟨2517696746482696554515849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1678464497655131036343899 2517696746482696554515849)
    ·
      refine ⟨1888272559862022415886887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2517696746482696554515849 1888272559862022415886887)
      ·
        refine ⟨2832408839793033623830331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888272559862022415886887 2832408839793033623830331)
        ·
          refine ⟨4248613259689550435745497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832408839793033623830331 4248613259689550435745497)
          ·
            refine ⟨3186459944767162826809123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4248613259689550435745497 3186459944767162826809123)
            ·
              refine ⟨4779689917150744240213685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186459944767162826809123 4779689917150744240213685)
              ·
                refine ⟨448095929732882272520033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4779689917150744240213685 448095929732882272520033)
                ·
                  refine ⟨336071947299661704390025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448095929732882272520033 336071947299661704390025)
                  ·
                    rfl

theorem cell20_736310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_736310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736310 prefixEnd_736310 := by exact prefixLift 736310
  have htrace : WordTrace (prefixWord ++ tailWord_736310) baseStart_736310 baseEnd_736310 := by
    simpa [prefixWord, tailWord_736310, baseEnd_736310] using wordTrace_append hprefix tailTrace_736310
  have hstable : (prefixWord ++ tailWord_736310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736310).length < 2 ^ (prefixWord ++ tailWord_736310).sum := by decide
  have hdescent : baseEnd_736310 < baseStart_736310 := by decide
  rcases family_descends (prefixWord ++ tailWord_736310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736328 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_736328 : Nat := 118140960795 + 736328 * 2 ^ 59
def prefixEnd_736328 : Nat := 4983230072969 + 3 ^ 40 * 736328 * 2
def baseEnd_736328 : Nat := 336080162990133641789951

theorem tailTrace_736328 : CollatzResearch.WordTrace tailWord_736328 prefixEnd_736328 336080162990133641789951 := by
  unfold tailWord_736328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13428044238208442827828819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17904058984277923770438425 13428044238208442827828819)
  ·
    refine ⟨20142066357312664241743229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13428044238208442827828819 20142066357312664241743229)
    ·
      refine ⟨7553274883992249090653711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20142066357312664241743229 7553274883992249090653711)
      ·
        refine ⟨11329912325988373635980567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7553274883992249090653711 11329912325988373635980567)
        ·
          refine ⟨16994868488982560453970851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11329912325988373635980567 16994868488982560453970851)
          ·
            refine ⟨25492302733473840680956277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16994868488982560453970851 25492302733473840680956277)
            ·
              refine ⟨2389903381263172563839651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25492302733473840680956277 2389903381263172563839651)
              ·
                refine ⟨3584855071894758845759477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389903381263172563839651 3584855071894758845759477)
                ·
                  refine ⟨336080162990133641789951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3584855071894758845759477 336080162990133641789951)
                  ·
                    rfl

theorem cell20_736328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_736328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736328 prefixEnd_736328 := by exact prefixLift 736328
  have htrace : WordTrace (prefixWord ++ tailWord_736328) baseStart_736328 baseEnd_736328 := by
    simpa [prefixWord, tailWord_736328, baseEnd_736328] using wordTrace_append hprefix tailTrace_736328
  have hstable : (prefixWord ++ tailWord_736328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736328).length < 2 ^ (prefixWord ++ tailWord_736328).sum := by decide
  have hdescent : baseEnd_736328 < baseStart_736328 := by decide
  rcases family_descends (prefixWord ++ tailWord_736328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736359 : List Nat := [1, 1, 5, 1, 1, 4, 1, 6]
def baseStart_736359 : Nat := 118140960795 + 736359 * 2 ^ 59
def prefixEnd_736359 : Nat := 4983230072969 + 3 ^ 40 * 736359 * 2
def baseEnd_736359 : Nat := 112031437411611770585497

theorem tailTrace_736359 : CollatzResearch.WordTrace tailWord_736359 prefixEnd_736359 112031437411611770585497 := by
  unfold tailWord_736359
  simp only [CollatzResearch.WordTrace]
  refine ⟨26857219139304577950036131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17904812759536385300024087 26857219139304577950036131)
  ·
    refine ⟨40285828708956866925054197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26857219139304577950036131 40285828708956866925054197)
    ·
      refine ⟨3776796441464706274223831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40285828708956866925054197 3776796441464706274223831)
      ·
        refine ⟨5665194662197059411335747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3776796441464706274223831 5665194662197059411335747)
        ·
          refine ⟨8497791993295589117003621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665194662197059411335747 8497791993295589117003621)
          ·
            refine ⟨1593335998742922959438179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8497791993295589117003621 1593335998742922959438179)
            ·
              refine ⟨2390003998114384439157269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593335998742922959438179 2390003998114384439157269)
              ·
                refine ⟨112031437411611770585497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2390003998114384439157269 112031437411611770585497)
                ·
                  rfl

theorem cell20_736359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 6].length) (baseStart_736359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736359 prefixEnd_736359 := by exact prefixLift 736359
  have htrace : WordTrace (prefixWord ++ tailWord_736359) baseStart_736359 baseEnd_736359 := by
    simpa [prefixWord, tailWord_736359, baseEnd_736359] using wordTrace_append hprefix tailTrace_736359
  have hstable : (prefixWord ++ tailWord_736359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736359).length < 2 ^ (prefixWord ++ tailWord_736359).sum := by decide
  have hdescent : baseEnd_736359 < baseStart_736359 := by decide
  rcases family_descends (prefixWord ++ tailWord_736359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736382 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_736382 : Nat := 118140960795 + 736382 * 2 ^ 59
def prefixEnd_736382 : Nat := 4983230072969 + 3 ^ 40 * 736382 * 2
def baseEnd_736382 : Nat := 336104810061549453989731

theorem tailTrace_736382 : CollatzResearch.WordTrace tailWord_736382 prefixEnd_736382 336104810061549453989731 := by
  unfold tailWord_736382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357257252277656609765425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17905372012147501918748933 3357257252277656609765425)
  ·
    refine ⟨2517942939208242457324069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3357257252277656609765425 2517942939208242457324069)
    ·
      refine ⟨472114301101545460748263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2517942939208242457324069 472114301101545460748263)
      ·
        refine ⟨708171451652318191122395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472114301101545460748263 708171451652318191122395)
        ·
          refine ⟨1062257177478477286683593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708171451652318191122395 1062257177478477286683593)
          ·
            refine ⟨796692883108857965012695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1062257177478477286683593 796692883108857965012695)
            ·
              refine ⟨1195039324663286947519043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796692883108857965012695 1195039324663286947519043)
              ·
                refine ⟨1792558986994930421278565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195039324663286947519043 1792558986994930421278565)
                ·
                  refine ⟨336104810061549453989731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792558986994930421278565 336104810061549453989731)
                  ·
                    rfl

theorem cell20_736382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_736382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736382 prefixEnd_736382 := by exact prefixLift 736382
  have htrace : WordTrace (prefixWord ++ tailWord_736382) baseStart_736382 baseEnd_736382 := by
    simpa [prefixWord, tailWord_736382, baseEnd_736382] using wordTrace_append hprefix tailTrace_736382
  have hstable : (prefixWord ++ tailWord_736382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736382).length < 2 ^ (prefixWord ++ tailWord_736382).sum := by decide
  have hdescent : baseEnd_736382 < baseStart_736382 := by decide
  rcases family_descends (prefixWord ++ tailWord_736382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736414 : List Nat := [4, 3, 1, 1, 2, 1, 2, 6]
def baseStart_736414 : Nat := 118140960795 + 736414 * 2 ^ 59
def prefixEnd_736414 : Nat := 4983230072969 + 3 ^ 40 * 736414 * 2
def baseEnd_736414 : Nat := 112039805244499854974311

theorem tailTrace_736414 : CollatzResearch.WordTrace tailWord_736414 prefixEnd_736414 112039805244499854974311 := by
  unfold tailWord_736414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357403144263165292911037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17906150102736881562192197 3357403144263165292911037)
  ·
    refine ⟨1259026179098686984841639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3357403144263165292911037 1259026179098686984841639)
    ·
      refine ⟨1888539268648030477262459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1259026179098686984841639 1888539268648030477262459)
      ·
        refine ⟨2832808902972045715893689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1888539268648030477262459 2832808902972045715893689)
        ·
          refine ⟨2124606677229034286920267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2832808902972045715893689 2124606677229034286920267)
          ·
            refine ⟨3186910015843551430380401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2124606677229034286920267 3186910015843551430380401)
            ·
              refine ⟨2390182511882663572785301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3186910015843551430380401 2390182511882663572785301)
              ·
                refine ⟨112039805244499854974311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2390182511882663572785301 112039805244499854974311)
                ·
                  rfl

theorem cell20_736414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_736414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736414 prefixEnd_736414 := by exact prefixLift 736414
  have htrace : WordTrace (prefixWord ++ tailWord_736414) baseStart_736414 baseEnd_736414 := by
    simpa [prefixWord, tailWord_736414, baseEnd_736414] using wordTrace_append hprefix tailTrace_736414
  have hstable : (prefixWord ++ tailWord_736414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736414).length < 2 ^ (prefixWord ++ tailWord_736414).sum := by decide
  have hdescent : baseEnd_736414 < baseStart_736414 := by decide
  rcases family_descends (prefixWord ++ tailWord_736414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736466 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_736466 : Nat := 118140960795 + 736466 * 2 ^ 59
def prefixEnd_736466 : Nat := 4983230072969 + 3 ^ 40 * 736466 * 2
def baseEnd_736466 : Nat := 336143149950418495189387

theorem tailTrace_736466 : CollatzResearch.WordTrace tailWord_736466 prefixEnd_736466 336143149950418495189387 := by
  unfold tailWord_736466
  simp only [CollatzResearch.WordTrace]
  refine ⟨6715280437479233806045313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17907414499944623482787501 6715280437479233806045313)
  ·
    refine ⟨5036460328109425354533985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6715280437479233806045313 5036460328109425354533985)
    ·
      refine ⟨3777345246082069015900489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5036460328109425354533985 3777345246082069015900489)
      ·
        refine ⟨2833008934561551761925367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3777345246082069015900489 2833008934561551761925367)
        ·
          refine ⟨4249513401842327642888051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2833008934561551761925367 4249513401842327642888051)
          ·
            refine ⟨6374270102763491464332077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249513401842327642888051 6374270102763491464332077)
            ·
              refine ⟨2390351288536309299124529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6374270102763491464332077 2390351288536309299124529)
              ·
                refine ⟨1792763466402231974343397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390351288536309299124529 1792763466402231974343397)
                ·
                  refine ⟨336143149950418495189387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1792763466402231974343397 336143149950418495189387)
                  ·
                    rfl

theorem cell20_736466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_736466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736466 prefixEnd_736466 := by exact prefixLift 736466
  have htrace : WordTrace (prefixWord ++ tailWord_736466) baseStart_736466 baseEnd_736466 := by
    simpa [prefixWord, tailWord_736466, baseEnd_736466] using wordTrace_append hprefix tailTrace_736466
  have hstable : (prefixWord ++ tailWord_736466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736466).length < 2 ^ (prefixWord ++ tailWord_736466).sum := by decide
  have hdescent : baseEnd_736466 < baseStart_736466 := by decide
  rcases family_descends (prefixWord ++ tailWord_736466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736538 : List Nat := [3, 1, 1, 3, 3, 3, 1, 3, 2]
def baseStart_736538 : Nat := 118140960795 + 736538 * 2 ^ 59
def prefixEnd_736538 : Nat := 4983230072969 + 3 ^ 40 * 736538 * 2
def baseEnd_736538 : Nat := 336176012712306244789093

theorem tailTrace_736538 : CollatzResearch.WordTrace tailWord_736538 prefixEnd_736538 336176012712306244789093 := by
  unfold tailWord_736538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6715936951414022880200567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17909165203770727680534845 6715936951414022880200567)
  ·
    refine ⟨10073905427121034320300851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6715936951414022880200567 10073905427121034320300851)
    ·
      refine ⟨15110858140681551480451277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10073905427121034320300851 15110858140681551480451277)
      ·
        refine ⟨5666571802755581805169229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15110858140681551480451277 5666571802755581805169229)
        ·
          refine ⟨2124964426033343176938461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5666571802755581805169229 2124964426033343176938461)
          ·
            refine ⟨796861659762503691351923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2124964426033343176938461 796861659762503691351923)
            ·
              refine ⟨1195292489643755537027885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 796861659762503691351923 1195292489643755537027885)
              ·
                refine ⟨448234683616408326385457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1195292489643755537027885 448234683616408326385457)
                ·
                  refine ⟨336176012712306244789093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448234683616408326385457 336176012712306244789093)
                  ·
                    rfl

theorem cell20_736538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 3, 2].length) (baseStart_736538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736538 prefixEnd_736538 := by exact prefixLift 736538
  have htrace : WordTrace (prefixWord ++ tailWord_736538) baseStart_736538 baseEnd_736538 := by
    simpa [prefixWord, tailWord_736538, baseEnd_736538] using wordTrace_append hprefix tailTrace_736538
  have hstable : (prefixWord ++ tailWord_736538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736538).length < 2 ^ (prefixWord ++ tailWord_736538).sum := by decide
  have hdescent : baseEnd_736538 < baseStart_736538 := by decide
  rcases family_descends (prefixWord ++ tailWord_736538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736549 : List Nat := [1, 3, 1, 2, 4, 3, 6]
def baseStart_736549 : Nat := 118140960795 + 736549 * 2 ^ 59
def prefixEnd_736549 : Nat := 4983230072969 + 3 ^ 40 * 736549 * 2
def baseEnd_736549 : Nat := 37353448156893232824709

theorem tailTrace_736549 : CollatzResearch.WordTrace tailWord_736549 prefixEnd_736549 37353448156893232824709 := by
  unfold tailWord_736549
  simp only [CollatzResearch.WordTrace]
  refine ⟨26864149008616240399452701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17909432672410826932968467 26864149008616240399452701)
  ·
    refine ⟨10074055878231090149794763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26864149008616240399452701 10074055878231090149794763)
    ·
      refine ⟨15111083817346635224692145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10074055878231090149794763 15111083817346635224692145)
      ·
        refine ⟨11333312863009976418519109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15111083817346635224692145 11333312863009976418519109)
        ·
          refine ⟨2124996161814370578472333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11333312863009976418519109 2124996161814370578472333)
          ·
            refine ⟨796873560680388966927125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2124996161814370578472333 796873560680388966927125)
            ·
              refine ⟨37353448156893232824709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 796873560680388966927125 37353448156893232824709)
              ·
                rfl

theorem cell20_736549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 6].length) (baseStart_736549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736549 prefixEnd_736549 := by exact prefixLift 736549
  have htrace : WordTrace (prefixWord ++ tailWord_736549) baseStart_736549 baseEnd_736549 := by
    simpa [prefixWord, tailWord_736549, baseEnd_736549] using wordTrace_append hprefix tailTrace_736549
  have hstable : (prefixWord ++ tailWord_736549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736549).length < 2 ^ (prefixWord ++ tailWord_736549).sum := by decide
  have hdescent : baseEnd_736549 < baseStart_736549 := by decide
  rcases family_descends (prefixWord ++ tailWord_736549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736556 : List Nat := [2, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_736556 : Nat := 118140960795 + 736556 * 2 ^ 59
def prefixEnd_736556 : Nat := 4983230072969 + 3 ^ 40 * 736556 * 2
def baseEnd_736556 : Nat := 336184228402778182189019

theorem tailTrace_736556 : CollatzResearch.WordTrace tailWord_736556 prefixEnd_736556 336184228402778182189019 := by
  unfold tailWord_736556
  simp only [CollatzResearch.WordTrace]
  refine ⟨13432202159795440297478761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17909602879727253729971681 13432202159795440297478761)
  ·
    refine ⟨10074151619846580223109071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13432202159795440297478761 10074151619846580223109071)
    ·
      refine ⟨15111227429769870334663607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10074151619846580223109071 15111227429769870334663607)
      ·
        refine ⟨22666841144654805501995411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15111227429769870334663607 22666841144654805501995411)
        ·
          refine ⟨34000261716982208252993117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22666841144654805501995411 34000261716982208252993117)
          ·
            refine ⟨12750098143868328094872419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34000261716982208252993117 12750098143868328094872419)
            ·
              refine ⟨19125147215802492142308629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12750098143868328094872419 19125147215802492142308629)
              ·
                refine ⟨896491275740741819170717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19125147215802492142308629 896491275740741819170717)
                ·
                  refine ⟨336184228402778182189019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896491275740741819170717 336184228402778182189019)
                  ·
                    rfl

theorem cell20_736556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_736556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736556 prefixEnd_736556 := by exact prefixLift 736556
  have htrace : WordTrace (prefixWord ++ tailWord_736556) baseStart_736556 baseEnd_736556 := by
    simpa [prefixWord, tailWord_736556, baseEnd_736556] using wordTrace_append hprefix tailTrace_736556
  have hstable : (prefixWord ++ tailWord_736556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736556).length < 2 ^ (prefixWord ++ tailWord_736556).sum := by decide
  have hdescent : baseEnd_736556 < baseStart_736556 := by decide
  rcases family_descends (prefixWord ++ tailWord_736556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736569 : List Nat := [1, 2, 1, 6, 2, 2, 2, 1, 3]
def baseStart_736569 : Nat := 118140960795 + 736569 * 2 ^ 59
def prefixEnd_736569 : Nat := 4983230072969 + 3 ^ 40 * 736569 * 2
def baseEnd_736569 : Nat := 336190161957007914755633

theorem tailTrace_736569 : CollatzResearch.WordTrace tailWord_736569 prefixEnd_736569 336190161957007914755633 := by
  unfold tailWord_736569
  simp only [CollatzResearch.WordTrace]
  refine ⟨26864878468543783815180761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17909918979029189210120507 26864878468543783815180761)
  ·
    refine ⟨20148658851407837861385571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26864878468543783815180761 20148658851407837861385571)
    ·
      refine ⟨30222988277111756792078357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20148658851407837861385571 30222988277111756792078357)
      ·
        refine ⟨1416702575489613599628673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30222988277111756792078357 1416702575489613599628673)
        ·
          refine ⟨1062526931617210199721505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1416702575489613599628673 1062526931617210199721505)
          ·
            refine ⟨796895198712907649791129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1062526931617210199721505 796895198712907649791129)
            ·
              refine ⟨597671399034680737343347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796895198712907649791129 597671399034680737343347)
              ·
                refine ⟨896507098552021106015021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 597671399034680737343347 896507098552021106015021)
                ·
                  refine ⟨336190161957007914755633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896507098552021106015021 336190161957007914755633)
                  ·
                    rfl

theorem cell20_736569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_736569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736569 prefixEnd_736569 := by exact prefixLift 736569
  have htrace : WordTrace (prefixWord ++ tailWord_736569) baseStart_736569 baseEnd_736569 := by
    simpa [prefixWord, tailWord_736569, baseEnd_736569] using wordTrace_append hprefix tailTrace_736569
  have hstable : (prefixWord ++ tailWord_736569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736569).length < 2 ^ (prefixWord ++ tailWord_736569).sum := by decide
  have hdescent : baseEnd_736569 < baseStart_736569 := by decide
  rcases family_descends (prefixWord ++ tailWord_736569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736608 : List Nat := [2, 1, 1, 3, 4, 9]
def baseStart_736608 : Nat := 118140960795 + 736608 * 2 ^ 59
def prefixEnd_736608 : Nat := 4983230072969 + 3 ^ 40 * 736608 * 2
def baseEnd_736608 : Nat := 12452146763692485646499

theorem tailTrace_736608 : CollatzResearch.WordTrace tailWord_736608 prefixEnd_736608 12452146763692485646499 := by
  unfold tailWord_736608
  simp only [CollatzResearch.WordTrace]
  refine ⟨13433150457701246737925239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17910867276934995650566985 13433150457701246737925239)
  ·
    refine ⟨20149725686551870106887859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13433150457701246737925239 20149725686551870106887859)
    ·
      refine ⟨30224588529827805160331789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20149725686551870106887859 30224588529827805160331789)
      ·
        refine ⟨11334220698685426935124421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30224588529827805160331789 11334220698685426935124421)
        ·
          refine ⟨2125166381003517550335829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11334220698685426935124421 2125166381003517550335829)
          ·
            refine ⟨12452146763692485646499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2125166381003517550335829 12452146763692485646499)
            ·
              rfl

theorem cell20_736608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 9].length) (baseStart_736608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736608 prefixEnd_736608 := by exact prefixLift 736608
  have htrace : WordTrace (prefixWord ++ tailWord_736608) baseStart_736608 baseEnd_736608 := by
    simpa [prefixWord, tailWord_736608, baseEnd_736608] using wordTrace_append hprefix tailTrace_736608
  have hstable : (prefixWord ++ tailWord_736608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736608).length < 2 ^ (prefixWord ++ tailWord_736608).sum := by decide
  have hdescent : baseEnd_736608 < baseStart_736608 := by decide
  rcases family_descends (prefixWord ++ tailWord_736608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736611 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 3]
def baseStart_736611 : Nat := 118140960795 + 736611 * 2 ^ 59
def prefixEnd_736611 : Nat := 4983230072969 + 3 ^ 40 * 736611 * 2
def baseEnd_736611 : Nat := 336209331901442435355461

theorem tailTrace_736611 : CollatzResearch.WordTrace tailWord_736611 prefixEnd_736611 336209331901442435355461 := by
  unfold tailWord_736611
  simp only [CollatzResearch.WordTrace]
  refine ⟨26866410334391624988209687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17910940222927749992139791 26866410334391624988209687)
  ·
    refine ⟨40299615501587437482314531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26866410334391624988209687 40299615501587437482314531)
    ·
      refine ⟨60449423252381156223471797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40299615501587437482314531 60449423252381156223471797)
      ·
        refine ⟨5667133429910733395950481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60449423252381156223471797 5667133429910733395950481)
        ·
          refine ⟨4250350072433050046962861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5667133429910733395950481 4250350072433050046962861)
          ·
            refine ⟨1593881277162393767611073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4250350072433050046962861 1593881277162393767611073)
            ·
              refine ⟨1195410957871795325708305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1593881277162393767611073 1195410957871795325708305)
              ·
                refine ⟨896558218403846494281229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195410957871795325708305 896558218403846494281229)
                ·
                  refine ⟨336209331901442435355461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 896558218403846494281229 336209331901442435355461)
                  ·
                    rfl

theorem cell20_736611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 3].length) (baseStart_736611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736611 prefixEnd_736611 := by exact prefixLift 736611
  have htrace : WordTrace (prefixWord ++ tailWord_736611) baseStart_736611 baseEnd_736611 := by
    simpa [prefixWord, tailWord_736611, baseEnd_736611] using wordTrace_append hprefix tailTrace_736611
  have hstable : (prefixWord ++ tailWord_736611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736611).length < 2 ^ (prefixWord ++ tailWord_736611).sum := by decide
  have hdescent : baseEnd_736611 < baseStart_736611 := by decide
  rcases family_descends (prefixWord ++ tailWord_736611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736638 : List Nat := [4, 2, 3, 2, 1, 1, 3, 4]
def baseStart_736638 : Nat := 118140960795 + 736638 * 2 ^ 59
def prefixEnd_736638 : Nat := 4983230072969 + 3 ^ 40 * 736638 * 2
def baseEnd_736638 : Nat := 112073885145716780485117

theorem tailTrace_736638 : CollatzResearch.WordTrace tailWord_736638 prefixEnd_736638 112073885145716780485117 := by
  unfold tailWord_736638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3358424388161726074930321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17911596736862539066295045 3358424388161726074930321)
  ·
    refine ⟨2518818291121294556197741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3358424388161726074930321 2518818291121294556197741)
    ·
      refine ⟨944556859170485458574153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2518818291121294556197741 944556859170485458574153)
      ·
        refine ⟨708417644377864093930615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 944556859170485458574153 708417644377864093930615)
        ·
          refine ⟨1062626466566796140895923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708417644377864093930615 1062626466566796140895923)
          ·
            refine ⟨1593939699850194211343885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1062626466566796140895923 1593939699850194211343885)
            ·
              refine ⟨597727387443822829253957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1593939699850194211343885 597727387443822829253957)
              ·
                refine ⟨112073885145716780485117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 597727387443822829253957 112073885145716780485117)
                ·
                  rfl

theorem cell20_736638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_736638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736638 prefixEnd_736638 := by exact prefixLift 736638
  have htrace : WordTrace (prefixWord ++ tailWord_736638) baseStart_736638 baseEnd_736638 := by
    simpa [prefixWord, tailWord_736638, baseEnd_736638] using wordTrace_append hprefix tailTrace_736638
  have hstable : (prefixWord ++ tailWord_736638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736638).length < 2 ^ (prefixWord ++ tailWord_736638).sum := by decide
  have hdescent : baseEnd_736638 < baseStart_736638 := by decide
  rcases family_descends (prefixWord ++ tailWord_736638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736697 : List Nat := [1, 2, 1, 4, 5, 1, 2, 4]
def baseStart_736697 : Nat := 118140960795 + 736697 * 2 ^ 59
def prefixEnd_736697 : Nat := 4983230072969 + 3 ^ 40 * 736697 * 2
def baseEnd_736697 : Nat := 112082861548269452829481

theorem tailTrace_736697 : CollatzResearch.WordTrace tailWord_736697 prefixEnd_736697 112082861548269452829481 := by
  unfold tailWord_736697
  simp only [CollatzResearch.WordTrace]
  refine ⟨26869547012080061675840345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17913031341386707783893563 26869547012080061675840345)
  ·
    refine ⟨20152160259060046256880259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26869547012080061675840345 20152160259060046256880259)
    ·
      refine ⟨30228240388590069385320389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20152160259060046256880259 30228240388590069385320389)
      ·
        refine ⟨5667795072860638009747573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30228240388590069385320389 5667795072860638009747573)
        ·
          refine ⟨531355788080684813413835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5667795072860638009747573 531355788080684813413835)
          ·
            refine ⟨797033682121027220120753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531355788080684813413835 797033682121027220120753)
            ·
              refine ⟨597775261590770415090565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797033682121027220120753 597775261590770415090565)
              ·
                refine ⟨112082861548269452829481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 597775261590770415090565 112082861548269452829481)
                ·
                  rfl

theorem cell20_736697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4].length) (baseStart_736697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736697 prefixEnd_736697 := by exact prefixLift 736697
  have htrace : WordTrace (prefixWord ++ tailWord_736697) baseStart_736697 baseEnd_736697 := by
    simpa [prefixWord, tailWord_736697, baseEnd_736697] using wordTrace_append hprefix tailTrace_736697
  have hstable : (prefixWord ++ tailWord_736697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736697).length < 2 ^ (prefixWord ++ tailWord_736697).sum := by decide
  have hdescent : baseEnd_736697 < baseStart_736697 := by decide
  rcases family_descends (prefixWord ++ tailWord_736697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736739 : List Nat := [1, 1, 1, 6, 2, 2, 2, 5]
def baseStart_736739 : Nat := 118140960795 + 736739 * 2 ^ 59
def prefixEnd_736739 : Nat := 4983230072969 + 3 ^ 40 * 736739 * 2
def baseEnd_736739 : Nat := 112089251529747626362757

theorem tailTrace_736739 : CollatzResearch.WordTrace tailWord_736739 prefixEnd_736739 112089251529747626362757 := by
  unfold tailWord_736739
  simp only [CollatzResearch.WordTrace]
  refine ⟨26871078877927902848869271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17914052585285268565912847 26871078877927902848869271)
  ·
    refine ⟨40306618316891854273303907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26871078877927902848869271 40306618316891854273303907)
    ·
      refine ⟨60459927475337781409955861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40306618316891854273303907 60459927475337781409955861)
      ·
        refine ⟨2834059100406458503591681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60459927475337781409955861 2834059100406458503591681)
        ·
          refine ⟨2125544325304843877693761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2834059100406458503591681 2125544325304843877693761)
          ·
            refine ⟨1594158243978632908270321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2125544325304843877693761 1594158243978632908270321)
            ·
              refine ⟨1195618682983974681202741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594158243978632908270321 1195618682983974681202741)
              ·
                refine ⟨112089251529747626362757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1195618682983974681202741 112089251529747626362757)
                ·
                  rfl

theorem cell20_736739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_736739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736739 prefixEnd_736739 := by exact prefixLift 736739
  have htrace : WordTrace (prefixWord ++ tailWord_736739) baseStart_736739 baseEnd_736739 := by
    simpa [prefixWord, tailWord_736739, baseEnd_736739] using wordTrace_append hprefix tailTrace_736739
  have hstable : (prefixWord ++ tailWord_736739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736739).length < 2 ^ (prefixWord ++ tailWord_736739).sum := by decide
  have hdescent : baseEnd_736739 < baseStart_736739 := by decide
  rcases family_descends (prefixWord ++ tailWord_736739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736760 : List Nat := [2, 1, 2, 1, 1, 5, 2, 6]
def baseStart_736760 : Nat := 118140960795 + 736760 * 2 ^ 59
def prefixEnd_736760 : Nat := 4983230072969 + 3 ^ 40 * 736760 * 2
def baseEnd_736760 : Nat := 112092446520486713129395

theorem tailTrace_736760 : CollatzResearch.WordTrace tailWord_736760 prefixEnd_736760 112092446520486713129395 := by
  unfold tailWord_736760
  simp only [CollatzResearch.WordTrace]
  refine ⟨13435922405425911717691867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17914563207234548956922489 13435922405425911717691867)
  ·
    refine ⟨20153883608138867576537801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13435922405425911717691867 20153883608138867576537801)
    ·
      refine ⟨15115412706104150682403351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20153883608138867576537801 15115412706104150682403351)
      ·
        refine ⟨22673119059156226023605027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15115412706104150682403351 22673119059156226023605027)
        ·
          refine ⟨34009678588734339035407541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22673119059156226023605027 34009678588734339035407541)
          ·
            refine ⟨3188407367693844284569457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34009678588734339035407541 3188407367693844284569457)
            ·
              refine ⟨2391305525770383213427093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3188407367693844284569457 2391305525770383213427093)
              ·
                refine ⟨112092446520486713129395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2391305525770383213427093 112092446520486713129395)
                ·
                  rfl

theorem cell20_736760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_736760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736760 prefixEnd_736760 := by exact prefixLift 736760
  have htrace : WordTrace (prefixWord ++ tailWord_736760) baseStart_736760 baseEnd_736760 := by
    simpa [prefixWord, tailWord_736760, baseEnd_736760] using wordTrace_append hprefix tailTrace_736760
  have hstable : (prefixWord ++ tailWord_736760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736760).length < 2 ^ (prefixWord ++ tailWord_736760).sum := by decide
  have hdescent : baseEnd_736760 < baseStart_736760 := by decide
  rcases family_descends (prefixWord ++ tailWord_736760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736767 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 5]
def baseStart_736767 : Nat := 118140960795 + 736767 * 2 ^ 59
def prefixEnd_736767 : Nat := 4983230072969 + 3 ^ 40 * 736767 * 2
def baseEnd_736767 : Nat := 336280534552199226154823

theorem tailTrace_736767 : CollatzResearch.WordTrace tailWord_736767 prefixEnd_736767 336280534552199226154823 := by
  unfold tailWord_736767
  simp only [CollatzResearch.WordTrace]
  refine ⟨26872100121826463630888555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17914733414550975753925703 26872100121826463630888555)
  ·
    refine ⟨40308150182739695446332833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26872100121826463630888555 40308150182739695446332833)
    ·
      refine ⟨30231112637054771584749625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40308150182739695446332833 30231112637054771584749625)
      ·
        refine ⟨22673334477791078688562219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30231112637054771584749625 22673334477791078688562219)
        ·
          refine ⟨34010001716686618032843329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22673334477791078688562219 34010001716686618032843329)
          ·
            refine ⟨25507501287514963524632497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34010001716686618032843329 25507501287514963524632497)
            ·
              refine ⟨19130625965636222643474373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25507501287514963524632497 19130625965636222643474373)
              ·
                refine ⟨3586992368556791745651445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19130625965636222643474373 3586992368556791745651445)
                ·
                  refine ⟨336280534552199226154823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3586992368556791745651445 336280534552199226154823)
                  ·
                    rfl

theorem cell20_736767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 5].length) (baseStart_736767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736767 prefixEnd_736767 := by exact prefixLift 736767
  have htrace : WordTrace (prefixWord ++ tailWord_736767) baseStart_736767 baseEnd_736767 := by
    simpa [prefixWord, tailWord_736767, baseEnd_736767] using wordTrace_append hprefix tailTrace_736767
  have hstable : (prefixWord ++ tailWord_736767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736767).length < 2 ^ (prefixWord ++ tailWord_736767).sum := by decide
  have hdescent : baseEnd_736767 < baseStart_736767 := by decide
  rcases family_descends (prefixWord ++ tailWord_736767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736787 : List Nat := [1, 1, 1, 2, 1, 6, 4, 2, 2]
def baseStart_736787 : Nat := 118140960795 + 736787 * 2 ^ 59
def prefixEnd_736787 : Nat := 4983230072969 + 3 ^ 40 * 736787 * 2
def baseEnd_736787 : Nat := 336289663097168045488075

theorem tailTrace_736787 : CollatzResearch.WordTrace tailWord_736787 prefixEnd_736787 336289663097168045488075 := by
  unfold tailWord_736787
  simp only [CollatzResearch.WordTrace]
  refine ⟨26872829581754007046616615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17915219721169338031077743 26872829581754007046616615)
  ·
    refine ⟨40309244372631010569924923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26872829581754007046616615 40309244372631010569924923)
    ·
      refine ⟨60463866558946515854887385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40309244372631010569924923 60463866558946515854887385)
      ·
        refine ⟨45347899919209886891165539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60463866558946515854887385 45347899919209886891165539)
        ·
          refine ⟨68021849878814830336748309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45347899919209886891165539 68021849878814830336748309)
          ·
            refine ⟨3188524213069445172035077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 68021849878814830336748309 3188524213069445172035077)
            ·
              refine ⟨597848289950520969756577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3188524213069445172035077 597848289950520969756577)
              ·
                refine ⟨448386217462890727317433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597848289950520969756577 448386217462890727317433)
                ·
                  refine ⟨336289663097168045488075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448386217462890727317433 336289663097168045488075)
                  ·
                    rfl

theorem cell20_736787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 2, 2].length) (baseStart_736787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736787 prefixEnd_736787 := by exact prefixLift 736787
  have htrace : WordTrace (prefixWord ++ tailWord_736787) baseStart_736787 baseEnd_736787 := by
    simpa [prefixWord, tailWord_736787, baseEnd_736787] using wordTrace_append hprefix tailTrace_736787
  have hstable : (prefixWord ++ tailWord_736787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736787).length < 2 ^ (prefixWord ++ tailWord_736787).sum := by decide
  have hdescent : baseEnd_736787 < baseStart_736787 := by decide
  rcases family_descends (prefixWord ++ tailWord_736787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736805 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_736805 : Nat := 118140960795 + 736805 * 2 ^ 59
def prefixEnd_736805 : Nat := 4983230072969 + 3 ^ 40 * 736805 * 2
def baseEnd_736805 : Nat := 336297878787639982888001

theorem tailTrace_736805 : CollatzResearch.WordTrace tailWord_736805 prefixEnd_736805 336297878787639982888001 := by
  unfold tailWord_736805
  simp only [CollatzResearch.WordTrace]
  refine ⟨26873486095688796120771869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17915657397125864080514579 26873486095688796120771869)
  ·
    refine ⟨10077557285883298545289451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26873486095688796120771869 10077557285883298545289451)
    ·
      refine ⟨15116335928824947817934177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10077557285883298545289451 15116335928824947817934177)
      ·
        refine ⟨11337251946618710863450633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15116335928824947817934177 11337251946618710863450633)
        ·
          refine ⟨8502938959964033147587975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11337251946618710863450633 8502938959964033147587975)
          ·
            refine ⟨12754408439946049721381963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8502938959964033147587975 12754408439946049721381963)
            ·
              refine ⟨19131612659919074582072945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12754408439946049721381963 19131612659919074582072945)
              ·
                refine ⟨14348709494939305936554709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19131612659919074582072945 14348709494939305936554709)
                ·
                  refine ⟨336297878787639982888001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14348709494939305936554709 336297878787639982888001)
                  ·
                    rfl

theorem cell20_736805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_736805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736805 prefixEnd_736805 := by exact prefixLift 736805
  have htrace : WordTrace (prefixWord ++ tailWord_736805) baseStart_736805 baseEnd_736805 := by
    simpa [prefixWord, tailWord_736805, baseEnd_736805] using wordTrace_append hprefix tailTrace_736805
  have hstable : (prefixWord ++ tailWord_736805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736805).length < 2 ^ (prefixWord ++ tailWord_736805).sum := by decide
  have hdescent : baseEnd_736805 < baseStart_736805 := by decide
  rcases family_descends (prefixWord ++ tailWord_736805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736825 : List Nat := [1, 2, 1, 5, 1, 3, 2, 3, 2]
def baseStart_736825 : Nat := 118140960795 + 736825 * 2 ^ 59
def prefixEnd_736825 : Nat := 4983230072969 + 3 ^ 40 * 736825 * 2
def baseEnd_736825 : Nat := 336307007332608802221253

theorem tailTrace_736825 : CollatzResearch.WordTrace tailWord_736825 prefixEnd_736825 336307007332608802221253 := by
  unfold tailWord_736825
  simp only [CollatzResearch.WordTrace]
  refine ⟨26874215555616339536499929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17916143703744226357666619 26874215555616339536499929)
  ·
    refine ⟨20155661666712254652374947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26874215555616339536499929 20155661666712254652374947)
    ·
      refine ⟨30233492500068381978562421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20155661666712254652374947 30233492500068381978562421)
      ·
        refine ⟨2834389921881410810490227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30233492500068381978562421 2834389921881410810490227)
        ·
          refine ⟨4251584882822116215735341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834389921881410810490227 4251584882822116215735341)
          ·
            refine ⟨1594344331058293580900753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4251584882822116215735341 1594344331058293580900753)
            ·
              refine ⟨1195758248293720185675565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594344331058293580900753 1195758248293720185675565)
              ·
                refine ⟨448409343110145069628337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1195758248293720185675565 448409343110145069628337)
                ·
                  refine ⟨336307007332608802221253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448409343110145069628337 336307007332608802221253)
                  ·
                    rfl

theorem cell20_736825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3, 2].length) (baseStart_736825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736825 prefixEnd_736825 := by exact prefixLift 736825
  have htrace : WordTrace (prefixWord ++ tailWord_736825) baseStart_736825 baseEnd_736825 := by
    simpa [prefixWord, tailWord_736825, baseEnd_736825] using wordTrace_append hprefix tailTrace_736825
  have hstable : (prefixWord ++ tailWord_736825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736825).length < 2 ^ (prefixWord ++ tailWord_736825).sum := by decide
  have hdescent : baseEnd_736825 < baseStart_736825 := by decide
  rcases family_descends (prefixWord ++ tailWord_736825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736867 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_736867 : Nat := 118140960795 + 736867 * 2 ^ 59
def prefixEnd_736867 : Nat := 4983230072969 + 3 ^ 40 * 736867 * 2
def baseEnd_736867 : Nat := 336326177277043322821081

theorem tailTrace_736867 : CollatzResearch.WordTrace tailWord_736867 prefixEnd_736867 336326177277043322821081 := by
  unfold tailWord_736867
  simp only [CollatzResearch.WordTrace]
  refine ⟨26875747421464180709528855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17917164947642787139685903 26875747421464180709528855)
  ·
    refine ⟨40313621132196271064293283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26875747421464180709528855 40313621132196271064293283)
    ·
      refine ⟨60470431698294406596439925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40313621132196271064293283 60470431698294406596439925)
      ·
        refine ⟨5669102971715100618416243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60470431698294406596439925 5669102971715100618416243)
        ·
          refine ⟨8503654457572650927624365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5669102971715100618416243 8503654457572650927624365)
          ·
            refine ⟨3188870421589744097859137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8503654457572650927624365 3188870421589744097859137)
            ·
              refine ⟨2391652816192308073394353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3188870421589744097859137 2391652816192308073394353)
              ·
                refine ⟨1793739612144231055045765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391652816192308073394353 1793739612144231055045765)
                ·
                  refine ⟨336326177277043322821081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1793739612144231055045765 336326177277043322821081)
                  ·
                    rfl

theorem cell20_736867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_736867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736867 prefixEnd_736867 := by exact prefixLift 736867
  have htrace : WordTrace (prefixWord ++ tailWord_736867) baseStart_736867 baseEnd_736867 := by
    simpa [prefixWord, tailWord_736867, baseEnd_736867] using wordTrace_append hprefix tailTrace_736867
  have hstable : (prefixWord ++ tailWord_736867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736867).length < 2 ^ (prefixWord ++ tailWord_736867).sum := by decide
  have hdescent : baseEnd_736867 < baseStart_736867 := by decide
  rcases family_descends (prefixWord ++ tailWord_736867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736901 : List Nat := [1, 3, 1, 1, 4, 1, 5, 2, 2]
def baseStart_736901 : Nat := 118140960795 + 736901 * 2 ^ 59
def prefixEnd_736901 : Nat := 4983230072969 + 3 ^ 40 * 736901 * 2
def baseEnd_736901 : Nat := 336341695803490315687609

theorem tailTrace_736901 : CollatzResearch.WordTrace tailWord_736901 prefixEnd_736901 336341695803490315687609 := by
  unfold tailWord_736901
  simp only [CollatzResearch.WordTrace]
  refine ⟨26876987503341004516266557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17917991668894003010844371 26876987503341004516266557)
  ·
    refine ⟨10078870313752876693599959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26876987503341004516266557 10078870313752876693599959)
    ·
      refine ⟨15118305470629315040399939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10078870313752876693599959 15118305470629315040399939)
      ·
        refine ⟨22677458205943972560599909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15118305470629315040399939 22677458205943972560599909)
        ·
          refine ⟨4252023413614494855112483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22677458205943972560599909 4252023413614494855112483)
          ·
            refine ⟨6378035120421742282668725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252023413614494855112483 6378035120421742282668725)
            ·
              refine ⟨597940792539538339000193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6378035120421742282668725 597940792539538339000193)
              ·
                refine ⟨448455594404653754250145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597940792539538339000193 448455594404653754250145)
                ·
                  refine ⟨336341695803490315687609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448455594404653754250145 336341695803490315687609)
                  ·
                    rfl

theorem cell20_736901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_736901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736901 prefixEnd_736901 := by exact prefixLift 736901
  have htrace : WordTrace (prefixWord ++ tailWord_736901) baseStart_736901 baseEnd_736901 := by
    simpa [prefixWord, tailWord_736901, baseEnd_736901] using wordTrace_append hprefix tailTrace_736901
  have hstable : (prefixWord ++ tailWord_736901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736901).length < 2 ^ (prefixWord ++ tailWord_736901).sum := by decide
  have hdescent : baseEnd_736901 < baseStart_736901 := by decide
  rcases family_descends (prefixWord ++ tailWord_736901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736905 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 4]
def baseStart_736905 : Nat := 118140960795 + 736905 * 2 ^ 59
def prefixEnd_736905 : Nat := 4983230072969 + 3 ^ 40 * 736905 * 2
def baseEnd_736905 : Nat := 336343521512484079554259

theorem tailTrace_736905 : CollatzResearch.WordTrace tailWord_736905 prefixEnd_736905 336343521512484079554259 := by
  unfold tailWord_736905
  simp only [CollatzResearch.WordTrace]
  refine ⟨26877133395326513199412169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17918088930217675466274779 26877133395326513199412169)
  ·
    refine ⟨20157850046494884899559127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26877133395326513199412169 20157850046494884899559127)
    ·
      refine ⟨30236775069742327349338691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20157850046494884899559127 30236775069742327349338691)
      ·
        refine ⟨45355162604613491024008037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30236775069742327349338691 45355162604613491024008037)
        ·
          refine ⟨8504092988365029567001507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45355162604613491024008037 8504092988365029567001507)
          ·
            refine ⟨12756139482547544350502261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8504092988365029567001507 12756139482547544350502261)
            ·
              refine ⟨1195888076488832282859587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12756139482547544350502261 1195888076488832282859587)
              ·
                refine ⟨1793832114733248424289381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195888076488832282859587 1793832114733248424289381)
                ·
                  refine ⟨336343521512484079554259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1793832114733248424289381 336343521512484079554259)
                  ·
                    rfl

theorem cell20_736905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 4].length) (baseStart_736905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736905 prefixEnd_736905 := by exact prefixLift 736905
  have htrace : WordTrace (prefixWord ++ tailWord_736905) baseStart_736905 baseEnd_736905 := by
    simpa [prefixWord, tailWord_736905, baseEnd_736905] using wordTrace_append hprefix tailTrace_736905
  have hstable : (prefixWord ++ tailWord_736905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736905).length < 2 ^ (prefixWord ++ tailWord_736905).sum := by decide
  have hdescent : baseEnd_736905 < baseStart_736905 := by decide
  rcases family_descends (prefixWord ++ tailWord_736905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736956 : List Nat := [2, 2, 2, 3, 1, 4, 2, 2, 2]
def baseStart_736956 : Nat := 118140960795 + 736956 * 2 ^ 59
def prefixEnd_736956 : Nat := 4983230072969 + 3 ^ 40 * 736956 * 2
def baseEnd_736956 : Nat := 336366799302154568854051

theorem tailTrace_736956 : CollatzResearch.WordTrace tailWord_736956 prefixEnd_736956 336366799302154568854051 := by
  unfold tailWord_736956
  simp only [CollatzResearch.WordTrace]
  refine ⟨13439496759070874454759361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17919329012094499273012481 13439496759070874454759361)
  ·
    refine ⟨10079622569303155841069521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13439496759070874454759361 10079622569303155841069521)
    ·
      refine ⟨7559716926977366880802141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10079622569303155841069521 7559716926977366880802141)
      ·
        refine ⟨2834893847616512580300803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7559716926977366880802141 2834893847616512580300803)
        ·
          refine ⟨4252340771424768870451205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834893847616512580300803 4252340771424768870451205)
          ·
            refine ⟨797313894642144163209601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4252340771424768870451205 797313894642144163209601)
            ·
              refine ⟨597985420981608122407201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 797313894642144163209601 597985420981608122407201)
              ·
                refine ⟨448489065736206091805401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597985420981608122407201 448489065736206091805401)
                ·
                  refine ⟨336366799302154568854051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448489065736206091805401 336366799302154568854051)
                  ·
                    rfl

theorem cell20_736956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_736956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736956 prefixEnd_736956 := by exact prefixLift 736956
  have htrace : WordTrace (prefixWord ++ tailWord_736956) baseStart_736956 baseEnd_736956 := by
    simpa [prefixWord, tailWord_736956, baseEnd_736956] using wordTrace_append hprefix tailTrace_736956
  have hstable : (prefixWord ++ tailWord_736956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736956).length < 2 ^ (prefixWord ++ tailWord_736956).sum := by decide
  have hdescent : baseEnd_736956 < baseStart_736956 := by decide
  rcases family_descends (prefixWord ++ tailWord_736956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736960 : List Nat := [2, 1, 1, 2, 4, 1, 3, 4, 2]
def baseStart_736960 : Nat := 118140960795 + 736960 * 2 ^ 59
def prefixEnd_736960 : Nat := 4983230072969 + 3 ^ 40 * 736960 * 2
def baseEnd_736960 : Nat := 336368625011148332720701

theorem tailTrace_736960 : CollatzResearch.WordTrace tailWord_736960 prefixEnd_736960 336368625011148332720701 := by
  unfold tailWord_736960
  simp only [CollatzResearch.WordTrace]
  refine ⟨13439569705063628796332167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17919426273418171728442889 13439569705063628796332167)
  ·
    refine ⟨20159354557595443194498251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13439569705063628796332167 20159354557595443194498251)
    ·
      refine ⟨30239031836393164791747377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20159354557595443194498251 30239031836393164791747377)
      ·
        refine ⟨22679273877294873593810533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30239031836393164791747377 22679273877294873593810533)
        ·
          refine ⟨4252363851992788798839475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22679273877294873593810533 4252363851992788798839475)
          ·
            refine ⟨6378545777989183198259213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252363851992788798839475 6378545777989183198259213)
            ·
              refine ⟨2391954666745943699347205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6378545777989183198259213 2391954666745943699347205)
              ·
                refine ⟨448491500014864443627601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2391954666745943699347205 448491500014864443627601)
                ·
                  refine ⟨336368625011148332720701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448491500014864443627601 336368625011148332720701)
                  ·
                    rfl

theorem cell20_736960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_736960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736960 prefixEnd_736960 := by exact prefixLift 736960
  have htrace : WordTrace (prefixWord ++ tailWord_736960) baseStart_736960 baseEnd_736960 := by
    simpa [prefixWord, tailWord_736960, baseEnd_736960] using wordTrace_append hprefix tailTrace_736960
  have hstable : (prefixWord ++ tailWord_736960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736960).length < 2 ^ (prefixWord ++ tailWord_736960).sum := by decide
  have hdescent : baseEnd_736960 < baseStart_736960 := by decide
  rcases family_descends (prefixWord ++ tailWord_736960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_736974 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_736974 : Nat := 118140960795 + 736974 * 2 ^ 59
def prefixEnd_736974 : Nat := 4983230072969 + 3 ^ 40 * 736974 * 2
def baseEnd_736974 : Nat := 336375014992626506253977

theorem tailTrace_736974 : CollatzResearch.WordTrace tailWord_736974 prefixEnd_736974 336375014992626506253977 := by
  unfold tailWord_736974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359956254009567247959247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17919766688051025322449317 3359956254009567247959247)
  ·
    refine ⟨5039934381014350871938871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3359956254009567247959247 5039934381014350871938871)
    ·
      refine ⟨7559901571521526307908307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5039934381014350871938871 7559901571521526307908307)
      ·
        refine ⟨11339852357282289461862461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7559901571521526307908307 11339852357282289461862461)
        ·
          refine ⟨4252444633980858548198423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11339852357282289461862461 4252444633980858548198423)
          ·
            refine ⟨6378666950971287822297635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4252444633980858548198423 6378666950971287822297635)
            ·
              refine ⟨9568000426456931733446453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6378666950971287822297635 9568000426456931733446453)
              ·
                refine ⟨897000039980337350010605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9568000426456931733446453 897000039980337350010605)
                ·
                  refine ⟨336375014992626506253977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897000039980337350010605 336375014992626506253977)
                  ·
                    rfl

theorem cell20_736974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_736974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_736974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_736974 prefixEnd_736974 := by exact prefixLift 736974
  have htrace : WordTrace (prefixWord ++ tailWord_736974) baseStart_736974 baseEnd_736974 := by
    simpa [prefixWord, tailWord_736974, baseEnd_736974] using wordTrace_append hprefix tailTrace_736974
  have hstable : (prefixWord ++ tailWord_736974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_736974).length < 2 ^ (prefixWord ++ tailWord_736974).sum := by decide
  have hdescent : baseEnd_736974 < baseStart_736974 := by decide
  rcases family_descends (prefixWord ++ tailWord_736974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737064 : List Nat := [2, 1, 5, 1, 1, 2, 8]
def baseStart_737064 : Nat := 118140960795 + 737064 * 2 ^ 59
def prefixEnd_737064 : Nat := 4983230072969 + 3 ^ 40 * 737064 * 2
def baseEnd_737064 : Nat := 37379565938331799250401

theorem tailTrace_737064 : CollatzResearch.WordTrace tailWord_737064 prefixEnd_737064 37379565938331799250401 := by
  unfold tailWord_737064
  simp only [CollatzResearch.WordTrace]
  refine ⟨13441466300875241677225123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17921955067833655569633497 13441466300875241677225123)
  ·
    refine ⟨20162199451312862515837685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13441466300875241677225123 20162199451312862515837685)
    ·
      refine ⟨1890206198560580860859783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20162199451312862515837685 1890206198560580860859783)
      ·
        refine ⟨2835309297840871291289675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1890206198560580860859783 2835309297840871291289675)
        ·
          refine ⟨4252963946761306936934513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2835309297840871291289675 4252963946761306936934513)
          ·
            refine ⟨3189722960070980202700885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4252963946761306936934513 3189722960070980202700885)
            ·
              refine ⟨37379565938331799250401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3189722960070980202700885 37379565938331799250401)
              ·
                rfl

theorem cell20_737064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 8].length) (baseStart_737064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737064 prefixEnd_737064 := by exact prefixLift 737064
  have htrace : WordTrace (prefixWord ++ tailWord_737064) baseStart_737064 baseEnd_737064 := by
    simpa [prefixWord, tailWord_737064, baseEnd_737064] using wordTrace_append hprefix tailTrace_737064
  have hstable : (prefixWord ++ tailWord_737064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737064).length < 2 ^ (prefixWord ++ tailWord_737064).sum := by decide
  have hdescent : baseEnd_737064 < baseStart_737064 := by decide
  rcases family_descends (prefixWord ++ tailWord_737064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737070 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_737070 : Nat := 118140960795 + 737070 * 2 ^ 59
def prefixEnd_737070 : Nat := 4983230072969 + 3 ^ 40 * 737070 * 2
def baseEnd_737070 : Nat := 336418832008476839053585

theorem tailTrace_737070 : CollatzResearch.WordTrace tailWord_737070 prefixEnd_737070 336418832008476839053585 := by
  unfold tailWord_737070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360393929966093297396083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17922100959819164252779109 3360393929966093297396083)
  ·
    refine ⟨5040590894949139946094125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3360393929966093297396083 5040590894949139946094125)
    ·
      refine ⟨1890221585605927479785297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5040590894949139946094125 1890221585605927479785297)
      ·
        refine ⟨1417666189204445609838973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1890221585605927479785297 1417666189204445609838973)
        ·
          refine ⟨531624820951667103689615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1417666189204445609838973 531624820951667103689615)
          ·
            refine ⟨797437231427500655534423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 531624820951667103689615 797437231427500655534423)
            ·
              refine ⟨1196155847141250983301635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797437231427500655534423 1196155847141250983301635)
              ·
                refine ⟨1794233770711876474952453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196155847141250983301635 1794233770711876474952453)
                ·
                  refine ⟨336418832008476839053585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794233770711876474952453 336418832008476839053585)
                  ·
                    rfl

theorem cell20_737070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_737070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737070 prefixEnd_737070 := by exact prefixLift 737070
  have htrace : WordTrace (prefixWord ++ tailWord_737070) baseStart_737070 baseEnd_737070 := by
    simpa [prefixWord, tailWord_737070, baseEnd_737070] using wordTrace_append hprefix tailTrace_737070
  have hstable : (prefixWord ++ tailWord_737070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737070).length < 2 ^ (prefixWord ++ tailWord_737070).sum := by decide
  have hdescent : baseEnd_737070 < baseStart_737070 := by decide
  rcases family_descends (prefixWord ++ tailWord_737070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737074 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_737074 : Nat := 118140960795 + 737074 * 2 ^ 59
def prefixEnd_737074 : Nat := 4983230072969 + 3 ^ 40 * 737074 * 2
def baseEnd_737074 : Nat := 336420657717470602920235

theorem tailTrace_737074 : CollatzResearch.WordTrace tailWord_737074 prefixEnd_737074 336420657717470602920235 := by
  unfold tailWord_737074
  simp only [CollatzResearch.WordTrace]
  refine ⟨6720824332928563765578569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17922198221142836708209517 6720824332928563765578569)
  ·
    refine ⟨5040618249696422824183927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6720824332928563765578569 5040618249696422824183927)
    ·
      refine ⟨7560927374544634236275891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5040618249696422824183927 7560927374544634236275891)
      ·
        refine ⟨11341391061816951354413837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7560927374544634236275891 11341391061816951354413837)
        ·
          refine ⟨4253021648181356757905189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11341391061816951354413837 4253021648181356757905189)
          ·
            refine ⟨797441559034004392107223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4253021648181356757905189 797441559034004392107223)
            ·
              refine ⟨1196162338551006588160835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797441559034004392107223 1196162338551006588160835)
              ·
                refine ⟨1794243507826509882241253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196162338551006588160835 1794243507826509882241253)
                ·
                  refine ⟨336420657717470602920235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794243507826509882241253 336420657717470602920235)
                  ·
                    rfl

theorem cell20_737074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_737074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737074 prefixEnd_737074 := by exact prefixLift 737074
  have htrace : WordTrace (prefixWord ++ tailWord_737074) baseStart_737074 baseEnd_737074 := by
    simpa [prefixWord, tailWord_737074, baseEnd_737074] using wordTrace_append hprefix tailTrace_737074
  have hstable : (prefixWord ++ tailWord_737074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737074).length < 2 ^ (prefixWord ++ tailWord_737074).sum := by decide
  have hdescent : baseEnd_737074 < baseStart_737074 := by decide
  rcases family_descends (prefixWord ++ tailWord_737074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737123 : List Nat := [1, 1, 1, 5, 12]
def baseStart_737123 : Nat := 118140960795 + 737123 * 2 ^ 59
def prefixEnd_737123 : Nat := 4983230072969 + 3 ^ 40 * 737123 * 2
def baseEnd_737123 : Nat := 4153617563612891485021

theorem tailTrace_737123 : CollatzResearch.WordTrace tailWord_737123 prefixEnd_737123 4153617563612891485021 := by
  unfold tailWord_737123
  simp only [CollatzResearch.WordTrace]
  refine ⟨26885084508536736430848023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17923389672357824287232015 26885084508536736430848023)
  ·
    refine ⟨40327626762805104646272035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26885084508536736430848023 40327626762805104646272035)
    ·
      refine ⟨60491440144207656969408053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40327626762805104646272035 60491440144207656969408053)
      ·
        refine ⟨5671072513519467840882005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60491440144207656969408053 5671072513519467840882005)
        ·
          refine ⟨4153617563612891485021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5671072513519467840882005 4153617563612891485021)
          ·
            rfl

theorem cell20_737123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 12].length) (baseStart_737123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737123 prefixEnd_737123 := by exact prefixLift 737123
  have htrace : WordTrace (prefixWord ++ tailWord_737123) baseStart_737123 baseEnd_737123 := by
    simpa [prefixWord, tailWord_737123, baseEnd_737123] using wordTrace_append hprefix tailTrace_737123
  have hstable : (prefixWord ++ tailWord_737123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737123).length < 2 ^ (prefixWord ++ tailWord_737123).sum := by decide
  have hdescent : baseEnd_737123 < baseStart_737123 := by decide
  rcases family_descends (prefixWord ++ tailWord_737123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737150 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_737150 : Nat := 118140960795 + 737150 * 2 ^ 59
def prefixEnd_737150 : Nat := 4983230072969 + 3 ^ 40 * 737150 * 2
def baseEnd_737150 : Nat := 336455346188352116386591

theorem tailTrace_737150 : CollatzResearch.WordTrace tailWord_737150 prefixEnd_737150 336455346188352116386591 := by
  unfold tailWord_737150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3360758659929865005260113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17924046186292613361387269 3360758659929865005260113)
  ·
    refine ⟨2520568994947398753945085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3360758659929865005260113 2520568994947398753945085)
    ·
      refine ⟨945213373105274532729407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2520568994947398753945085 945213373105274532729407)
      ·
        refine ⟨1417820059657911799094111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945213373105274532729407 1417820059657911799094111)
        ·
          refine ⟨2126730089486867698641167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417820059657911799094111 2126730089486867698641167)
          ·
            refine ⟨3190095134230301547961751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2126730089486867698641167 3190095134230301547961751)
            ·
              refine ⟨4785142701345452321942627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3190095134230301547961751 4785142701345452321942627)
              ·
                refine ⟨7177714052018178482913941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4785142701345452321942627 7177714052018178482913941)
                ·
                  refine ⟨336455346188352116386591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7177714052018178482913941 336455346188352116386591)
                  ·
                    rfl

theorem cell20_737150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_737150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737150 prefixEnd_737150 := by exact prefixLift 737150
  have htrace : WordTrace (prefixWord ++ tailWord_737150) baseStart_737150 baseEnd_737150 := by
    simpa [prefixWord, tailWord_737150, baseEnd_737150] using wordTrace_append hprefix tailTrace_737150
  have hstable : (prefixWord ++ tailWord_737150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737150).length < 2 ^ (prefixWord ++ tailWord_737150).sum := by decide
  have hdescent : baseEnd_737150 < baseStart_737150 := by decide
  rcases family_descends (prefixWord ++ tailWord_737150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737178 : List Nat := [3, 1, 1, 4, 2, 2, 7]
def baseStart_737178 : Nat := 118140960795 + 737178 * 2 ^ 59
def prefixEnd_737178 : Nat := 4983230072969 + 3 ^ 40 * 737178 * 2
def baseEnd_737178 : Nat := 37385347350145384828127

theorem tailTrace_737178 : CollatzResearch.WordTrace tailWord_737178 prefixEnd_737178 37385347350145384828127 := by
  unfold tailWord_737178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6721772630834370206025047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17924727015558320549400125 6721772630834370206025047)
  ·
    refine ⟨10082658946251555309037571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6721772630834370206025047 10082658946251555309037571)
    ·
      refine ⟨15123988419377332963556357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10082658946251555309037571 15123988419377332963556357)
      ·
        refine ⟨2835747828633249930666817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15123988419377332963556357 2835747828633249930666817)
        ·
          refine ⟨2126810871474937448000113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2835747828633249930666817 2126810871474937448000113)
          ·
            refine ⟨1595108153606203086000085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2126810871474937448000113 1595108153606203086000085)
            ·
              refine ⟨37385347350145384828127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1595108153606203086000085 37385347350145384828127)
              ·
                rfl

theorem cell20_737178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 7].length) (baseStart_737178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737178 prefixEnd_737178 := by exact prefixLift 737178
  have htrace : WordTrace (prefixWord ++ tailWord_737178) baseStart_737178 baseEnd_737178 := by
    simpa [prefixWord, tailWord_737178, baseEnd_737178] using wordTrace_append hprefix tailTrace_737178
  have hstable : (prefixWord ++ tailWord_737178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737178).length < 2 ^ (prefixWord ++ tailWord_737178).sum := by decide
  have hdescent : baseEnd_737178 < baseStart_737178 := by decide
  rcases family_descends (prefixWord ++ tailWord_737178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737181 : List Nat := [1, 4, 2, 1, 2, 4, 1, 2, 3]
def baseStart_737181 : Nat := 118140960795 + 737181 * 2 ^ 59
def prefixEnd_737181 : Nat := 4983230072969 + 3 ^ 40 * 737181 * 2
def baseEnd_737181 : Nat := 336469495433053786353131

theorem tailTrace_737181 : CollatzResearch.WordTrace tailWord_737181 prefixEnd_737181 336469495433053786353131 := by
  unfold tailWord_737181
  simp only [CollatzResearch.WordTrace]
  refine ⟨26887199942326612336459397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17924799961551074890972931 26887199942326612336459397)
  ·
    refine ⟨5041349989186239813086137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26887199942326612336459397 5041349989186239813086137)
    ·
      refine ⟨3781012491889679859814603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5041349989186239813086137 3781012491889679859814603)
      ·
        refine ⟨5671518737834519789721905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3781012491889679859814603 5671518737834519789721905)
        ·
          refine ⟨4253639053375889842291429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5671518737834519789721905 4253639053375889842291429)
          ·
            refine ⟨797557322507979345429643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4253639053375889842291429 797557322507979345429643)
            ·
              refine ⟨1196335983761969018144465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797557322507979345429643 1196335983761969018144465)
              ·
                refine ⟨897251987821476763608349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1196335983761969018144465 897251987821476763608349)
                ·
                  refine ⟨336469495433053786353131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897251987821476763608349 336469495433053786353131)
                  ·
                    rfl

theorem cell20_737181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_737181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737181 prefixEnd_737181 := by exact prefixLift 737181
  have htrace : WordTrace (prefixWord ++ tailWord_737181) baseStart_737181 baseEnd_737181 := by
    simpa [prefixWord, tailWord_737181, baseEnd_737181] using wordTrace_append hprefix tailTrace_737181
  have hstable : (prefixWord ++ tailWord_737181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737181).length < 2 ^ (prefixWord ++ tailWord_737181).sum := by decide
  have hdescent : baseEnd_737181 < baseStart_737181 := by decide
  rcases family_descends (prefixWord ++ tailWord_737181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737188 : List Nat := [2, 3, 1, 2, 1, 3, 2, 4, 2]
def baseStart_737188 : Nat := 118140960795 + 737188 * 2 ^ 59
def prefixEnd_737188 : Nat := 4983230072969 + 3 ^ 40 * 737188 * 2
def baseEnd_737188 : Nat := 336472690423792873119769

theorem tailTrace_737188 : CollatzResearch.WordTrace tailWord_737188 prefixEnd_737188 336472690423792873119769 := by
  unfold tailWord_737188
  simp only [CollatzResearch.WordTrace]
  refine ⟨13443727626650626265982109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17924970168867501687976145 13443727626650626265982109)
  ·
    refine ⟨5041397859993984849743291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13443727626650626265982109 5041397859993984849743291)
    ·
      refine ⟨7562096789990977274614937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5041397859993984849743291 7562096789990977274614937)
      ·
        refine ⟨5671572592493232955961203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7562096789990977274614937 5671572592493232955961203)
        ·
          refine ⟨8507358888739849433941805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5671572592493232955961203 8507358888739849433941805)
          ·
            refine ⟨3190259583277443537728177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8507358888739849433941805 3190259583277443537728177)
            ·
              refine ⟨2392694687458082653296133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3190259583277443537728177 2392694687458082653296133)
              ·
                refine ⟨448630253898390497493025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2392694687458082653296133 448630253898390497493025)
                ·
                  refine ⟨336472690423792873119769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448630253898390497493025 336472690423792873119769)
                  ·
                    rfl

theorem cell20_737188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 2].length) (baseStart_737188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737188 prefixEnd_737188 := by exact prefixLift 737188
  have htrace : WordTrace (prefixWord ++ tailWord_737188) baseStart_737188 baseEnd_737188 := by
    simpa [prefixWord, tailWord_737188, baseEnd_737188] using wordTrace_append hprefix tailTrace_737188
  have hstable : (prefixWord ++ tailWord_737188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737188).length < 2 ^ (prefixWord ++ tailWord_737188).sum := by decide
  have hdescent : baseEnd_737188 < baseStart_737188 := by decide
  rcases family_descends (prefixWord ++ tailWord_737188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737199 : List Nat := [1, 1, 2, 1, 2, 2, 4, 7]
def baseStart_737199 : Nat := 118140960795 + 737199 * 2 ^ 59
def prefixEnd_737199 : Nat := 4983230072969 + 3 ^ 40 * 737199 * 2
def baseEnd_737199 : Nat := 112159237041175241251019

theorem tailTrace_737199 : CollatzResearch.WordTrace tailWord_737199 prefixEnd_737199 112159237041175241251019 := by
  unfold tailWord_737199
  simp only [CollatzResearch.WordTrace]
  refine ⟨26887856456261401410614651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17925237637507600940409767 26887856456261401410614651)
  ·
    refine ⟨40331784684392102115921977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26887856456261401410614651 40331784684392102115921977)
    ·
      refine ⟨30248838513294076586941483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40331784684392102115921977 30248838513294076586941483)
      ·
        refine ⟨45373257769941114880412225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30248838513294076586941483 45373257769941114880412225)
        ·
          refine ⟨34029943327455836160309169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45373257769941114880412225 34029943327455836160309169)
          ·
            refine ⟨25522457495591877120231877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34029943327455836160309169 25522457495591877120231877)
            ·
              refine ⟨4785460780423476960043477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25522457495591877120231877 4785460780423476960043477)
              ·
                refine ⟨112159237041175241251019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4785460780423476960043477 112159237041175241251019)
                ·
                  rfl

theorem cell20_737199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 7].length) (baseStart_737199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737199 prefixEnd_737199 := by exact prefixLift 737199
  have htrace : WordTrace (prefixWord ++ tailWord_737199) baseStart_737199 baseEnd_737199 := by
    simpa [prefixWord, tailWord_737199, baseEnd_737199] using wordTrace_append hprefix tailTrace_737199
  have hstable : (prefixWord ++ tailWord_737199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737199).length < 2 ^ (prefixWord ++ tailWord_737199).sum := by decide
  have hdescent : baseEnd_737199 < baseStart_737199 := by decide
  rcases family_descends (prefixWord ++ tailWord_737199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737226 : List Nat := [3, 1, 2, 1, 2, 1, 5, 3, 2]
def baseStart_737226 : Nat := 118140960795 + 737226 * 2 ^ 59
def prefixEnd_737226 : Nat := 4983230072969 + 3 ^ 40 * 737226 * 2
def baseEnd_737226 : Nat := 336490034659233629852947

theorem tailTrace_737226 : CollatzResearch.WordTrace tailWord_737226 prefixEnd_737226 336490034659233629852947 := by
  unfold tailWord_737226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722210306790896255461883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17925894151442390014565021 6722210306790896255461883)
  ·
    refine ⟨10083315460186344383192825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6722210306790896255461883 10083315460186344383192825)
    ·
      refine ⟨7562486595139758287394619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10083315460186344383192825 7562486595139758287394619)
      ·
        refine ⟨11343729892709637431091929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7562486595139758287394619 11343729892709637431091929)
        ·
          refine ⟨8507797419532228073318947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11343729892709637431091929 8507797419532228073318947)
          ·
            refine ⟨12761696129298342109978421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8507797419532228073318947 12761696129298342109978421)
            ·
              refine ⟨1196409012121719572810477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12761696129298342109978421 1196409012121719572810477)
              ·
                refine ⟨448653379545644839803929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196409012121719572810477 448653379545644839803929)
                ·
                  refine ⟨336490034659233629852947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448653379545644839803929 336490034659233629852947)
                  ·
                    rfl

theorem cell20_737226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_737226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737226 prefixEnd_737226 := by exact prefixLift 737226
  have htrace : WordTrace (prefixWord ++ tailWord_737226) baseStart_737226 baseEnd_737226 := by
    simpa [prefixWord, tailWord_737226, baseEnd_737226] using wordTrace_append hprefix tailTrace_737226
  have hstable : (prefixWord ++ tailWord_737226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737226).length < 2 ^ (prefixWord ++ tailWord_737226).sum := by decide
  have hdescent : baseEnd_737226 < baseStart_737226 := by decide
  rcases family_descends (prefixWord ++ tailWord_737226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737247 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 4]
def baseStart_737247 : Nat := 118140960795 + 737247 * 2 ^ 59
def prefixEnd_737247 : Nat := 4983230072969 + 3 ^ 40 * 737247 * 2
def baseEnd_737247 : Nat := 336499619631450890152861

theorem tailTrace_737247 : CollatzResearch.WordTrace tailWord_737247 prefixEnd_737247 336499619631450890152861 := by
  unfold tailWord_737247
  simp only [CollatzResearch.WordTrace]
  refine ⟨26889607160087505608361995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17926404773391670405574663 26889607160087505608361995)
  ·
    refine ⟨40334410740131258412542993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26889607160087505608361995 40334410740131258412542993)
    ·
      refine ⟨30250808055098443809407245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40334410740131258412542993 30250808055098443809407245)
      ·
        refine ⟨11344053020661916428527717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30250808055098443809407245 11344053020661916428527717)
        ·
          refine ⟨2127009941374109330348947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11344053020661916428527717 2127009941374109330348947)
          ·
            refine ⟨3190514912061163995523421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127009941374109330348947 3190514912061163995523421)
            ·
              refine ⟨1196443092022936498321283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3190514912061163995523421 1196443092022936498321283)
              ·
                refine ⟨1794664638034404747481925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196443092022936498321283 1794664638034404747481925)
                ·
                  refine ⟨336499619631450890152861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1794664638034404747481925 336499619631450890152861)
                  ·
                    rfl

theorem cell20_737247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 4].length) (baseStart_737247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737247 prefixEnd_737247 := by exact prefixLift 737247
  have htrace : WordTrace (prefixWord ++ tailWord_737247) baseStart_737247 baseEnd_737247 := by
    simpa [prefixWord, tailWord_737247, baseEnd_737247] using wordTrace_append hprefix tailTrace_737247
  have hstable : (prefixWord ++ tailWord_737247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737247).length < 2 ^ (prefixWord ++ tailWord_737247).sum := by decide
  have hdescent : baseEnd_737247 < baseStart_737247 := by decide
  rcases family_descends (prefixWord ++ tailWord_737247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737250 : List Nat := [3, 3, 3, 1, 2, 1, 2, 5]
def baseStart_737250 : Nat := 118140960795 + 737250 * 2 ^ 59
def prefixEnd_737250 : Nat := 4983230072969 + 3 ^ 40 * 737250 * 2
def baseEnd_737250 : Nat := 112166996304398737684283

theorem tailTrace_737250 : CollatzResearch.WordTrace tailWord_737250 prefixEnd_737250 112166996304398737684283 := by
  unfold tailWord_737250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6722429144769159280180301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17926477719384424747147469 6722429144769159280180301)
  ·
    refine ⟨2520910929288434730067613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6722429144769159280180301 2520910929288434730067613)
    ·
      refine ⟨945341598483163023775355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2520910929288434730067613 945341598483163023775355)
      ·
        refine ⟨1418012397724744535663033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 945341598483163023775355 1418012397724744535663033)
        ·
          refine ⟨1063509298293558401747275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1418012397724744535663033 1063509298293558401747275)
          ·
            refine ⟨1595263947440337602620913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063509298293558401747275 1595263947440337602620913)
            ·
              refine ⟨1196447960580253201965685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1595263947440337602620913 1196447960580253201965685)
              ·
                refine ⟨112166996304398737684283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1196447960580253201965685 112166996304398737684283)
                ·
                  rfl

theorem cell20_737250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_737250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737250 prefixEnd_737250 := by exact prefixLift 737250
  have htrace : WordTrace (prefixWord ++ tailWord_737250) baseStart_737250 baseEnd_737250 := by
    simpa [prefixWord, tailWord_737250, baseEnd_737250] using wordTrace_append hprefix tailTrace_737250
  have hstable : (prefixWord ++ tailWord_737250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737250).length < 2 ^ (prefixWord ++ tailWord_737250).sum := by decide
  have hdescent : baseEnd_737250 < baseStart_737250 := by decide
  rcases family_descends (prefixWord ++ tailWord_737250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737275 : List Nat := [1, 1, 1, 1, 1, 3, 6, 6]
def baseStart_737275 : Nat := 118140960795 + 737275 * 2 ^ 59
def prefixEnd_737275 : Nat := 4983230072969 + 3 ^ 40 * 737275 * 2
def baseEnd_737275 : Nat := 112170799864802412406471

theorem tailTrace_737275 : CollatzResearch.WordTrace tailWord_737275 prefixEnd_737275 112170799864802412406471 := by
  unfold tailWord_737275
  simp only [CollatzResearch.WordTrace]
  refine ⟨26890628403986066390381279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17927085602657377593587519 26890628403986066390381279)
  ·
    refine ⟨40335942605979099585571919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26890628403986066390381279 40335942605979099585571919)
    ·
      refine ⟨60503913908968649378357879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40335942605979099585571919 60503913908968649378357879)
      ·
        refine ⟨90755870863452974067536819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60503913908968649378357879 90755870863452974067536819)
        ·
          refine ⟨136133806295179461101305229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90755870863452974067536819 136133806295179461101305229)
          ·
            refine ⟨51050177360692297912989461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136133806295179461101305229 51050177360692297912989461)
            ·
              refine ⟨2392977063782451464671381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51050177360692297912989461 2392977063782451464671381)
              ·
                refine ⟨112170799864802412406471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2392977063782451464671381 112170799864802412406471)
                ·
                  rfl

theorem cell20_737275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_737275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737275 prefixEnd_737275 := by exact prefixLift 737275
  have htrace : WordTrace (prefixWord ++ tailWord_737275) baseStart_737275 baseEnd_737275 := by
    simpa [prefixWord, tailWord_737275, baseEnd_737275] using wordTrace_append hprefix tailTrace_737275
  have hstable : (prefixWord ++ tailWord_737275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737275).length < 2 ^ (prefixWord ++ tailWord_737275).sum := by decide
  have hdescent : baseEnd_737275 < baseStart_737275 := by decide
  rcases family_descends (prefixWord ++ tailWord_737275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737299 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 3]
def baseStart_737299 : Nat := 118140960795 + 737299 * 2 ^ 59
def prefixEnd_737299 : Nat := 4983230072969 + 3 ^ 40 * 737299 * 2
def baseEnd_737299 : Nat := 336523353848369820419315

theorem tailTrace_737299 : CollatzResearch.WordTrace tailWord_737299 prefixEnd_737299 336523353848369820419315 := by
  unfold tailWord_737299
  simp only [CollatzResearch.WordTrace]
  refine ⟨26891503755899118489254951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17927669170599412326169967 26891503755899118489254951)
  ·
    refine ⟨40337255633848677733882427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26891503755899118489254951 40337255633848677733882427)
    ·
      refine ⟨60505883450773016600823641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40337255633848677733882427 60505883450773016600823641)
      ·
        refine ⟨45379412588079762450617731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60505883450773016600823641 45379412588079762450617731)
        ·
          refine ⟨68069118882119643675926597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45379412588079762450617731 68069118882119643675926597)
          ·
            refine ⟨12762959790397433189236237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68069118882119643675926597 12762959790397433189236237)
            ·
              refine ⟨4786109921399037445963589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12762959790397433189236237 4786109921399037445963589)
              ·
                refine ⟨897395610262319521118173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4786109921399037445963589 897395610262319521118173)
                ·
                  refine ⟨336523353848369820419315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897395610262319521118173 336523353848369820419315)
                  ·
                    rfl

theorem cell20_737299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_737299 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737299 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737299 prefixEnd_737299 := by exact prefixLift 737299
  have htrace : WordTrace (prefixWord ++ tailWord_737299) baseStart_737299 baseEnd_737299 := by
    simpa [prefixWord, tailWord_737299, baseEnd_737299] using wordTrace_append hprefix tailTrace_737299
  have hstable : (prefixWord ++ tailWord_737299).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737299).length < 2 ^ (prefixWord ++ tailWord_737299).sum := by decide
  have hdescent : baseEnd_737299 < baseStart_737299 := by decide
  rcases family_descends (prefixWord ++ tailWord_737299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737309 : List Nat := [1, 4, 2, 2, 2, 3, 1, 5]
def baseStart_737309 : Nat := 118140960795 + 737309 * 2 ^ 59
def prefixEnd_737309 : Nat := 4983230072969 + 3 ^ 40 * 737309 * 2
def baseEnd_737309 : Nat := 112175972706951410028647

theorem tailTrace_737309 : CollatzResearch.WordTrace tailWord_737309 prefixEnd_737309 112175972706951410028647 := by
  unfold tailWord_737309
  simp only [CollatzResearch.WordTrace]
  refine ⟨26891868485862890197118981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17927912323908593464745987 26891868485862890197118981)
  ·
    refine ⟨5042225341099291911959809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26891868485862890197118981 5042225341099291911959809)
    ·
      refine ⟨3781669005824468933969857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5042225341099291911959809 3781669005824468933969857)
      ·
        refine ⟨2836251754368351700477393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3781669005824468933969857 2836251754368351700477393)
        ·
          refine ⟨2127188815776263775358045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2836251754368351700477393 2127188815776263775358045)
          ·
            refine ⟨797695805916098915759267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2127188815776263775358045 797695805916098915759267)
            ·
              refine ⟨1196543708874148373638901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797695805916098915759267 1196543708874148373638901)
              ·
                refine ⟨112175972706951410028647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1196543708874148373638901 112175972706951410028647)
                ·
                  rfl

theorem cell20_737309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_737309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737309 prefixEnd_737309 := by exact prefixLift 737309
  have htrace : WordTrace (prefixWord ++ tailWord_737309) baseStart_737309 baseEnd_737309 := by
    simpa [prefixWord, tailWord_737309, baseEnd_737309] using wordTrace_append hprefix tailTrace_737309
  have hstable : (prefixWord ++ tailWord_737309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737309).length < 2 ^ (prefixWord ++ tailWord_737309).sum := by decide
  have hdescent : baseEnd_737309 < baseStart_737309 := by decide
  rcases family_descends (prefixWord ++ tailWord_737309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737340 : List Nat := [2, 2, 2, 2, 2, 1, 4, 3, 2]
def baseStart_737340 : Nat := 118140960795 + 737340 * 2 ^ 59
def prefixEnd_737340 : Nat := 4983230072969 + 3 ^ 40 * 737340 * 2
def baseEnd_737340 : Nat := 336542067365555900052481

theorem tailTrace_737340 : CollatzResearch.WordTrace tailWord_737340 prefixEnd_737340 336542067365555900052481 := by
  unfold tailWord_737340
  simp only [CollatzResearch.WordTrace]
  refine ⟨13446499574375291245748737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17928666099167054994331649 13446499574375291245748737)
  ·
    refine ⟨10084874680781468434311553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13446499574375291245748737 10084874680781468434311553)
    ·
      refine ⟨7563656010586101325733665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10084874680781468434311553 7563656010586101325733665)
      ·
        refine ⟨5672742007939575994300249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7563656010586101325733665 5672742007939575994300249)
        ·
          refine ⟨4254556505954681995725187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5672742007939575994300249 4254556505954681995725187)
          ·
            refine ⟨6381834758932022993587781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254556505954681995725187 6381834758932022993587781)
            ·
              refine ⟨1196594017299754311297709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6381834758932022993587781 1196594017299754311297709)
              ·
                refine ⟨448722756487407866736641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196594017299754311297709 448722756487407866736641)
                ·
                  refine ⟨336542067365555900052481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448722756487407866736641 336542067365555900052481)
                  ·
                    rfl

theorem cell20_737340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3, 2].length) (baseStart_737340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737340 prefixEnd_737340 := by exact prefixLift 737340
  have htrace : WordTrace (prefixWord ++ tailWord_737340) baseStart_737340 baseEnd_737340 := by
    simpa [prefixWord, tailWord_737340, baseEnd_737340] using wordTrace_append hprefix tailTrace_737340
  have hstable : (prefixWord ++ tailWord_737340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737340).length < 2 ^ (prefixWord ++ tailWord_737340).sum := by decide
  have hdescent : baseEnd_737340 < baseStart_737340 := by decide
  rcases family_descends (prefixWord ++ tailWord_737340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737351 : List Nat := [1, 1, 4, 1, 3, 1, 9]
def baseStart_737351 : Nat := 118140960795 + 737351 * 2 ^ 59
def prefixEnd_737351 : Nat := 4983230072969 + 3 ^ 40 * 737351 * 2
def baseEnd_737351 : Nat := 37394120896143194520641

theorem tailTrace_737351 : CollatzResearch.WordTrace tailWord_737351 prefixEnd_737351 37394120896143194520641 := by
  unfold tailWord_737351
  simp only [CollatzResearch.WordTrace]
  refine ⟨26893400351710731370147907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17928933567807154246765271 26893400351710731370147907)
  ·
    refine ⟨40340100527566097055221861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26893400351710731370147907 40340100527566097055221861)
    ·
      refine ⟨7563768848918643197854099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40340100527566097055221861 7563768848918643197854099)
      ·
        refine ⟨11345653273377964796781149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7563768848918643197854099 11345653273377964796781149)
        ·
          refine ⟨4254619977516736798792931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11345653273377964796781149 4254619977516736798792931)
          ·
            refine ⟨6381929966275105198189397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4254619977516736798792931 6381929966275105198189397)
            ·
              refine ⟨37394120896143194520641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6381929966275105198189397 37394120896143194520641)
              ·
                rfl

theorem cell20_737351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_737351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737351 prefixEnd_737351 := by exact prefixLift 737351
  have htrace : WordTrace (prefixWord ++ tailWord_737351) baseStart_737351 baseEnd_737351 := by
    simpa [prefixWord, tailWord_737351, baseEnd_737351] using wordTrace_append hprefix tailTrace_737351
  have hstable : (prefixWord ++ tailWord_737351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737351).length < 2 ^ (prefixWord ++ tailWord_737351).sum := by decide
  have hdescent : baseEnd_737351 < baseStart_737351 := by decide
  rcases family_descends (prefixWord ++ tailWord_737351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737413 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 5]
def baseStart_737413 : Nat := 118140960795 + 737413 * 2 ^ 59
def prefixEnd_737413 : Nat := 4983230072969 + 3 ^ 40 * 737413 * 2
def baseEnd_737413 : Nat := 336575386554692090618849

theorem tailTrace_737413 : CollatzResearch.WordTrace tailWord_737413 prefixEnd_737413 336575386554692090618849 := by
  unfold tailWord_737413
  simp only [CollatzResearch.WordTrace]
  refine ⟨26895661677486115958904893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17930441118324077305936595 26895661677486115958904893)
  ·
    refine ⟨10085873129057293484589335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26895661677486115958904893 10085873129057293484589335)
    ·
      refine ⟨15128809693585940226884003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10085873129057293484589335 15128809693585940226884003)
      ·
        refine ⟨22693214540378910340326005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15128809693585940226884003 22693214540378910340326005)
        ·
          refine ⟨2127488863160522844405563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22693214540378910340326005 2127488863160522844405563)
          ·
            refine ⟨3191233294740784266608345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127488863160522844405563 3191233294740784266608345)
            ·
              refine ⟨2393424971055588199956259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3191233294740784266608345 2393424971055588199956259)
              ·
                refine ⟨3590137456583382299934389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2393424971055588199956259 3590137456583382299934389)
                ·
                  refine ⟨336575386554692090618849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3590137456583382299934389 336575386554692090618849)
                  ·
                    rfl

theorem cell20_737413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_737413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737413 prefixEnd_737413 := by exact prefixLift 737413
  have htrace : WordTrace (prefixWord ++ tailWord_737413) baseStart_737413 baseEnd_737413 := by
    simpa [prefixWord, tailWord_737413, baseEnd_737413] using wordTrace_append hprefix tailTrace_737413
  have hstable : (prefixWord ++ tailWord_737413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737413).length < 2 ^ (prefixWord ++ tailWord_737413).sum := by decide
  have hdescent : baseEnd_737413 < baseStart_737413 := by decide
  rcases family_descends (prefixWord ++ tailWord_737413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737416 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_737416 : Nat := 118140960795 + 737416 * 2 ^ 59
def prefixEnd_737416 : Nat := 4983230072969 + 3 ^ 40 * 737416 * 2
def baseEnd_737416 : Nat := 336576755836437413518837

theorem tailTrace_737416 : CollatzResearch.WordTrace tailWord_737416 prefixEnd_737416 336576755836437413518837 := by
  unfold tailWord_737416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13447885548237623735632051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17930514064316831647509401 13447885548237623735632051)
  ·
    refine ⟨20171828322356435603448077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13447885548237623735632051 20171828322356435603448077)
    ·
      refine ⟨7564435620883663351293029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20171828322356435603448077 7564435620883663351293029)
      ·
        refine ⟨1418331678915686878367443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7564435620883663351293029 1418331678915686878367443)
        ·
          refine ⟨2127497518373530317551165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418331678915686878367443 2127497518373530317551165)
          ·
            refine ⟨797811569390073869081687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2127497518373530317551165 797811569390073869081687)
            ·
              refine ⟨1196717354085110803622531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 797811569390073869081687 1196717354085110803622531)
              ·
                refine ⟨1795076031127666205433797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1196717354085110803622531 1795076031127666205433797)
                ·
                  refine ⟨336576755836437413518837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795076031127666205433797 336576755836437413518837)
                  ·
                    rfl

theorem cell20_737416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_737416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737416 prefixEnd_737416 := by exact prefixLift 737416
  have htrace : WordTrace (prefixWord ++ tailWord_737416) baseStart_737416 baseEnd_737416 := by
    simpa [prefixWord, tailWord_737416, baseEnd_737416] using wordTrace_append hprefix tailTrace_737416
  have hstable : (prefixWord ++ tailWord_737416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737416).length < 2 ^ (prefixWord ++ tailWord_737416).sum := by decide
  have hdescent : baseEnd_737416 < baseStart_737416 := by decide
  rcases family_descends (prefixWord ++ tailWord_737416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737461 : List Nat := [1, 3, 3, 4, 2, 7]
def baseStart_737461 : Nat := 118140960795 + 737461 * 2 ^ 59
def prefixEnd_737461 : Nat := 4983230072969 + 3 ^ 40 * 737461 * 2
def baseEnd_737461 : Nat := 12466566483800639148839

theorem tailTrace_737461 : CollatzResearch.WordTrace tailWord_737461 prefixEnd_737461 12466566483800639148839 := by
  unfold tailWord_737461
  simp only [CollatzResearch.WordTrace]
  refine ⟨26897412381312220156652237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17931608254208146771101491 26897412381312220156652237)
  ·
    refine ⟨10086529642992082558744589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26897412381312220156652237 10086529642992082558744589)
    ·
      refine ⟨3782448616122030959529221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10086529642992082558744589 3782448616122030959529221)
      ·
        refine ⟨709209115522880804911729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3782448616122030959529221 709209115522880804911729)
        ·
          refine ⟨531906836642160603683797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 709209115522880804911729 531906836642160603683797)
          ·
            refine ⟨12466566483800639148839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 531906836642160603683797 12466566483800639148839)
            ·
              rfl

theorem cell20_737461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 7].length) (baseStart_737461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737461 prefixEnd_737461 := by exact prefixLift 737461
  have htrace : WordTrace (prefixWord ++ tailWord_737461) baseStart_737461 baseEnd_737461 := by
    simpa [prefixWord, tailWord_737461, baseEnd_737461] using wordTrace_append hprefix tailTrace_737461
  have hstable : (prefixWord ++ tailWord_737461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737461).length < 2 ^ (prefixWord ++ tailWord_737461).sum := by decide
  have hdescent : baseEnd_737461 < baseStart_737461 := by decide
  rcases family_descends (prefixWord ++ tailWord_737461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737489 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 3]
def baseStart_737489 : Nat := 118140960795 + 737489 * 2 ^ 59
def prefixEnd_737489 : Nat := 4983230072969 + 3 ^ 40 * 737489 * 2
def baseEnd_737489 : Nat := 336610075025573604085205

theorem tailTrace_737489 : CollatzResearch.WordTrace tailWord_737489 prefixEnd_737489 336610075025573604085205 := by
  unfold tailWord_737489
  simp only [CollatzResearch.WordTrace]
  refine ⟨26898433625210780938671521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17932289083473853959114347 26898433625210780938671521)
  ·
    refine ⟨20173825218908085704003641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26898433625210780938671521 20173825218908085704003641)
    ·
      refine ⟨15130368914181064278002731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20173825218908085704003641 15130368914181064278002731)
      ·
        refine ⟨22695553371271596417004097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15130368914181064278002731 22695553371271596417004097)
        ·
          refine ⟨17021665028453697312753073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22695553371271596417004097 17021665028453697312753073)
          ·
            refine ⟨12766248771340272984564805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17021665028453697312753073 12766248771340272984564805)
            ·
              refine ⟨2393671644626301184605901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12766248771340272984564805 2393671644626301184605901)
              ·
                refine ⟨897626866734862944227213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2393671644626301184605901 897626866734862944227213)
                ·
                  refine ⟨336610075025573604085205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897626866734862944227213 336610075025573604085205)
                  ·
                    rfl

theorem cell20_737489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_737489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737489 prefixEnd_737489 := by exact prefixLift 737489
  have htrace : WordTrace (prefixWord ++ tailWord_737489) baseStart_737489 baseEnd_737489 := by
    simpa [prefixWord, tailWord_737489, baseEnd_737489] using wordTrace_append hprefix tailTrace_737489
  have hstable : (prefixWord ++ tailWord_737489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737489).length < 2 ^ (prefixWord ++ tailWord_737489).sum := by decide
  have hdescent : baseEnd_737489 < baseStart_737489 := by decide
  rcases family_descends (prefixWord ++ tailWord_737489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737496 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 6]
def baseStart_737496 : Nat := 118140960795 + 737496 * 2 ^ 59
def prefixEnd_737496 : Nat := 4983230072969 + 3 ^ 40 * 737496 * 2
def baseEnd_737496 : Nat := 336613270016312690851843

theorem tailTrace_737496 : CollatzResearch.WordTrace tailWord_737496 prefixEnd_737496 336613270016312690851843 := by
  unfold tailWord_737496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13449344468092710567088171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17932459290790280756117561 13449344468092710567088171)
  ·
    refine ⟨20174016702139065850632257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13449344468092710567088171 20174016702139065850632257)
    ·
      refine ⟨15130512526604299387974193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20174016702139065850632257 15130512526604299387974193)
      ·
        refine ⟨11347884394953224540980645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15130512526604299387974193 11347884394953224540980645)
        ·
          refine ⟨2127728324053729601433871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11347884394953224540980645 2127728324053729601433871)
          ·
            refine ⟨3191592486080594402150807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127728324053729601433871 3191592486080594402150807)
            ·
              refine ⟨4787388729120891603226211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3191592486080594402150807 4787388729120891603226211)
              ·
                refine ⟨7181083093681337404839317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4787388729120891603226211 7181083093681337404839317)
                ·
                  refine ⟨336613270016312690851843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7181083093681337404839317 336613270016312690851843)
                  ·
                    rfl

theorem cell20_737496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_737496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737496 prefixEnd_737496 := by exact prefixLift 737496
  have htrace : WordTrace (prefixWord ++ tailWord_737496) baseStart_737496 baseEnd_737496 := by
    simpa [prefixWord, tailWord_737496, baseEnd_737496] using wordTrace_append hprefix tailTrace_737496
  have hstable : (prefixWord ++ tailWord_737496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737496).length < 2 ^ (prefixWord ++ tailWord_737496).sum := by decide
  have hdescent : baseEnd_737496 < baseStart_737496 := by decide
  rcases family_descends (prefixWord ++ tailWord_737496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737568 : List Nat := [2, 1, 1, 5, 2, 1, 3, 3, 2]
def baseStart_737568 : Nat := 118140960795 + 737568 * 2 ^ 59
def prefixEnd_737568 : Nat := 4983230072969 + 3 ^ 40 * 737568 * 2
def baseEnd_737568 : Nat := 336646132778200440451549

theorem tailTrace_737568 : CollatzResearch.WordTrace tailWord_737568 prefixEnd_737568 336646132778200440451549 := by
  unfold tailWord_737568
  simp only [CollatzResearch.WordTrace]
  refine ⟨13450657495962288715398679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17934209994616384953864905 13450657495962288715398679)
  ·
    refine ⟨20175986243943433073098019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13450657495962288715398679 20175986243943433073098019)
    ·
      refine ⟨30263979365915149609647029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20175986243943433073098019 30263979365915149609647029)
      ·
        refine ⟨2837248065554545275904409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30263979365915149609647029 2837248065554545275904409)
        ·
          refine ⟨2127936049165908956928307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2837248065554545275904409 2127936049165908956928307)
          ·
            refine ⟨3191904073748863435392461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2127936049165908956928307 3191904073748863435392461)
            ·
              refine ⟨1196964027655823788272173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3191904073748863435392461 1196964027655823788272173)
              ·
                refine ⟨448861510370933920602065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1196964027655823788272173 448861510370933920602065)
                ·
                  refine ⟨336646132778200440451549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448861510370933920602065 336646132778200440451549)
                  ·
                    rfl

theorem cell20_737568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_737568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737568 prefixEnd_737568 := by exact prefixLift 737568
  have htrace : WordTrace (prefixWord ++ tailWord_737568) baseStart_737568 baseEnd_737568 := by
    simpa [prefixWord, tailWord_737568, baseEnd_737568] using wordTrace_append hprefix tailTrace_737568
  have hstable : (prefixWord ++ tailWord_737568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737568).length < 2 ^ (prefixWord ++ tailWord_737568).sum := by decide
  have hdescent : baseEnd_737568 < baseStart_737568 := by decide
  rcases family_descends (prefixWord ++ tailWord_737568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737585 : List Nat := [1, 2, 2, 3, 4, 1, 3, 2, 2]
def baseStart_737585 : Nat := 118140960795 + 737585 * 2 ^ 59
def prefixEnd_737585 : Nat := 4983230072969 + 3 ^ 40 * 737585 * 2
def baseEnd_737585 : Nat := 336653892041423936884813

theorem tailTrace_737585 : CollatzResearch.WordTrace tailWord_737585 prefixEnd_737585 336653892041423936884813 := by
  unfold tailWord_737585
  simp only [CollatzResearch.WordTrace]
  refine ⟨26901935032862989334166209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17934623355241992889444139 26901935032862989334166209)
  ·
    refine ⟨20176451274647242000624657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26901935032862989334166209 20176451274647242000624657)
    ·
      refine ⟨15132338455985431500468493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20176451274647242000624657 15132338455985431500468493)
      ·
        refine ⟨5674626920994536812675685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15132338455985431500468493 5674626920994536812675685)
        ·
          refine ⟨1063992547686475652376691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5674626920994536812675685 1063992547686475652376691)
          ·
            refine ⟨1595988821529713478565037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1063992547686475652376691 1595988821529713478565037)
            ·
              refine ⟨598495808073642554461889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1595988821529713478565037 598495808073642554461889)
              ·
                refine ⟨448871856055231915846417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 598495808073642554461889 448871856055231915846417)
                ·
                  refine ⟨336653892041423936884813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448871856055231915846417 336653892041423936884813)
                  ·
                    rfl

theorem cell20_737585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_737585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737585 prefixEnd_737585 := by exact prefixLift 737585
  have htrace : WordTrace (prefixWord ++ tailWord_737585) baseStart_737585 baseEnd_737585 := by
    simpa [prefixWord, tailWord_737585, baseEnd_737585] using wordTrace_append hprefix tailTrace_737585
  have hstable : (prefixWord ++ tailWord_737585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737585).length < 2 ^ (prefixWord ++ tailWord_737585).sum := by decide
  have hdescent : baseEnd_737585 < baseStart_737585 := by decide
  rcases family_descends (prefixWord ++ tailWord_737585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737617 : List Nat := [1, 2, 2, 1, 4, 2, 2, 6]
def baseStart_737617 : Nat := 118140960795 + 737617 * 2 ^ 59
def prefixEnd_737617 : Nat := 4983230072969 + 3 ^ 40 * 737617 * 2
def baseEnd_737617 : Nat := 112222832571124682606005

theorem tailTrace_737617 : CollatzResearch.WordTrace tailWord_737617 prefixEnd_737617 112222832571124682606005 := by
  unfold tailWord_737617
  simp only [CollatzResearch.WordTrace]
  refine ⟨26903102168747058799331105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17935401445831372532887403 26903102168747058799331105)
  ·
    refine ⟨20177326626560294099498329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26903102168747058799331105 20177326626560294099498329)
    ·
      refine ⟨15132994969920220574623747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20177326626560294099498329 15132994969920220574623747)
      ·
        refine ⟨22699492454880330861935621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15132994969920220574623747 22699492454880330861935621)
        ·
          refine ⟨4256154835290062036612929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22699492454880330861935621 4256154835290062036612929)
          ·
            refine ⟨3192116126467546527459697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4256154835290062036612929 3192116126467546527459697)
            ·
              refine ⟨2394087094850659895594773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3192116126467546527459697 2394087094850659895594773)
              ·
                refine ⟨112222832571124682606005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2394087094850659895594773 112222832571124682606005)
                ·
                  rfl

theorem cell20_737617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_737617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737617 prefixEnd_737617 := by exact prefixLift 737617
  have htrace : WordTrace (prefixWord ++ tailWord_737617) baseStart_737617 baseEnd_737617 := by
    simpa [prefixWord, tailWord_737617, baseEnd_737617] using wordTrace_append hprefix tailTrace_737617
  have hstable : (prefixWord ++ tailWord_737617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737617).length < 2 ^ (prefixWord ++ tailWord_737617).sum := by decide
  have hdescent : baseEnd_737617 < baseStart_737617 := by decide
  rcases family_descends (prefixWord ++ tailWord_737617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737624 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_737624 : Nat := 118140960795 + 737624 * 2 ^ 59
def prefixEnd_737624 : Nat := 4983230072969 + 3 ^ 40 * 737624 * 2
def baseEnd_737624 : Nat := 336671692704113134584653

theorem tailTrace_737624 : CollatzResearch.WordTrace tailWord_737624 prefixEnd_737624 336671692704113134584653 := by
  unfold tailWord_737624
  simp only [CollatzResearch.WordTrace]
  refine ⟨13451678739860849497417963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17935571653147799329890617 13451678739860849497417963)
  ·
    refine ⟨20177518109791274246126945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13451678739860849497417963 20177518109791274246126945)
    ·
      refine ⟨15133138582343455684595209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20177518109791274246126945 15133138582343455684595209)
      ·
        refine ⟨11349853936757591763446407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15133138582343455684595209 11349853936757591763446407)
        ·
          refine ⟨17024780905136387645169611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11349853936757591763446407 17024780905136387645169611)
          ·
            refine ⟨25537171357704581467754417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17024780905136387645169611 25537171357704581467754417)
            ·
              refine ⟨19152878518278436100815813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25537171357704581467754417 19152878518278436100815813)
              ·
                refine ⟨3591164722177206768902965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19152878518278436100815813 3591164722177206768902965)
                ·
                  refine ⟨336671692704113134584653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3591164722177206768902965 336671692704113134584653)
                  ·
                    rfl

theorem cell20_737624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_737624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737624 prefixEnd_737624 := by exact prefixLift 737624
  have htrace : WordTrace (prefixWord ++ tailWord_737624) baseStart_737624 baseEnd_737624 := by
    simpa [prefixWord, tailWord_737624, baseEnd_737624] using wordTrace_append hprefix tailTrace_737624
  have hstable : (prefixWord ++ tailWord_737624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737624).length < 2 ^ (prefixWord ++ tailWord_737624).sum := by decide
  have hdescent : baseEnd_737624 < baseStart_737624 := by decide
  rcases family_descends (prefixWord ++ tailWord_737624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737630 : List Nat := [4, 4, 2, 1, 9]
def baseStart_737630 : Nat := 118140960795 + 737630 * 2 ^ 59
def prefixEnd_737630 : Nat := 4983230072969 + 3 ^ 40 * 737630 * 2
def baseEnd_737630 : Nat := 4156474460093873831909

theorem tailTrace_737630 : CollatzResearch.WordTrace tailWord_737630 prefixEnd_737630 4156474460093873831909 := by
  unfold tailWord_737630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362947039712495252444293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17935717545133308013036229 3362947039712495252444293)
  ·
    refine ⟨630552569946092859833305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3362947039712495252444293 630552569946092859833305)
    ·
      refine ⟨472914427459569644874979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 630552569946092859833305 472914427459569644874979)
      ·
        refine ⟨709371641189354467312469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 472914427459569644874979 709371641189354467312469)
        ·
          refine ⟨4156474460093873831909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 709371641189354467312469 4156474460093873831909)
          ·
            rfl

theorem cell20_737630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 9].length) (baseStart_737630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737630 prefixEnd_737630 := by exact prefixLift 737630
  have htrace : WordTrace (prefixWord ++ tailWord_737630) baseStart_737630 baseEnd_737630 := by
    simpa [prefixWord, tailWord_737630, baseEnd_737630] using wordTrace_append hprefix tailTrace_737630
  have hstable : (prefixWord ++ tailWord_737630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737630).length < 2 ^ (prefixWord ++ tailWord_737630).sum := by decide
  have hdescent : baseEnd_737630 < baseStart_737630 := by decide
  rcases family_descends (prefixWord ++ tailWord_737630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737641 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 3]
def baseStart_737641 : Nat := 118140960795 + 737641 * 2 ^ 59
def prefixEnd_737641 : Nat := 4983230072969 + 3 ^ 40 * 737641 * 2
def baseEnd_737641 : Nat := 336679451967336631017917

theorem tailTrace_737641 : CollatzResearch.WordTrace tailWord_737641 prefixEnd_737641 336679451967336631017917 := by
  unfold tailWord_737641
  simp only [CollatzResearch.WordTrace]
  refine ⟨26903977520660110898204777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17935985013773407265469851 26903977520660110898204777)
  ·
    refine ⟨20177983140495083173653583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26903977520660110898204777 20177983140495083173653583)
    ·
      refine ⟨30266974710742624760480375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20177983140495083173653583 30266974710742624760480375)
      ·
        refine ⟨45400462066113937140720563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30266974710742624760480375 45400462066113937140720563)
        ·
          refine ⟨68100693099170905711080845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45400462066113937140720563 68100693099170905711080845)
          ·
            refine ⟨25537759912189089641655317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68100693099170905711080845 25537759912189089641655317)
            ·
              refine ⟨1197082495883863576952593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25537759912189089641655317 1197082495883863576952593)
              ·
                refine ⟨897811871912897682714445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197082495883863576952593 897811871912897682714445)
                ·
                  refine ⟨336679451967336631017917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897811871912897682714445 336679451967336631017917)
                  ·
                    rfl

theorem cell20_737641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_737641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737641 prefixEnd_737641 := by exact prefixLift 737641
  have htrace : WordTrace (prefixWord ++ tailWord_737641) baseStart_737641 baseEnd_737641 := by
    simpa [prefixWord, tailWord_737641, baseEnd_737641] using wordTrace_append hprefix tailTrace_737641
  have hstable : (prefixWord ++ tailWord_737641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737641).length < 2 ^ (prefixWord ++ tailWord_737641).sum := by decide
  have hdescent : baseEnd_737641 < baseStart_737641 := by decide
  rcases family_descends (prefixWord ++ tailWord_737641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737644 : List Nat := [2, 2, 1, 1, 6, 1, 1, 4, 2]
def baseStart_737644 : Nat := 118140960795 + 737644 * 2 ^ 59
def prefixEnd_737644 : Nat := 4983230072969 + 3 ^ 40 * 737644 * 2
def baseEnd_737644 : Nat := 336680821249081953917905

theorem tailTrace_737644 : CollatzResearch.WordTrace tailWord_737644 prefixEnd_737644 336680821249081953917905 := by
  unfold tailWord_737644
  simp only [CollatzResearch.WordTrace]
  refine ⟨13452043469824621205281993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17936057959766161607042657 13452043469824621205281993)
  ·
    refine ⟨10089032602368465903961495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13452043469824621205281993 10089032602368465903961495)
    ·
      refine ⟨15133548903552698855942243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10089032602368465903961495 15133548903552698855942243)
      ·
        refine ⟨22700323355329048283913365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15133548903552698855942243 22700323355329048283913365)
        ·
          refine ⟨1064077657281049138308439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22700323355329048283913365 1064077657281049138308439)
          ·
            refine ⟨1596116485921573707462659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064077657281049138308439 1596116485921573707462659)
            ·
              refine ⟨2394174728882360561193989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596116485921573707462659 2394174728882360561193989)
              ·
                refine ⟨448907761665442605223873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2394174728882360561193989 448907761665442605223873)
                ·
                  refine ⟨336680821249081953917905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 448907761665442605223873 336680821249081953917905)
                  ·
                    rfl

theorem cell20_737644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_737644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737644 prefixEnd_737644 := by exact prefixLift 737644
  have htrace : WordTrace (prefixWord ++ tailWord_737644) baseStart_737644 baseEnd_737644 := by
    simpa [prefixWord, tailWord_737644, baseEnd_737644] using wordTrace_append hprefix tailTrace_737644
  have hstable : (prefixWord ++ tailWord_737644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737644).length < 2 ^ (prefixWord ++ tailWord_737644).sum := by decide
  have hdescent : baseEnd_737644 < baseStart_737644 := by decide
  rcases family_descends (prefixWord ++ tailWord_737644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737665 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 4]
def baseStart_737665 : Nat := 118140960795 + 737665 * 2 ^ 59
def prefixEnd_737665 : Nat := 4983230072969 + 3 ^ 40 * 737665 * 2
def baseEnd_737665 : Nat := 336690406221299214217819

theorem tailTrace_737665 : CollatzResearch.WordTrace tailWord_737665 prefixEnd_737665 336690406221299214217819 := by
  unfold tailWord_737665
  simp only [CollatzResearch.WordTrace]
  refine ⟨26904852872573162997078449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17936568581715441998052299 26904852872573162997078449)
  ·
    refine ⟨20178639654429872247808837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26904852872573162997078449 20178639654429872247808837)
    ·
      refine ⟨3783494935205601046464157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20178639654429872247808837 3783494935205601046464157)
      ·
        refine ⟨1418810600702100392424059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3783494935205601046464157 1418810600702100392424059)
        ·
          refine ⟨2128215901053150588636089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1418810600702100392424059 2128215901053150588636089)
          ·
            refine ⟨1596161925789862941477067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2128215901053150588636089 1596161925789862941477067)
            ·
              refine ⟨2394242888684794412215601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1596161925789862941477067 2394242888684794412215601)
              ·
                refine ⟨1795682166513595809161701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2394242888684794412215601 1795682166513595809161701)
                ·
                  refine ⟨336690406221299214217819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795682166513595809161701 336690406221299214217819)
                  ·
                    rfl

theorem cell20_737665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_737665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737665 prefixEnd_737665 := by exact prefixLift 737665
  have htrace : WordTrace (prefixWord ++ tailWord_737665) baseStart_737665 baseEnd_737665 := by
    simpa [prefixWord, tailWord_737665, baseEnd_737665] using wordTrace_append hprefix tailTrace_737665
  have hstable : (prefixWord ++ tailWord_737665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737665).length < 2 ^ (prefixWord ++ tailWord_737665).sum := by decide
  have hdescent : baseEnd_737665 < baseStart_737665 := by decide
  rcases family_descends (prefixWord ++ tailWord_737665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737672 : List Nat := [2, 1, 3, 3, 1, 1, 5, 4]
def baseStart_737672 : Nat := 118140960795 + 737672 * 2 ^ 59
def prefixEnd_737672 : Nat := 4983230072969 + 3 ^ 40 * 737672 * 2
def baseEnd_737672 : Nat := 112231200404012766994819

theorem tailTrace_737672 : CollatzResearch.WordTrace tailWord_737672 prefixEnd_737672 112231200404012766994819 := by
  unfold tailWord_737672
  simp only [CollatzResearch.WordTrace]
  refine ⟨13452554091773901596291635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17936738789031868795055513 13452554091773901596291635)
  ·
    refine ⟨20178831137660852394437453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13452554091773901596291635 20178831137660852394437453)
    ·
      refine ⟨7567061676622819647914045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20178831137660852394437453 7567061676622819647914045)
      ·
        refine ⟨2837648128733557367967767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7567061676622819647914045 2837648128733557367967767)
        ·
          refine ⟨4256472193100336051951651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837648128733557367967767 4256472193100336051951651)
          ·
            refine ⟨6384708289650504077927477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4256472193100336051951651 6384708289650504077927477)
            ·
              refine ⟨598566402154734757305701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6384708289650504077927477 598566402154734757305701)
              ·
                refine ⟨112231200404012766994819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598566402154734757305701 112231200404012766994819)
                ·
                  rfl

theorem cell20_737672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_737672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737672 prefixEnd_737672 := by exact prefixLift 737672
  have htrace : WordTrace (prefixWord ++ tailWord_737672) baseStart_737672 baseEnd_737672 := by
    simpa [prefixWord, tailWord_737672, baseEnd_737672] using wordTrace_append hprefix tailTrace_737672
  have hstable : (prefixWord ++ tailWord_737672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737672).length < 2 ^ (prefixWord ++ tailWord_737672).sum := by decide
  have hdescent : baseEnd_737672 < baseStart_737672 := by decide
  rcases family_descends (prefixWord ++ tailWord_737672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737696 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_737696 : Nat := 118140960795 + 737696 * 2 ^ 59
def prefixEnd_737696 : Nat := 4983230072969 + 3 ^ 40 * 737696 * 2
def baseEnd_737696 : Nat := 336704555466000884184359

theorem tailTrace_737696 : CollatzResearch.WordTrace tailWord_737696 prefixEnd_737696 336704555466000884184359 := by
  unfold tailWord_737696
  simp only [CollatzResearch.WordTrace]
  refine ⟨13452991767730427645728471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17937322356973903527637961 13452991767730427645728471)
  ·
    refine ⟨20179487651595641468592707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13452991767730427645728471 20179487651595641468592707)
    ·
      refine ⟨30269231477393462202889061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20179487651595641468592707 30269231477393462202889061)
      ·
        refine ⟨5675480902011274163041699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30269231477393462202889061 5675480902011274163041699)
        ·
          refine ⟨8513221353016911244562549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5675480902011274163041699 8513221353016911244562549)
          ·
            refine ⟨798114501845335429177739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8513221353016911244562549 798114501845335429177739)
            ·
              refine ⟨1197171752768003143766609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798114501845335429177739 1197171752768003143766609)
              ·
                refine ⟨897878814576002357824957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197171752768003143766609 897878814576002357824957)
                ·
                  refine ⟨336704555466000884184359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 897878814576002357824957 336704555466000884184359)
                  ·
                    rfl

theorem cell20_737696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_737696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737696 prefixEnd_737696 := by exact prefixLift 737696
  have htrace : WordTrace (prefixWord ++ tailWord_737696) baseStart_737696 baseEnd_737696 := by
    simpa [prefixWord, tailWord_737696, baseEnd_737696] using wordTrace_append hprefix tailTrace_737696
  have hstable : (prefixWord ++ tailWord_737696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737696).length < 2 ^ (prefixWord ++ tailWord_737696).sum := by decide
  have hdescent : baseEnd_737696 < baseStart_737696 := by decide
  rcases family_descends (prefixWord ++ tailWord_737696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737703 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 4]
def baseStart_737703 : Nat := 118140960795 + 737703 * 2 ^ 59
def prefixEnd_737703 : Nat := 4983230072969 + 3 ^ 40 * 737703 * 2
def baseEnd_737703 : Nat := 336707750456739970950997

theorem tailTrace_737703 : CollatzResearch.WordTrace tailWord_737703 prefixEnd_737703 336707750456739970950997 := by
  unfold tailWord_737703
  simp only [CollatzResearch.WordTrace]
  refine ⟨26906238846435495486961763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17937492564290330324641175 26906238846435495486961763)
  ·
    refine ⟨40359358269653243230442645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26906238846435495486961763 40359358269653243230442645)
    ·
      refine ⟨1891844918889995776426999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40359358269653243230442645 1891844918889995776426999)
      ·
        refine ⟨2837767378334993664640499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1891844918889995776426999 2837767378334993664640499)
        ·
          refine ⟨4256651067502490496960749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2837767378334993664640499 4256651067502490496960749)
          ·
            refine ⟨1596244150313433936360281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4256651067502490496960749 1596244150313433936360281)
            ·
              refine ⟨1197183112735075452270211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596244150313433936360281 1197183112735075452270211)
              ·
                refine ⟨1795774669102613178405317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197183112735075452270211 1795774669102613178405317)
                ·
                  refine ⟨336707750456739970950997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1795774669102613178405317 336707750456739970950997)
                  ·
                    rfl

theorem cell20_737703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 4].length) (baseStart_737703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737703 prefixEnd_737703 := by exact prefixLift 737703
  have htrace : WordTrace (prefixWord ++ tailWord_737703) baseStart_737703 baseEnd_737703 := by
    simpa [prefixWord, tailWord_737703, baseEnd_737703] using wordTrace_append hprefix tailTrace_737703
  have hstable : (prefixWord ++ tailWord_737703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737703).length < 2 ^ (prefixWord ++ tailWord_737703).sum := by decide
  have hdescent : baseEnd_737703 < baseStart_737703 := by decide
  rcases family_descends (prefixWord ++ tailWord_737703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737738 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_737738 : Nat := 118140960795 + 737738 * 2 ^ 59
def prefixEnd_737738 : Nat := 4983230072969 + 3 ^ 40 * 737738 * 2
def baseEnd_737738 : Nat := 336723725410435404784187

theorem tailTrace_737738 : CollatzResearch.WordTrace tailWord_737738 prefixEnd_737738 336723725410435404784187 := by
  unfold tailWord_737738
  simp only [CollatzResearch.WordTrace]
  refine ⟨6726878850327174116121467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17938343600872464309657245 6726878850327174116121467)
  ·
    refine ⟨10090318275490761174182201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6726878850327174116121467 10090318275490761174182201)
    ·
      refine ⟨7567738706618070880636651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10090318275490761174182201 7567738706618070880636651)
      ·
        refine ⟨11351608059927106320954977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7567738706618070880636651 11351608059927106320954977)
        ·
          refine ⟨8513706044945329740716233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11351608059927106320954977 8513706044945329740716233)
          ·
            refine ⟨6385279533708997305537175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8513706044945329740716233 6385279533708997305537175)
            ·
              refine ⟨9577919300563495958305763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6385279533708997305537175 9577919300563495958305763)
              ·
                refine ⟨14366878950845243937458645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9577919300563495958305763 14366878950845243937458645)
                ·
                  refine ⟨336723725410435404784187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14366878950845243937458645 336723725410435404784187)
                  ·
                    rfl

theorem cell20_737738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_737738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737738 prefixEnd_737738 := by exact prefixLift 737738
  have htrace : WordTrace (prefixWord ++ tailWord_737738) baseStart_737738 baseEnd_737738 := by
    simpa [prefixWord, tailWord_737738, baseEnd_737738] using wordTrace_append hprefix tailTrace_737738
  have hstable : (prefixWord ++ tailWord_737738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737738).length < 2 ^ (prefixWord ++ tailWord_737738).sum := by decide
  have hdescent : baseEnd_737738 < baseStart_737738 := by decide
  rcases family_descends (prefixWord ++ tailWord_737738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737745 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 6]
def baseStart_737745 : Nat := 118140960795 + 737745 * 2 ^ 59
def prefixEnd_737745 : Nat := 4983230072969 + 3 ^ 40 * 737745 * 2
def baseEnd_737745 : Nat := 336726920401174491550825

theorem tailTrace_737745 : CollatzResearch.WordTrace tailWord_737745 prefixEnd_737745 336726920401174491550825 := by
  unfold tailWord_737745
  simp only [CollatzResearch.WordTrace]
  refine ⟨26907770712283336659990689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17938513808188891106660459 26907770712283336659990689)
  ·
    refine ⟨20180828034212502494993017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26907770712283336659990689 20180828034212502494993017)
    ·
      refine ⟨15135621025659376871244763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20180828034212502494993017 15135621025659376871244763)
      ·
        refine ⟨22703431538489065306867145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15135621025659376871244763 22703431538489065306867145)
        ·
          refine ⟨17027573653866798980150359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22703431538489065306867145 17027573653866798980150359)
          ·
            refine ⟨25541360480800198470225539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17027573653866798980150359 25541360480800198470225539)
            ·
              refine ⟨38312040721200297705338309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25541360480800198470225539 38312040721200297705338309)
              ·
                refine ⟨7183507635225055819750933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38312040721200297705338309 7183507635225055819750933)
                ·
                  refine ⟨336726920401174491550825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7183507635225055819750933 336726920401174491550825)
                  ·
                    rfl

theorem cell20_737745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_737745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737745 prefixEnd_737745 := by exact prefixLift 737745
  have htrace : WordTrace (prefixWord ++ tailWord_737745) baseStart_737745 baseEnd_737745 := by
    simpa [prefixWord, tailWord_737745, baseEnd_737745] using wordTrace_append hprefix tailTrace_737745
  have hstable : (prefixWord ++ tailWord_737745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737745).length < 2 ^ (prefixWord ++ tailWord_737745).sum := by decide
  have hdescent : baseEnd_737745 < baseStart_737745 := by decide
  rcases family_descends (prefixWord ++ tailWord_737745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737748 : List Nat := [2, 4, 1, 2, 2, 3, 6]
def baseStart_737748 : Nat := 118140960795 + 737748 * 2 ^ 59
def prefixEnd_737748 : Nat := 4983230072969 + 3 ^ 40 * 737748 * 2
def baseEnd_737748 : Nat := 37414254409213312716757

theorem tailTrace_737748 : CollatzResearch.WordTrace tailWord_737748 prefixEnd_737748 37414254409213312716757 := by
  unfold tailWord_737748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13453940065636234086174949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17938586754181645448233265 13453940065636234086174949)
  ·
    refine ⟨2522613762306793891157803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13453940065636234086174949 2522613762306793891157803)
    ·
      refine ⟨3783920643460190836736705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2522613762306793891157803 3783920643460190836736705)
      ·
        refine ⟨2837940482595143127552529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3783920643460190836736705 2837940482595143127552529)
        ·
          refine ⟨2128455361946357345664397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2837940482595143127552529 2128455361946357345664397)
          ·
            refine ⟨798170760729884004624149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2128455361946357345664397 798170760729884004624149)
            ·
              refine ⟨37414254409213312716757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 798170760729884004624149 37414254409213312716757)
              ·
                rfl

theorem cell20_737748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 6].length) (baseStart_737748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737748 prefixEnd_737748 := by exact prefixLift 737748
  have htrace : WordTrace (prefixWord ++ tailWord_737748) baseStart_737748 baseEnd_737748 := by
    simpa [prefixWord, tailWord_737748, baseEnd_737748] using wordTrace_append hprefix tailTrace_737748
  have hstable : (prefixWord ++ tailWord_737748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737748).length < 2 ^ (prefixWord ++ tailWord_737748).sum := by decide
  have hdescent : baseEnd_737748 < baseStart_737748 := by decide
  rcases family_descends (prefixWord ++ tailWord_737748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737837 : List Nat := [1, 5, 4, 1, 1, 1, 3, 4]
def baseStart_737837 : Nat := 118140960795 + 737837 * 2 ^ 59
def prefixEnd_737837 : Nat := 4983230072969 + 3 ^ 40 * 737837 * 2
def baseEnd_737837 : Nat := 112256303902677020161261

theorem tailTrace_737837 : CollatzResearch.WordTrace tailWord_737837 prefixEnd_737837 112256303902677020161261 := by
  unfold tailWord_737837
  simp only [CollatzResearch.WordTrace]
  refine ⟨26911126227950036372339765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17940750818633357581559843 26911126227950036372339765)
  ·
    refine ⟨2522918083870315909906853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26911126227950036372339765 2522918083870315909906853)
    ·
      refine ⟨473047140725684233107535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2522918083870315909906853 473047140725684233107535)
      ·
        refine ⟨709570711088526349661303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473047140725684233107535 709570711088526349661303)
        ·
          refine ⟨1064356066632789524491955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 709570711088526349661303 1064356066632789524491955)
          ·
            refine ⟨1596534099949184286737933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064356066632789524491955 1596534099949184286737933)
            ·
              refine ⟨598700287480944107526725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1596534099949184286737933 598700287480944107526725)
              ·
                refine ⟨112256303902677020161261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598700287480944107526725 112256303902677020161261)
                ·
                  rfl

theorem cell20_737837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4].length) (baseStart_737837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737837 prefixEnd_737837 := by exact prefixLift 737837
  have htrace : WordTrace (prefixWord ++ tailWord_737837) baseStart_737837 baseEnd_737837 := by
    simpa [prefixWord, tailWord_737837, baseEnd_737837] using wordTrace_append hprefix tailTrace_737837
  have hstable : (prefixWord ++ tailWord_737837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737837).length < 2 ^ (prefixWord ++ tailWord_737837).sum := by decide
  have hdescent : baseEnd_737837 < baseStart_737837 := by decide
  rcases family_descends (prefixWord ++ tailWord_737837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737855 : List Nat := [1, 1, 2, 2, 3, 2, 4, 3, 2]
def baseStart_737855 : Nat := 118140960795 + 737855 * 2 ^ 59
def prefixEnd_737855 : Nat := 4983230072969 + 3 ^ 40 * 737855 * 2
def baseEnd_737855 : Nat := 336777127398502997883709

theorem tailTrace_737855 : CollatzResearch.WordTrace tailWord_737855 prefixEnd_737855 336777127398502997883709 := by
  unfold tailWord_737855
  simp only [CollatzResearch.WordTrace]
  refine ⟨26911782741884825446495019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17941188494589883630996679 26911782741884825446495019)
  ·
    refine ⟨40367674112827238169742529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26911782741884825446495019 40367674112827238169742529)
    ·
      refine ⟨30275755584620428627306897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40367674112827238169742529 30275755584620428627306897)
      ·
        refine ⟨22706816688465321470480173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30275755584620428627306897 22706816688465321470480173)
        ·
          refine ⟨8515056258174495551430065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22706816688465321470480173 8515056258174495551430065)
          ·
            refine ⟨6386292193630871663572549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8515056258174495551430065 6386292193630871663572549)
            ·
              refine ⟨1197429786305788436919853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6386292193630871663572549 1197429786305788436919853)
              ·
                refine ⟨449036169864670663844945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1197429786305788436919853 449036169864670663844945)
                ·
                  refine ⟨336777127398502997883709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449036169864670663844945 336777127398502997883709)
                  ·
                    rfl

theorem cell20_737855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 2].length) (baseStart_737855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737855 prefixEnd_737855 := by exact prefixLift 737855
  have htrace : WordTrace (prefixWord ++ tailWord_737855) baseStart_737855 baseEnd_737855 := by
    simpa [prefixWord, tailWord_737855, baseEnd_737855] using wordTrace_append hprefix tailTrace_737855
  have hstable : (prefixWord ++ tailWord_737855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737855).length < 2 ^ (prefixWord ++ tailWord_737855).sum := by decide
  have hdescent : baseEnd_737855 < baseStart_737855 := by decide
  rcases family_descends (prefixWord ++ tailWord_737855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737876 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_737876 : Nat := 118140960795 + 737876 * 2 ^ 59
def prefixEnd_737876 : Nat := 4983230072969 + 3 ^ 40 * 737876 * 2
def baseEnd_737876 : Nat := 336786712370720258183623

theorem tailTrace_737876 : CollatzResearch.WordTrace tailWord_737876 prefixEnd_737876 336786712370720258183623 := by
  unfold tailWord_737876
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456274337404373016504741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17941699116539164022006321 13456274337404373016504741)
  ·
    refine ⟨2523051438263319940594639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13456274337404373016504741 2523051438263319940594639)
    ·
      refine ⟨3784577157394979910891959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523051438263319940594639 3784577157394979910891959)
      ·
        refine ⟨5676865736092469866337939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3784577157394979910891959 5676865736092469866337939)
        ·
          refine ⟨8515298604138704799506909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5676865736092469866337939 8515298604138704799506909)
          ·
            refine ⟨3193236976552014299815091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8515298604138704799506909 3193236976552014299815091)
            ·
              refine ⟨4789855464828021449722637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3193236976552014299815091 4789855464828021449722637)
              ·
                refine ⟨1796195799310508043645989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4789855464828021449722637 1796195799310508043645989)
                ·
                  refine ⟨336786712370720258183623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796195799310508043645989 336786712370720258183623)
                  ·
                    rfl

theorem cell20_737876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_737876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737876 prefixEnd_737876 := by exact prefixLift 737876
  have htrace : WordTrace (prefixWord ++ tailWord_737876) baseStart_737876 baseEnd_737876 := by
    simpa [prefixWord, tailWord_737876, baseEnd_737876] using wordTrace_append hprefix tailTrace_737876
  have hstable : (prefixWord ++ tailWord_737876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737876).length < 2 ^ (prefixWord ++ tailWord_737876).sum := by decide
  have hdescent : baseEnd_737876 < baseStart_737876 := by decide
  rcases family_descends (prefixWord ++ tailWord_737876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737896 : List Nat := [2, 1, 4, 3, 3, 1, 2, 4]
def baseStart_737896 : Nat := 118140960795 + 737896 * 2 ^ 59
def prefixEnd_737896 : Nat := 4983230072969 + 3 ^ 40 * 737896 * 2
def baseEnd_737896 : Nat := 112265280305229692505625

theorem tailTrace_737896 : CollatzResearch.WordTrace tailWord_737896 prefixEnd_737896 112265280305229692505625 := by
  unfold tailWord_737896
  simp only [CollatzResearch.WordTrace]
  refine ⟨13456639067368144724368771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17942185423157526299158361 13456639067368144724368771)
  ·
    refine ⟨20184958601052217086553157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13456639067368144724368771 20184958601052217086553157)
    ·
      refine ⟨3784679737697290703728717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20184958601052217086553157 3784679737697290703728717)
      ·
        refine ⟨1419254901636484013898269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3784679737697290703728717 1419254901636484013898269)
        ·
          refine ⟨532220588113681505211851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1419254901636484013898269 532220588113681505211851)
          ·
            refine ⟨798330882170522257817777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532220588113681505211851 798330882170522257817777)
            ·
              refine ⟨598748161627891693363333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798330882170522257817777 598748161627891693363333)
              ·
                refine ⟨112265280305229692505625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 598748161627891693363333 112265280305229692505625)
                ·
                  rfl

theorem cell20_737896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_737896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737896 prefixEnd_737896 := by exact prefixLift 737896
  have htrace : WordTrace (prefixWord ++ tailWord_737896) baseStart_737896 baseEnd_737896 := by
    simpa [prefixWord, tailWord_737896, baseEnd_737896] using wordTrace_append hprefix tailTrace_737896
  have hstable : (prefixWord ++ tailWord_737896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737896).length < 2 ^ (prefixWord ++ tailWord_737896).sum := by decide
  have hdescent : baseEnd_737896 < baseStart_737896 := by decide
  rcases family_descends (prefixWord ++ tailWord_737896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737938 : List Nat := [3, 2, 3, 1, 2, 2, 2, 5]
def baseStart_737938 : Nat := 118140960795 + 737938 * 2 ^ 59
def prefixEnd_737938 : Nat := 4983230072969 + 3 ^ 40 * 737938 * 2
def baseEnd_737938 : Nat := 112271670286707866038901

theorem tailTrace_737938 : CollatzResearch.WordTrace tailWord_737938 prefixEnd_737938 112271670286707866038901 := by
  unfold tailWord_737938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6728702500146032655441617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17943206667056087081177645 6728702500146032655441617)
  ·
    refine ⟨5046526875109524491581213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6728702500146032655441617 5046526875109524491581213)
    ·
      refine ⟨1892447578166071684342955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5046526875109524491581213 1892447578166071684342955)
      ·
        refine ⟨2838671367249107526514433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892447578166071684342955 2838671367249107526514433)
        ·
          refine ⟨2129003525436830644885825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2838671367249107526514433 2129003525436830644885825)
          ·
            refine ⟨1596752644077622983664369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2129003525436830644885825 1596752644077622983664369)
            ·
              refine ⟨1197564483058217237748277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596752644077622983664369 1197564483058217237748277)
              ·
                refine ⟨112271670286707866038901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1197564483058217237748277 112271670286707866038901)
                ·
                  rfl

theorem cell20_737938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_737938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737938 prefixEnd_737938 := by exact prefixLift 737938
  have htrace : WordTrace (prefixWord ++ tailWord_737938) baseStart_737938 baseEnd_737938 := by
    simpa [prefixWord, tailWord_737938, baseEnd_737938] using wordTrace_append hprefix tailTrace_737938
  have hstable : (prefixWord ++ tailWord_737938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737938).length < 2 ^ (prefixWord ++ tailWord_737938).sum := by decide
  have hdescent : baseEnd_737938 < baseStart_737938 := by decide
  rcases family_descends (prefixWord ++ tailWord_737938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_737983 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 3]
def baseStart_737983 : Nat := 118140960795 + 737983 * 2 ^ 59
def prefixEnd_737983 : Nat := 4983230072969 + 3 ^ 40 * 737983 * 2
def baseEnd_737983 : Nat := 336835550086303441616519

theorem tailTrace_737983 : CollatzResearch.WordTrace tailWord_737983 prefixEnd_737983 336835550086303441616519 := by
  unfold tailWord_737983
  simp only [CollatzResearch.WordTrace]
  refine ⟨26916451285421103307154603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17944300856947402204769735 26916451285421103307154603)
  ·
    refine ⟨40374676928131654960731905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26916451285421103307154603 40374676928131654960731905)
    ·
      refine ⟨30281007696098741220548929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40374676928131654960731905 30281007696098741220548929)
      ·
        refine ⟨22710755772074055915411697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30281007696098741220548929 22710755772074055915411697)
        ·
          refine ⟨17033066829055541936558773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22710755772074055915411697 17033066829055541936558773)
          ·
            refine ⟨1596850015223957056552385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17033066829055541936558773 1596850015223957056552385)
            ·
              refine ⟨1197637511417967792414289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596850015223957056552385 1197637511417967792414289)
              ·
                refine ⟨898228133563475844310717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1197637511417967792414289 898228133563475844310717)
                ·
                  refine ⟨336835550086303441616519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898228133563475844310717 336835550086303441616519)
                  ·
                    rfl

theorem cell20_737983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_737983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_737983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_737983 prefixEnd_737983 := by exact prefixLift 737983
  have htrace : WordTrace (prefixWord ++ tailWord_737983) baseStart_737983 baseEnd_737983 := by
    simpa [prefixWord, tailWord_737983, baseEnd_737983] using wordTrace_append hprefix tailTrace_737983
  have hstable : (prefixWord ++ tailWord_737983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_737983).length < 2 ^ (prefixWord ++ tailWord_737983).sum := by decide
  have hdescent : baseEnd_737983 < baseStart_737983 := by decide
  rcases family_descends (prefixWord ++ tailWord_737983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738024 : List Nat := [2, 1, 4, 1, 4, 1, 2, 3, 2]
def baseStart_738024 : Nat := 118140960795 + 738024 * 2 ^ 59
def prefixEnd_738024 : Nat := 4983230072969 + 3 ^ 40 * 738024 * 2
def baseEnd_738024 : Nat := 336854263603489521249685

theorem tailTrace_738024 : CollatzResearch.WordTrace tailWord_738024 prefixEnd_738024 336854263603489521249685 := by
  unfold tailWord_738024
  simp only [CollatzResearch.WordTrace]
  refine ⟨13458973339136283654698563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17945297785515044872931417 13458973339136283654698563)
  ·
    refine ⟨20188460008704425482047845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13458973339136283654698563 20188460008704425482047845)
    ·
      refine ⟨3785336251632079777883971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20188460008704425482047845 3785336251632079777883971)
      ·
        refine ⟨5678004377448119666825957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3785336251632079777883971 5678004377448119666825957)
        ·
          refine ⟨1064625820771522437529867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5678004377448119666825957 1064625820771522437529867)
          ·
            refine ⟨1596938731157283656294801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1064625820771522437529867 1596938731157283656294801)
            ·
              refine ⟨1197704048367962742221101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1596938731157283656294801 1197704048367962742221101)
              ·
                refine ⟨449139018137986028332913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1197704048367962742221101 449139018137986028332913)
                ·
                  refine ⟨336854263603489521249685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449139018137986028332913 336854263603489521249685)
                  ·
                    rfl

theorem cell20_738024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 3, 2].length) (baseStart_738024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738024 prefixEnd_738024 := by exact prefixLift 738024
  have htrace : WordTrace (prefixWord ++ tailWord_738024) baseStart_738024 baseEnd_738024 := by
    simpa [prefixWord, tailWord_738024, baseEnd_738024] using wordTrace_append hprefix tailTrace_738024
  have hstable : (prefixWord ++ tailWord_738024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738024).length < 2 ^ (prefixWord ++ tailWord_738024).sum := by decide
  have hdescent : baseEnd_738024 < baseStart_738024 := by decide
  rcases family_descends (prefixWord ++ tailWord_738024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738080 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_738080 : Nat := 118140960795 + 738080 * 2 ^ 59
def prefixEnd_738080 : Nat := 4983230072969 + 3 ^ 40 * 738080 * 2
def baseEnd_738080 : Nat := 336879823529402215382789

theorem tailTrace_738080 : CollatzResearch.WordTrace tailWord_738080 prefixEnd_738080 336879823529402215382789 := by
  unfold tailWord_738080
  simp only [CollatzResearch.WordTrace]
  refine ⟨13459994583034844436717847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17946659444046459248957129 13459994583034844436717847)
  ·
    refine ⟨20189991874552266655076771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13459994583034844436717847 20189991874552266655076771)
    ·
      refine ⟨30284987811828399982615157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20189991874552266655076771 30284987811828399982615157)
      ·
        refine ⟨2839217607358912498370171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30284987811828399982615157 2839217607358912498370171)
        ·
          refine ⟨4258826411038368747555257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2839217607358912498370171 4258826411038368747555257)
          ·
            refine ⟨3194119808278776560666443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4258826411038368747555257 3194119808278776560666443)
            ·
              refine ⟨4791179712418164840999665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3194119808278776560666443 4791179712418164840999665)
              ·
                refine ⟨3593384784313623630749749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4791179712418164840999665 3593384784313623630749749)
                ·
                  refine ⟨336879823529402215382789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3593384784313623630749749 336879823529402215382789)
                  ·
                    rfl

theorem cell20_738080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_738080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738080 prefixEnd_738080 := by exact prefixLift 738080
  have htrace : WordTrace (prefixWord ++ tailWord_738080) baseStart_738080 baseEnd_738080 := by
    simpa [prefixWord, tailWord_738080, baseEnd_738080] using wordTrace_append hprefix tailTrace_738080
  have hstable : (prefixWord ++ tailWord_738080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738080).length < 2 ^ (prefixWord ++ tailWord_738080).sum := by decide
  have hdescent : baseEnd_738080 < baseStart_738080 := by decide
  rcases family_descends (prefixWord ++ tailWord_738080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738100 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_738100 : Nat := 118140960795 + 738100 * 2 ^ 59
def prefixEnd_738100 : Nat := 4983230072969 + 3 ^ 40 * 738100 * 2
def baseEnd_738100 : Nat := 336888952074371034716041

theorem tailTrace_738100 : CollatzResearch.WordTrace tailWord_738100 prefixEnd_738100 336888952074371034716041 := by
  unfold tailWord_738100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13460359312998616144581877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17947145750664821526109169 13460359312998616144581877)
  ·
    refine ⟨1261908685593620263554551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13460359312998616144581877 1261908685593620263554551)
    ·
      refine ⟨1892863028390430395331827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1261908685593620263554551 1892863028390430395331827)
      ·
        refine ⟨2839294542585645592997741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1892863028390430395331827 2839294542585645592997741)
        ·
          refine ⟨1064735453469617097374153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2839294542585645592997741 1064735453469617097374153)
          ·
            refine ⟨798551590102212823030615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1064735453469617097374153 798551590102212823030615)
            ·
              refine ⟨1197827385153319234545923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798551590102212823030615 1197827385153319234545923)
              ·
                refine ⟨1796741077729978851818885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1197827385153319234545923 1796741077729978851818885)
                ·
                  refine ⟨336888952074371034716041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1796741077729978851818885 336888952074371034716041)
                  ·
                    rfl

theorem cell20_738100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_738100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738100 prefixEnd_738100 := by exact prefixLift 738100
  have htrace : WordTrace (prefixWord ++ tailWord_738100) baseStart_738100 baseEnd_738100 := by
    simpa [prefixWord, tailWord_738100, baseEnd_738100] using wordTrace_append hprefix tailTrace_738100
  have hstable : (prefixWord ++ tailWord_738100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738100).length < 2 ^ (prefixWord ++ tailWord_738100).sum := by decide
  have hdescent : baseEnd_738100 < baseStart_738100 := by decide
  rcases family_descends (prefixWord ++ tailWord_738100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738110 : List Nat := [4, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_738110 : Nat := 118140960795 + 738110 * 2 ^ 59
def prefixEnd_738110 : Nat := 4983230072969 + 3 ^ 40 * 738110 * 2
def baseEnd_738110 : Nat := 336893516346855444382667

theorem tailTrace_738110 : CollatzResearch.WordTrace tailWord_738110 prefixEnd_738110 336893516346855444382667 := by
  unfold tailWord_738110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3365135419495125499628473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17947388903974002664685189 3365135419495125499628473)
  ·
    refine ⟨2523851564621344124721355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3365135419495125499628473 2523851564621344124721355)
    ·
      refine ⟨3785777346932016187082033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2523851564621344124721355 3785777346932016187082033)
      ·
        refine ⟨2839333010199012140311525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3785777346932016187082033 2839333010199012140311525)
        ·
          refine ⟨532374939412314776308411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2839333010199012140311525 532374939412314776308411)
          ·
            refine ⟨798562409118472164462617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532374939412314776308411 798562409118472164462617)
            ·
              refine ⟨598921806838854123346963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798562409118472164462617 598921806838854123346963)
              ·
                refine ⟨898382710258281185020445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 598921806838854123346963 898382710258281185020445)
                ·
                  refine ⟨336893516346855444382667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898382710258281185020445 336893516346855444382667)
                  ·
                    rfl

theorem cell20_738110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_738110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738110 prefixEnd_738110 := by exact prefixLift 738110
  have htrace : WordTrace (prefixWord ++ tailWord_738110) baseStart_738110 baseEnd_738110 := by
    simpa [prefixWord, tailWord_738110, baseEnd_738110] using wordTrace_append hprefix tailTrace_738110
  have hstable : (prefixWord ++ tailWord_738110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738110).length < 2 ^ (prefixWord ++ tailWord_738110).sum := by decide
  have hdescent : baseEnd_738110 < baseStart_738110 := by decide
  rcases family_descends (prefixWord ++ tailWord_738110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738111 : List Nat := [1, 1, 2, 2, 5, 2, 2, 5]
def baseStart_738111 : Nat := 118140960795 + 738111 * 2 ^ 59
def prefixEnd_738111 : Nat := 4983230072969 + 3 ^ 40 * 738111 * 2
def baseEnd_738111 : Nat := 112297990924701295116443

theorem tailTrace_738111 : CollatzResearch.WordTrace tailWord_738111 prefixEnd_738111 112297990924701295116443 := by
  unfold tailWord_738111
  simp only [CollatzResearch.WordTrace]
  refine ⟨26921119828957381167814187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17947413219304920778542791 26921119828957381167814187)
  ·
    refine ⟨40381679743436071751721281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26921119828957381167814187 40381679743436071751721281)
    ·
      refine ⟨30286259807577053813790961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40381679743436071751721281 30286259807577053813790961)
      ·
        refine ⟨22714694855682790360343221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30286259807577053813790961 22714694855682790360343221)
        ·
          refine ⟨2129502642720261596282177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22714694855682790360343221 2129502642720261596282177)
          ·
            refine ⟨1597126982040196197211633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2129502642720261596282177 1597126982040196197211633)
            ·
              refine ⟨1197845236530147147908725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597126982040196197211633 1197845236530147147908725)
              ·
                refine ⟨112297990924701295116443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1197845236530147147908725 112297990924701295116443)
                ·
                  rfl

theorem cell20_738111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 5].length) (baseStart_738111 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738111 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738111 prefixEnd_738111 := by exact prefixLift 738111
  have htrace : WordTrace (prefixWord ++ tailWord_738111) baseStart_738111 baseEnd_738111 := by
    simpa [prefixWord, tailWord_738111, baseEnd_738111] using wordTrace_append hprefix tailTrace_738111
  have hstable : (prefixWord ++ tailWord_738111).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738111).length < 2 ^ (prefixWord ++ tailWord_738111).sum := by decide
  have hdescent : baseEnd_738111 < baseStart_738111 := by decide
  rcases family_descends (prefixWord ++ tailWord_738111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738166 : List Nat := [5, 1, 1, 3, 1, 1, 3, 5]
def baseStart_738166 : Nat := 118140960795 + 738166 * 2 ^ 59
def prefixEnd_738166 : Nat := 4983230072969 + 3 ^ 40 * 738166 * 2
def baseEnd_738166 : Nat := 112306358757589379505257

theorem tailTrace_738166 : CollatzResearch.WordTrace tailWord_738166 prefixEnd_738166 112306358757589379505257 := by
  unfold tailWord_738166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1682695365234882847566647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17948750562505417040710901 1682695365234882847566647)
  ·
    refine ⟨2524043047852324271349971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1682695365234882847566647 2524043047852324271349971)
    ·
      refine ⟨3786064571778486407024957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524043047852324271349971 3786064571778486407024957)
      ·
        refine ⟨1419774214416932402634359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3786064571778486407024957 1419774214416932402634359)
        ·
          refine ⟨2129661321625398603951539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419774214416932402634359 2129661321625398603951539)
          ·
            refine ⟨3194491982438097905927309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2129661321625398603951539 3194491982438097905927309)
            ·
              refine ⟨1197934493414286714722741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3194491982438097905927309 1197934493414286714722741)
              ·
                refine ⟨112306358757589379505257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1197934493414286714722741 112306358757589379505257)
                ·
                  rfl

theorem cell20_738166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_738166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738166 prefixEnd_738166 := by exact prefixLift 738166
  have htrace : WordTrace (prefixWord ++ tailWord_738166) baseStart_738166 baseEnd_738166 := by
    simpa [prefixWord, tailWord_738166, baseEnd_738166] using wordTrace_append hprefix tailTrace_738166
  have hstable : (prefixWord ++ tailWord_738166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738166).length < 2 ^ (prefixWord ++ tailWord_738166).sum := by decide
  have hdescent : baseEnd_738166 < baseStart_738166 := by decide
  rcases family_descends (prefixWord ++ tailWord_738166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738197 : List Nat := [1, 3, 2, 1, 1, 5, 2, 3, 2]
def baseStart_738197 : Nat := 118140960795 + 738197 * 2 ^ 59
def prefixEnd_738197 : Nat := 4983230072969 + 3 ^ 40 * 738197 * 2
def baseEnd_738197 : Nat := 336933225517469808482311

theorem tailTrace_738197 : CollatzResearch.WordTrace tailWord_738197 prefixEnd_738197 336933225517469808482311 := by
  unfold tailWord_738197
  simp only [CollatzResearch.WordTrace]
  refine ⟨26924256506645817855444845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17949504337763878570296563 26924256506645817855444845)
  ·
    refine ⟨10096596189992181695791817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26924256506645817855444845 10096596189992181695791817)
    ·
      refine ⟨7572447142494136271843863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10096596189992181695791817 7572447142494136271843863)
      ·
        refine ⟨11358670713741204407765795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7572447142494136271843863 11358670713741204407765795)
        ·
          refine ⟨17038006070611806611648693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11358670713741204407765795 17038006070611806611648693)
          ·
            refine ⟨1597313069119856869842065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17038006070611806611648693 1597313069119856869842065)
            ·
              refine ⟨1197984801839892652381549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597313069119856869842065 1197984801839892652381549)
              ·
                refine ⟨449244300689959744643081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1197984801839892652381549 449244300689959744643081)
                ·
                  refine ⟨336933225517469808482311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449244300689959744643081 336933225517469808482311)
                  ·
                    rfl

theorem cell20_738197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_738197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738197 prefixEnd_738197 := by exact prefixLift 738197
  have htrace : WordTrace (prefixWord ++ tailWord_738197) baseStart_738197 baseEnd_738197 := by
    simpa [prefixWord, tailWord_738197, baseEnd_738197] using wordTrace_append hprefix tailTrace_738197
  have hstable : (prefixWord ++ tailWord_738197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738197).length < 2 ^ (prefixWord ++ tailWord_738197).sum := by decide
  have hdescent : baseEnd_738197 < baseStart_738197 := by decide
  rcases family_descends (prefixWord ++ tailWord_738197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738287 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 3]
def baseStart_738287 : Nat := 118140960795 + 738287 * 2 ^ 59
def prefixEnd_738287 : Nat := 4983230072969 + 3 ^ 40 * 738287 * 2
def baseEnd_738287 : Nat := 336974303969829495481943

theorem tailTrace_738287 : CollatzResearch.WordTrace tailWord_738287 prefixEnd_738287 336974303969829495481943 := by
  unfold tailWord_738287
  simp only [CollatzResearch.WordTrace]
  refine ⟨26927539076319763226221115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17951692717546508817480743 26927539076319763226221115)
  ·
    refine ⟨40391308614479644839331673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26927539076319763226221115 40391308614479644839331673)
    ·
      refine ⟨30293481460859733629498755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40391308614479644839331673 30293481460859733629498755)
      ·
        refine ⟨45440222191289600444248133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30293481460859733629498755 45440222191289600444248133)
        ·
          refine ⟨8520041660866800083296525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45440222191289600444248133 8520041660866800083296525)
          ·
            refine ⟨3195015622825050031236197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8520041660866800083296525 3195015622825050031236197)
            ·
              refine ⟨599065429279696880856787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3195015622825050031236197 599065429279696880856787)
              ·
                refine ⟨898598143919545321285181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599065429279696880856787 898598143919545321285181)
                ·
                  refine ⟨336974303969829495481943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898598143919545321285181 336974303969829495481943)
                  ·
                    rfl

theorem cell20_738287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 3].length) (baseStart_738287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738287 prefixEnd_738287 := by exact prefixLift 738287
  have htrace : WordTrace (prefixWord ++ tailWord_738287) baseStart_738287 baseEnd_738287 := by
    simpa [prefixWord, tailWord_738287, baseEnd_738287] using wordTrace_append hprefix tailTrace_738287
  have hstable : (prefixWord ++ tailWord_738287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738287).length < 2 ^ (prefixWord ++ tailWord_738287).sum := by decide
  have hdescent : baseEnd_738287 < baseStart_738287 := by decide
  rcases family_descends (prefixWord ++ tailWord_738287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738325 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 3]
def baseStart_738325 : Nat := 118140960795 + 738325 * 2 ^ 59
def prefixEnd_738325 : Nat := 4983230072969 + 3 ^ 40 * 738325 * 2
def baseEnd_738325 : Nat := 336991648205270252215121

theorem tailTrace_738325 : CollatzResearch.WordTrace tailWord_738325 prefixEnd_738325 336991648205270252215121 := by
  unfold tailWord_738325
  simp only [CollatzResearch.WordTrace]
  refine ⟨26928925050182095716104429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17952616700121397144069619 26928925050182095716104429)
  ·
    refine ⟨10098346893818285893539161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26928925050182095716104429 10098346893818285893539161)
    ·
      refine ⟨7573760170363714420154371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10098346893818285893539161 7573760170363714420154371)
      ·
        refine ⟨11360640255545571630231557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7573760170363714420154371 11360640255545571630231557)
        ·
          refine ⟨2130120047914794680668417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11360640255545571630231557 2130120047914794680668417)
          ·
            refine ⟨1597590035936096010501313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2130120047914794680668417 1597590035936096010501313)
            ·
              refine ⟨1198192526952072007875985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597590035936096010501313 1198192526952072007875985)
              ·
                refine ⟨898644395214054005906989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1198192526952072007875985 898644395214054005906989)
                ·
                  refine ⟨336991648205270252215121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898644395214054005906989 336991648205270252215121)
                  ·
                    rfl

theorem cell20_738325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_738325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738325 prefixEnd_738325 := by exact prefixLift 738325
  have htrace : WordTrace (prefixWord ++ tailWord_738325) baseStart_738325 baseEnd_738325 := by
    simpa [prefixWord, tailWord_738325, baseEnd_738325] using wordTrace_append hprefix tailTrace_738325
  have hstable : (prefixWord ++ tailWord_738325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738325).length < 2 ^ (prefixWord ++ tailWord_738325).sum := by decide
  have hdescent : baseEnd_738325 < baseStart_738325 := by decide
  rcases family_descends (prefixWord ++ tailWord_738325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738328 : List Nat := [2, 1, 2, 3, 2, 4, 2, 2, 2]
def baseStart_738328 : Nat := 118140960795 + 738328 * 2 ^ 59
def prefixEnd_738328 : Nat := 4983230072969 + 3 ^ 40 * 738328 * 2
def baseEnd_738328 : Nat := 336993017487015575115109

theorem tailTrace_738328 : CollatzResearch.WordTrace tailWord_738328 prefixEnd_738328 336993017487015575115109 := by
  unfold tailWord_738328
  simp only [CollatzResearch.WordTrace]
  refine ⟨13464517234585613614231819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17952689646114151485642425 13464517234585613614231819)
  ·
    refine ⟨20196775851878420421347729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13464517234585613614231819 20196775851878420421347729)
    ·
      refine ⟨15147581888908815316010797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20196775851878420421347729 15147581888908815316010797)
      ·
        refine ⟨5680343208340805743504049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15147581888908815316010797 5680343208340805743504049)
        ·
          refine ⟨4260257406255604307628037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5680343208340805743504049 4260257406255604307628037)
          ·
            refine ⟨798798263672925807680257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4260257406255604307628037 798798263672925807680257)
            ·
              refine ⟨599098697754694355760193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798798263672925807680257 599098697754694355760193)
              ·
                refine ⟨449324023316020766820145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599098697754694355760193 449324023316020766820145)
                ·
                  refine ⟨336993017487015575115109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449324023316020766820145 336993017487015575115109)
                  ·
                    rfl

theorem cell20_738328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_738328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738328 prefixEnd_738328 := by exact prefixLift 738328
  have htrace : WordTrace (prefixWord ++ tailWord_738328) baseStart_738328 baseEnd_738328 := by
    simpa [prefixWord, tailWord_738328, baseEnd_738328] using wordTrace_append hprefix tailTrace_738328
  have hstable : (prefixWord ++ tailWord_738328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738328).length < 2 ^ (prefixWord ++ tailWord_738328).sum := by decide
  have hdescent : baseEnd_738328 < baseStart_738328 := by decide
  rcases family_descends (prefixWord ++ tailWord_738328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738329 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_738329 : Nat := 118140960795 + 738329 * 2 ^ 59
def prefixEnd_738329 : Nat := 4983230072969 + 3 ^ 40 * 738329 * 2
def baseEnd_738329 : Nat := 336993473914264016081771

theorem tailTrace_738329 : CollatzResearch.WordTrace tailWord_738329 prefixEnd_738329 336993473914264016081771 := by
  unfold tailWord_738329
  simp only [CollatzResearch.WordTrace]
  refine ⟨26929070942167604399250041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17952713961445069599500027 26929070942167604399250041)
  ·
    refine ⟨20196803206625703299437531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26929070942167604399250041 20196803206625703299437531)
    ·
      refine ⟨30295204809938554949156297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20196803206625703299437531 30295204809938554949156297)
      ·
        refine ⟨22721403607453916211867223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30295204809938554949156297 22721403607453916211867223)
        ·
          refine ⟨34082105411180874317800835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22721403607453916211867223 34082105411180874317800835)
          ·
            refine ⟨51123158116771311476701253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34082105411180874317800835 51123158116771311476701253)
            ·
              refine ⟨9585592146894620901881485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51123158116771311476701253 9585592146894620901881485)
              ·
                refine ⟨3594597055085482838205557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9585592146894620901881485 3594597055085482838205557)
                ·
                  refine ⟨336993473914264016081771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594597055085482838205557 336993473914264016081771)
                  ·
                    rfl

theorem cell20_738329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_738329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738329 prefixEnd_738329 := by exact prefixLift 738329
  have htrace : WordTrace (prefixWord ++ tailWord_738329) baseStart_738329 baseEnd_738329 := by
    simpa [prefixWord, tailWord_738329, baseEnd_738329] using wordTrace_append hprefix tailTrace_738329
  have hstable : (prefixWord ++ tailWord_738329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738329).length < 2 ^ (prefixWord ++ tailWord_738329).sum := by decide
  have hdescent : baseEnd_738329 < baseStart_738329 := by decide
  rcases family_descends (prefixWord ++ tailWord_738329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738339 : List Nat := [1, 1, 1, 4, 3, 4, 1, 5]
def baseStart_738339 : Nat := 118140960795 + 738339 * 2 ^ 59
def prefixEnd_738339 : Nat := 4983230072969 + 3 ^ 40 * 738339 * 2
def baseEnd_738339 : Nat := 112332679395582808582799

theorem tailTrace_738339 : CollatzResearch.WordTrace tailWord_738339 prefixEnd_738339 112332679395582808582799 := by
  unfold tailWord_738339
  simp only [CollatzResearch.WordTrace]
  refine ⟨26929435672131376107114071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17952957114754250738076047 26929435672131376107114071)
  ·
    refine ⟨40394153508197064160671107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26929435672131376107114071 40394153508197064160671107)
    ·
      refine ⟨60591230262295596241006661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40394153508197064160671107 60591230262295596241006661)
      ·
        refine ⟨11360855674180424295188749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60591230262295596241006661 11360855674180424295188749)
        ·
          refine ⟨4260320877817659110695781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11360855674180424295188749 4260320877817659110695781)
          ·
            refine ⟨798810164590811083255459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4260320877817659110695781 798810164590811083255459)
            ·
              refine ⟨1198215246886216624883189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798810164590811083255459 1198215246886216624883189)
              ·
                refine ⟨112332679395582808582799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1198215246886216624883189 112332679395582808582799)
                ·
                  rfl

theorem cell20_738339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_738339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738339 prefixEnd_738339 := by exact prefixLift 738339
  have htrace : WordTrace (prefixWord ++ tailWord_738339) baseStart_738339 baseEnd_738339 := by
    simpa [prefixWord, tailWord_738339, baseEnd_738339] using wordTrace_append hprefix tailTrace_738339
  have hstable : (prefixWord ++ tailWord_738339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738339).length < 2 ^ (prefixWord ++ tailWord_738339).sum := by decide
  have hdescent : baseEnd_738339 < baseStart_738339 := by decide
  rcases family_descends (prefixWord ++ tailWord_738339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738353 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_738353 : Nat := 118140960795 + 738353 * 2 ^ 59
def prefixEnd_738353 : Nat := 4983230072969 + 3 ^ 40 * 738353 * 2
def baseEnd_738353 : Nat := 337004428168226599281673

theorem tailTrace_738353 : CollatzResearch.WordTrace tailWord_738353 prefixEnd_738353 337004428168226599281673 := by
  unfold tailWord_738353
  simp only [CollatzResearch.WordTrace]
  refine ⟨26929946294080656498123713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17953297529387104332082475 26929946294080656498123713)
  ·
    refine ⟨20197459720560492373592785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26929946294080656498123713 20197459720560492373592785)
    ·
      refine ⟨15148094790420369280194589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20197459720560492373592785 15148094790420369280194589)
      ·
        refine ⟨5680535546407638480072971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15148094790420369280194589 5680535546407638480072971)
        ·
          refine ⟨8520803319611457720109457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5680535546407638480072971 8520803319611457720109457)
          ·
            refine ⟨6390602489708593290082093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8520803319611457720109457 6390602489708593290082093)
            ·
              refine ⟨2396475933640722483780785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6390602489708593290082093 2396475933640722483780785)
              ·
                refine ⟨1797356950230541862835589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2396475933640722483780785 1797356950230541862835589)
                ·
                  refine ⟨337004428168226599281673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797356950230541862835589 337004428168226599281673)
                  ·
                    rfl

theorem cell20_738353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_738353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738353 prefixEnd_738353 := by exact prefixLift 738353
  have htrace : WordTrace (prefixWord ++ tailWord_738353) baseStart_738353 baseEnd_738353 := by
    simpa [prefixWord, tailWord_738353, baseEnd_738353] using wordTrace_append hprefix tailTrace_738353
  have hstable : (prefixWord ++ tailWord_738353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738353).length < 2 ^ (prefixWord ++ tailWord_738353).sum := by decide
  have hdescent : baseEnd_738353 < baseStart_738353 := by decide
  rcases family_descends (prefixWord ++ tailWord_738353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738366 : List Nat := [4, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_738366 : Nat := 118140960795 + 738366 * 2 ^ 59
def prefixEnd_738366 : Nat := 4983230072969 + 3 ^ 40 * 738366 * 2
def baseEnd_738366 : Nat := 337010361722456331848287

theorem tailTrace_738366 : CollatzResearch.WordTrace tailWord_738366 prefixEnd_738366 337010361722456331848287 := by
  unfold tailWord_738366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366302555379194964793369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17953613628689039812231301 3366302555379194964793369)
  ·
    refine ⟨2524726916534396223595027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3366302555379194964793369 2524726916534396223595027)
    ·
      refine ⟨3787090374801594335392541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524726916534396223595027 3787090374801594335392541)
      ·
        refine ⟨1420158890550597875772203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3787090374801594335392541 1420158890550597875772203)
        ·
          refine ⟨2130238335825896813658305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420158890550597875772203 2130238335825896813658305)
          ·
            refine ⟨1597678751869422610243729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2130238335825896813658305 1597678751869422610243729)
            ·
              refine ⟨1198259063902066957682797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1597678751869422610243729 1198259063902066957682797)
              ·
                refine ⟨449347148963275109131049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198259063902066957682797 449347148963275109131049)
                ·
                  refine ⟨337010361722456331848287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449347148963275109131049 337010361722456331848287)
                  ·
                    rfl

theorem cell20_738366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_738366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738366 prefixEnd_738366 := by exact prefixLift 738366
  have htrace : WordTrace (prefixWord ++ tailWord_738366) baseStart_738366 baseEnd_738366 := by
    simpa [prefixWord, tailWord_738366, baseEnd_738366] using wordTrace_append hprefix tailTrace_738366
  have hstable : (prefixWord ++ tailWord_738366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738366).length < 2 ^ (prefixWord ++ tailWord_738366).sum := by decide
  have hdescent : baseEnd_738366 < baseStart_738366 := by decide
  rcases family_descends (prefixWord ++ tailWord_738366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738367 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 5]
def baseStart_738367 : Nat := 118140960795 + 738367 * 2 ^ 59
def prefixEnd_738367 : Nat := 4983230072969 + 3 ^ 40 * 738367 * 2
def baseEnd_738367 : Nat := 337010818149704772814949

theorem tailTrace_738367 : CollatzResearch.WordTrace tailWord_738367 prefixEnd_738367 337010818149704772814949 := by
  unfold tailWord_738367
  simp only [CollatzResearch.WordTrace]
  refine ⟨26930456916029936889133355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17953637944019957926088903 26930456916029936889133355)
  ·
    refine ⟨40395685374044905333700033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26930456916029936889133355 40395685374044905333700033)
    ·
      refine ⟨30296764030533679000275025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40395685374044905333700033 30296764030533679000275025)
      ·
        refine ⟨22722573022900259250206269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30296764030533679000275025 22722573022900259250206269)
        ·
          refine ⟨8520964883587597218827351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22722573022900259250206269 8520964883587597218827351)
          ·
            refine ⟨12781447325381395828241027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8520964883587597218827351 12781447325381395828241027)
            ·
              refine ⟨19172170988072093742361541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12781447325381395828241027 19172170988072093742361541)
              ·
                refine ⟨3594782060263517576692789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19172170988072093742361541 3594782060263517576692789)
                ·
                  refine ⟨337010818149704772814949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3594782060263517576692789 337010818149704772814949)
                  ·
                    rfl

theorem cell20_738367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 5].length) (baseStart_738367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738367 prefixEnd_738367 := by exact prefixLift 738367
  have htrace : WordTrace (prefixWord ++ tailWord_738367) baseStart_738367 baseEnd_738367 := by
    simpa [prefixWord, tailWord_738367, baseEnd_738367] using wordTrace_append hprefix tailTrace_738367
  have hstable : (prefixWord ++ tailWord_738367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738367).length < 2 ^ (prefixWord ++ tailWord_738367).sum := by decide
  have hdescent : baseEnd_738367 < baseStart_738367 := by decide
  rcases family_descends (prefixWord ++ tailWord_738367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738397 : List Nat := [1, 4, 4, 1, 2, 1, 3, 1, 3]
def baseStart_738397 : Nat := 118140960795 + 738397 * 2 ^ 59
def prefixEnd_738397 : Nat := 4983230072969 + 3 ^ 40 * 738397 * 2
def baseEnd_738397 : Nat := 337024510967158001814827

theorem tailTrace_738397 : CollatzResearch.WordTrace tailWord_738397 prefixEnd_738397 337024510967158001814827 := by
  unfold tailWord_738397
  simp only [CollatzResearch.WordTrace]
  refine ⟨26931551105921252012725445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17954367403947501341816963 26931551105921252012725445)
  ·
    refine ⟨5049665832360234752386021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26931551105921252012725445 5049665832360234752386021)
    ·
      refine ⟨946812343567544016072379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5049665832360234752386021 946812343567544016072379)
      ·
        refine ⟨1420218515351316024108569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946812343567544016072379 1420218515351316024108569)
        ·
          refine ⟨1065163886513487018081427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1420218515351316024108569 1065163886513487018081427)
          ·
            refine ⟨1597745829770230527122141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065163886513487018081427 1597745829770230527122141)
            ·
              refine ⟨599154686163836447670803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1597745829770230527122141 599154686163836447670803)
              ·
                refine ⟨898732029245754671506205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599154686163836447670803 898732029245754671506205)
                ·
                  refine ⟨337024510967158001814827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898732029245754671506205 337024510967158001814827)
                  ·
                    rfl

theorem cell20_738397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_738397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738397 prefixEnd_738397 := by exact prefixLift 738397
  have htrace : WordTrace (prefixWord ++ tailWord_738397) baseStart_738397 baseEnd_738397 := by
    simpa [prefixWord, tailWord_738397, baseEnd_738397] using wordTrace_append hprefix tailTrace_738397
  have hstable : (prefixWord ++ tailWord_738397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738397).length < 2 ^ (prefixWord ++ tailWord_738397).sum := by decide
  have hdescent : baseEnd_738397 < baseStart_738397 := by decide
  rcases family_descends (prefixWord ++ tailWord_738397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738421 : List Nat := [1, 3, 4, 3, 1, 2, 1, 3, 2]
def baseStart_738421 : Nat := 118140960795 + 738421 * 2 ^ 59
def prefixEnd_738421 : Nat := 4983230072969 + 3 ^ 40 * 738421 * 2
def baseEnd_738421 : Nat := 337035465221120585014729

theorem tailTrace_738421 : CollatzResearch.WordTrace tailWord_738421 prefixEnd_738421 337035465221120585014729 := by
  unfold tailWord_738421
  simp only [CollatzResearch.WordTrace]
  refine ⟨26932426457834304111599117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17954950971889536074399411 26932426457834304111599117)
  ·
    refine ⟨10099659921687864041849669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26932426457834304111599117 10099659921687864041849669)
    ·
      refine ⟨1893686235316474507846813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10099659921687864041849669 1893686235316474507846813)
      ·
        refine ⟨710132338243677940442555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1893686235316474507846813 710132338243677940442555)
        ·
          refine ⟨1065198507365516910663833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710132338243677940442555 1065198507365516910663833)
          ·
            refine ⟨798898880524137682997875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065198507365516910663833 798898880524137682997875)
            ·
              refine ⟨1198348320786206524496813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 798898880524137682997875 1198348320786206524496813)
              ·
                refine ⟨449380620294827446686305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198348320786206524496813 449380620294827446686305)
                ·
                  refine ⟨337035465221120585014729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449380620294827446686305 337035465221120585014729)
                  ·
                    rfl

theorem cell20_738421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 2].length) (baseStart_738421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738421 prefixEnd_738421 := by exact prefixLift 738421
  have htrace : WordTrace (prefixWord ++ tailWord_738421) baseStart_738421 baseEnd_738421 := by
    simpa [prefixWord, tailWord_738421, baseEnd_738421] using wordTrace_append hprefix tailTrace_738421
  have hstable : (prefixWord ++ tailWord_738421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738421).length < 2 ^ (prefixWord ++ tailWord_738421).sum := by decide
  have hdescent : baseEnd_738421 < baseStart_738421 := by decide
  rcases family_descends (prefixWord ++ tailWord_738421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738422 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_738422 : Nat := 118140960795 + 738422 * 2 ^ 59
def prefixEnd_738422 : Nat := 4983230072969 + 3 ^ 40 * 738422 * 2
def baseEnd_738422 : Nat := 337035921648369025981391

theorem tailTrace_738422 : CollatzResearch.WordTrace tailWord_738422 prefixEnd_738422 337035921648369025981391 := by
  unfold tailWord_738422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1683278933176917580149095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17954975287220454188257013 1683278933176917580149095)
  ·
    refine ⟨2524918399765376370223643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1683278933176917580149095 2524918399765376370223643)
    ·
      refine ⟨3787377599648064555335465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524918399765376370223643 3787377599648064555335465)
      ·
        refine ⟨2840533199736048416501599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3787377599648064555335465 2840533199736048416501599)
        ·
          refine ⟨4260799799604072624752399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2840533199736048416501599 4260799799604072624752399)
          ·
            refine ⟨6391199699406108937128599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4260799799604072624752399 6391199699406108937128599)
            ·
              refine ⟨9586799549109163405692899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6391199699406108937128599 9586799549109163405692899)
              ·
                refine ⟨14380199323663745108539349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9586799549109163405692899 14380199323663745108539349)
                ·
                  refine ⟨337035921648369025981391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14380199323663745108539349 337035921648369025981391)
                  ·
                    rfl

theorem cell20_738422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_738422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738422 prefixEnd_738422 := by exact prefixLift 738422
  have htrace : WordTrace (prefixWord ++ tailWord_738422) baseStart_738422 baseEnd_738422 := by
    simpa [prefixWord, tailWord_738422, baseEnd_738422] using wordTrace_append hprefix tailTrace_738422
  have hstable : (prefixWord ++ tailWord_738422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738422).length < 2 ^ (prefixWord ++ tailWord_738422).sum := by decide
  have hdescent : baseEnd_738422 < baseStart_738422 := by decide
  rcases family_descends (prefixWord ++ tailWord_738422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738436 : List Nat := [2, 3, 2, 1, 2, 2, 8]
def baseStart_738436 : Nat := 118140960795 + 738436 * 2 ^ 59
def prefixEnd_738436 : Nat := 4983230072969 + 3 ^ 40 * 738436 * 2
def baseEnd_738436 : Nat := 37449145736649688834963

theorem tailTrace_738436 : CollatzResearch.WordTrace tailWord_738436 prefixEnd_738436 37449145736649688834963 := by
  unfold tailWord_738436
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466486776389980836697581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17955315701853307782263441 13466486776389980836697581)
  ·
    refine ⟨5049932541146242813761593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13466486776389980836697581 5049932541146242813761593)
    ·
      refine ⟨3787449405859682110321195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5049932541146242813761593 3787449405859682110321195)
      ·
        refine ⟨5681174108789523165481793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787449405859682110321195 5681174108789523165481793)
        ·
          refine ⟨4260880581592142374111345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5681174108789523165481793 4260880581592142374111345)
          ·
            refine ⟨3195660436194106780583509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4260880581592142374111345 3195660436194106780583509)
            ·
              refine ⟨37449145736649688834963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3195660436194106780583509 37449145736649688834963)
              ·
                rfl

theorem cell20_738436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 8].length) (baseStart_738436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738436 prefixEnd_738436 := by exact prefixLift 738436
  have htrace : WordTrace (prefixWord ++ tailWord_738436) baseStart_738436 baseEnd_738436 := by
    simpa [prefixWord, tailWord_738436, baseEnd_738436] using wordTrace_append hprefix tailTrace_738436
  have hstable : (prefixWord ++ tailWord_738436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738436).length < 2 ^ (prefixWord ++ tailWord_738436).sum := by decide
  have hdescent : baseEnd_738436 < baseStart_738436 := by decide
  rcases family_descends (prefixWord ++ tailWord_738436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738446 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_738446 : Nat := 118140960795 + 738446 * 2 ^ 59
def prefixEnd_738446 : Nat := 4983230072969 + 3 ^ 40 * 738446 * 2
def baseEnd_738446 : Nat := 337046875902331609181293

theorem tailTrace_738446 : CollatzResearch.WordTrace tailWord_738446 prefixEnd_738446 337046875902331609181293 := by
  unfold tailWord_738446
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366667285342966672657399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17955558855162488920839461 3366667285342966672657399)
  ·
    refine ⟨5050000928014450008986099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3366667285342966672657399 5050000928014450008986099)
    ·
      refine ⟨7575001392021675013479149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5050000928014450008986099 7575001392021675013479149)
      ·
        refine ⟨2840625522008128130054681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7575001392021675013479149 2840625522008128130054681)
        ·
          refine ⟨2130469141506096097541011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2840625522008128130054681 2130469141506096097541011)
          ·
            refine ⟨3195703712259144146311517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130469141506096097541011 3195703712259144146311517)
            ·
              refine ⟨1198388892097179054866819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3195703712259144146311517 1198388892097179054866819)
              ·
                refine ⟨1797583338145768582300229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1198388892097179054866819 1797583338145768582300229)
                ·
                  refine ⟨337046875902331609181293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1797583338145768582300229 337046875902331609181293)
                  ·
                    rfl

theorem cell20_738446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_738446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738446 prefixEnd_738446 := by exact prefixLift 738446
  have htrace : WordTrace (prefixWord ++ tailWord_738446) baseStart_738446 baseEnd_738446 := by
    simpa [prefixWord, tailWord_738446, baseEnd_738446] using wordTrace_append hprefix tailTrace_738446
  have hstable : (prefixWord ++ tailWord_738446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738446).length < 2 ^ (prefixWord ++ tailWord_738446).sum := by decide
  have hdescent : baseEnd_738446 < baseStart_738446 := by decide
  rcases family_descends (prefixWord ++ tailWord_738446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738456 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_738456 : Nat := 118140960795 + 738456 * 2 ^ 59
def prefixEnd_738456 : Nat := 4983230072969 + 3 ^ 40 * 738456 * 2
def baseEnd_738456 : Nat := 337051440174816018847919

theorem tailTrace_738456 : CollatzResearch.WordTrace tailWord_738456 prefixEnd_738456 337051440174816018847919 := by
  unfold tailWord_738456
  simp only [CollatzResearch.WordTrace]
  refine ⟨13466851506353752544561611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17955802008471670059415481 13466851506353752544561611)
  ·
    refine ⟨20200277259530628816842417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13466851506353752544561611 20200277259530628816842417)
    ·
      refine ⟨15150207944647971612631813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20200277259530628816842417 15150207944647971612631813)
      ·
        refine ⟨2840663989621494677368465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15150207944647971612631813 2840663989621494677368465)
        ·
          refine ⟨2130497992216121008026349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2840663989621494677368465 2130497992216121008026349)
          ·
            refine ⟨798936747081045378009881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2130497992216121008026349 798936747081045378009881)
            ·
              refine ⟨599202560310784033507411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798936747081045378009881 599202560310784033507411)
              ·
                refine ⟨898803840466176050261117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599202560310784033507411 898803840466176050261117)
                ·
                  refine ⟨337051440174816018847919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 898803840466176050261117 337051440174816018847919)
                  ·
                    rfl

theorem cell20_738456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_738456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738456 prefixEnd_738456 := by exact prefixLift 738456
  have htrace : WordTrace (prefixWord ++ tailWord_738456) baseStart_738456 baseEnd_738456 := by
    simpa [prefixWord, tailWord_738456, baseEnd_738456] using wordTrace_append hprefix tailTrace_738456
  have hstable : (prefixWord ++ tailWord_738456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738456).length < 2 ^ (prefixWord ++ tailWord_738456).sum := by decide
  have hdescent : baseEnd_738456 < baseStart_738456 := by decide
  rcases family_descends (prefixWord ++ tailWord_738456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738488 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_738488 : Nat := 118140960795 + 738488 * 2 ^ 59
def prefixEnd_738488 : Nat := 4983230072969 + 3 ^ 40 * 738488 * 2
def baseEnd_738488 : Nat := 337066045846766129781121

theorem tailTrace_738488 : CollatzResearch.WordTrace tailWord_738488 prefixEnd_738488 337066045846766129781121 := by
  unfold tailWord_738488
  simp only [CollatzResearch.WordTrace]
  refine ⟨13467435074295787277144059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17956580099061049702858745 13467435074295787277144059)
  ·
    refine ⟨20201152611443680915716089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13467435074295787277144059 20201152611443680915716089)
    ·
      refine ⟨15150864458582760686787067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20201152611443680915716089 15150864458582760686787067)
      ·
        refine ⟨22726296687874141030180601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15150864458582760686787067 22726296687874141030180601)
        ·
          refine ⟨17044722515905605772635451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22726296687874141030180601 17044722515905605772635451)
          ·
            refine ⟨25567083773858408658953177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17044722515905605772635451 25567083773858408658953177)
            ·
              refine ⟨19175312830393806494214883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25567083773858408658953177 19175312830393806494214883)
              ·
                refine ⟨28762969245590709741322325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19175312830393806494214883 28762969245590709741322325)
                ·
                  refine ⟨337066045846766129781121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28762969245590709741322325 337066045846766129781121)
                  ·
                    rfl

theorem cell20_738488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_738488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738488 prefixEnd_738488 := by exact prefixLift 738488
  have htrace : WordTrace (prefixWord ++ tailWord_738488) baseStart_738488 baseEnd_738488 := by
    simpa [prefixWord, tailWord_738488, baseEnd_738488] using wordTrace_append hprefix tailTrace_738488
  have hstable : (prefixWord ++ tailWord_738488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738488).length < 2 ^ (prefixWord ++ tailWord_738488).sum := by decide
  have hdescent : baseEnd_738488 < baseStart_738488 := by decide
  rcases family_descends (prefixWord ++ tailWord_738488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738497 : List Nat := [1, 2, 6, 1, 1, 3, 2, 2, 2]
def baseStart_738497 : Nat := 118140960795 + 738497 * 2 ^ 59
def prefixEnd_738497 : Nat := 4983230072969 + 3 ^ 40 * 738497 * 2
def baseEnd_738497 : Nat := 337070153692002098481085

theorem tailTrace_738497 : CollatzResearch.WordTrace tailWord_738497 prefixEnd_738497 337070153692002098481085 := by
  unfold tailWord_738497
  simp only [CollatzResearch.WordTrace]
  refine ⟨26935198405558969091365745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17956798937039312727577163 26935198405558969091365745)
  ·
    refine ⟨20201398804169226818524309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26935198405558969091365745 20201398804169226818524309)
    ·
      refine ⟨946940568945432507118327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20201398804169226818524309 946940568945432507118327)
      ·
        refine ⟨1420410853418148760677491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946940568945432507118327 1420410853418148760677491)
        ·
          refine ⟨2130616280127223141016237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420410853418148760677491 2130616280127223141016237)
          ·
            refine ⟨798981105047708677881089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2130616280127223141016237 798981105047708677881089)
            ·
              refine ⟨599235828785781508410817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798981105047708677881089 599235828785781508410817)
              ·
                refine ⟨449426871589336131308113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599235828785781508410817 449426871589336131308113)
                ·
                  refine ⟨337070153692002098481085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449426871589336131308113 337070153692002098481085)
                  ·
                    rfl

theorem cell20_738497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_738497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738497 prefixEnd_738497 := by exact prefixLift 738497
  have htrace : WordTrace (prefixWord ++ tailWord_738497) baseStart_738497 baseEnd_738497 := by
    simpa [prefixWord, tailWord_738497, baseEnd_738497] using wordTrace_append hprefix tailTrace_738497
  have hstable : (prefixWord ++ tailWord_738497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738497).length < 2 ^ (prefixWord ++ tailWord_738497).sum := by decide
  have hdescent : baseEnd_738497 < baseStart_738497 := by decide
  rcases family_descends (prefixWord ++ tailWord_738497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738529 : List Nat := [1, 2, 3, 1, 3, 3, 3, 4]
def baseStart_738529 : Nat := 118140960795 + 738529 * 2 ^ 59
def prefixEnd_738529 : Nat := 4983230072969 + 3 ^ 40 * 738529 * 2
def baseEnd_738529 : Nat := 112361586454650736471429

theorem tailTrace_738529 : CollatzResearch.WordTrace tailWord_738529 prefixEnd_738529 112361586454650736471429 := by
  unfold tailWord_738529
  simp only [CollatzResearch.WordTrace]
  refine ⟨26936365541443038556530641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17957577027628692371020427 26936365541443038556530641)
  ·
    refine ⟨20202274156082278917397981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26936365541443038556530641 20202274156082278917397981)
    ·
      refine ⟨7575852808530854594024243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20202274156082278917397981 7575852808530854594024243)
      ·
        refine ⟨11363779212796281891036365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7575852808530854594024243 11363779212796281891036365)
        ·
          refine ⟨4261417204798605709138637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11363779212796281891036365 4261417204798605709138637)
          ·
            refine ⟨1598031451799477140926989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4261417204798605709138637 1598031451799477140926989)
            ·
              refine ⟨599261794424803927847621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1598031451799477140926989 599261794424803927847621)
              ·
                refine ⟨112361586454650736471429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599261794424803927847621 112361586454650736471429)
                ·
                  rfl

theorem cell20_738529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 4].length) (baseStart_738529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738529 prefixEnd_738529 := by exact prefixLift 738529
  have htrace : WordTrace (prefixWord ++ tailWord_738529) baseStart_738529 baseEnd_738529 := by
    simpa [prefixWord, tailWord_738529, baseEnd_738529] using wordTrace_append hprefix tailTrace_738529
  have hstable : (prefixWord ++ tailWord_738529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738529).length < 2 ^ (prefixWord ++ tailWord_738529).sum := by decide
  have hdescent : baseEnd_738529 < baseStart_738529 := by decide
  rcases family_descends (prefixWord ++ tailWord_738529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738590 : List Nat := [4, 3, 2, 1, 3, 1, 1, 3, 2]
def baseStart_738590 : Nat := 118140960795 + 738590 * 2 ^ 59
def prefixEnd_738590 : Nat := 4983230072969 + 3 ^ 40 * 738590 * 2
def baseEnd_738590 : Nat := 337112601426107108380705

theorem tailTrace_738590 : CollatzResearch.WordTrace tailWord_738590 prefixEnd_738590 337112601426107108380705 := by
  unfold tailWord_738590
  simp only [CollatzResearch.WordTrace]
  refine ⟨3367323799277755746812653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17959060262814697316334149 3367323799277755746812653)
  ·
    refine ⟨1262746424729158405054745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3367323799277755746812653 1262746424729158405054745)
    ·
      refine ⟨947059818546868803791059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1262746424729158405054745 947059818546868803791059)
      ·
        refine ⟨1420589727820303205686589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947059818546868803791059 1420589727820303205686589)
        ·
          refine ⟨532721147932613702132471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1420589727820303205686589 532721147932613702132471)
          ·
            refine ⟨799081721898920553198707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 532721147932613702132471 799081721898920553198707)
            ·
              refine ⟨1198622582848380829798061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799081721898920553198707 1198622582848380829798061)
              ·
                refine ⟨449483468568142811174273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198622582848380829798061 449483468568142811174273)
                ·
                  refine ⟨337112601426107108380705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449483468568142811174273 337112601426107108380705)
                  ·
                    rfl

theorem cell20_738590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_738590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738590 prefixEnd_738590 := by exact prefixLift 738590
  have htrace : WordTrace (prefixWord ++ tailWord_738590) baseStart_738590 baseEnd_738590 := by
    simpa [prefixWord, tailWord_738590, baseEnd_738590] using wordTrace_append hprefix tailTrace_738590
  have hstable : (prefixWord ++ tailWord_738590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738590).length < 2 ^ (prefixWord ++ tailWord_738590).sum := by decide
  have hdescent : baseEnd_738590 < baseStart_738590 := by decide
  rcases family_descends (prefixWord ++ tailWord_738590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738594 : List Nat := [3, 3, 1, 1, 4, 2, 1, 3, 2]
def baseStart_738594 : Nat := 118140960795 + 738594 * 2 ^ 59
def prefixEnd_738594 : Nat := 4983230072969 + 3 ^ 40 * 738594 * 2
def baseEnd_738594 : Nat := 337114427135100872247355

theorem tailTrace_738594 : CollatzResearch.WordTrace tailWord_738594 prefixEnd_738594 337114427135100872247355 := by
  unfold tailWord_738594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6734684071551888664411709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17959157524138369771764557 6734684071551888664411709)
  ·
    refine ⟨2525506526831958249154391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6734684071551888664411709 2525506526831958249154391)
    ·
      refine ⟨3788259790247937373731587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2525506526831958249154391 3788259790247937373731587)
      ·
        refine ⟨5682389685371906060597381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3788259790247937373731587 5682389685371906060597381)
        ·
          refine ⟨1065448066007232386362009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5682389685371906060597381 1065448066007232386362009)
          ·
            refine ⟨799086049505424289771507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065448066007232386362009 799086049505424289771507)
            ·
              refine ⟨1198629074258136434657261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799086049505424289771507 1198629074258136434657261)
              ·
                refine ⟨449485902846801162996473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1198629074258136434657261 449485902846801162996473)
                ·
                  refine ⟨337114427135100872247355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449485902846801162996473 337114427135100872247355)
                  ·
                    rfl

theorem cell20_738594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_738594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738594 prefixEnd_738594 := by exact prefixLift 738594
  have htrace : WordTrace (prefixWord ++ tailWord_738594) baseStart_738594 baseEnd_738594 := by
    simpa [prefixWord, tailWord_738594, baseEnd_738594] using wordTrace_append hprefix tailTrace_738594
  have hstable : (prefixWord ++ tailWord_738594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738594).length < 2 ^ (prefixWord ++ tailWord_738594).sum := by decide
  have hdescent : baseEnd_738594 < baseStart_738594 := by decide
  rcases family_descends (prefixWord ++ tailWord_738594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738595 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_738595 : Nat := 118140960795 + 738595 * 2 ^ 59
def prefixEnd_738595 : Nat := 4983230072969 + 3 ^ 40 * 738595 * 2
def baseEnd_738595 : Nat := 337114883562349313214017

theorem tailTrace_738595 : CollatzResearch.WordTrace tailWord_738595 prefixEnd_738595 337114883562349313214017 := by
  unfold tailWord_738595
  simp only [CollatzResearch.WordTrace]
  refine ⟨26938772759203931828433239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17959181839469287885622159 26938772759203931828433239)
  ·
    refine ⟨40408159138805897742649859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26938772759203931828433239 40408159138805897742649859)
    ·
      refine ⟨60612238708208846613974789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40408159138805897742649859 60612238708208846613974789)
      ·
        refine ⟨11364794757789158740120273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60612238708208846613974789 11364794757789158740120273)
        ·
          refine ⟨8523596068341869055090205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11364794757789158740120273 8523596068341869055090205)
          ·
            refine ⟨3196348525628200895658827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8523596068341869055090205 3196348525628200895658827)
            ·
              refine ⟨4794522788442301343488241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3196348525628200895658827 4794522788442301343488241)
              ·
                refine ⟨3595892091331726007616181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4794522788442301343488241 3595892091331726007616181)
                ·
                  refine ⟨337114883562349313214017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3595892091331726007616181 337114883562349313214017)
                  ·
                    rfl

theorem cell20_738595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_738595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738595 prefixEnd_738595 := by exact prefixLift 738595
  have htrace : WordTrace (prefixWord ++ tailWord_738595) baseStart_738595 baseEnd_738595 := by
    simpa [prefixWord, tailWord_738595, baseEnd_738595] using wordTrace_append hprefix tailTrace_738595
  have hstable : (prefixWord ++ tailWord_738595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738595).length < 2 ^ (prefixWord ++ tailWord_738595).sum := by decide
  have hdescent : baseEnd_738595 < baseStart_738595 := by decide
  rcases family_descends (prefixWord ++ tailWord_738595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738605 : List Nat := [1, 5, 3, 1, 1, 1, 8]
def baseStart_738605 : Nat := 118140960795 + 738605 * 2 ^ 59
def prefixEnd_738605 : Nat := 4983230072969 + 3 ^ 40 * 738605 * 2
def baseEnd_738605 : Nat := 37457716426092635875627

theorem tailTrace_738605 : CollatzResearch.WordTrace tailWord_738605 prefixEnd_738605 37457716426092635875627 := by
  unfold tailWord_738605
  simp only [CollatzResearch.WordTrace]
  refine ⟨26939137489167703536297269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17959424992778469024198179 26939137489167703536297269)
  ·
    refine ⟨2525544139609472206527869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26939137489167703536297269 2525544139609472206527869)
    ·
      refine ⟨947079052353552077447951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2525544139609472206527869 947079052353552077447951)
      ·
        refine ⟨1420618578530328116171927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947079052353552077447951 1420618578530328116171927)
        ·
          refine ⟨2130927867795492174257891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1420618578530328116171927 2130927867795492174257891)
          ·
            refine ⟨3196391801693238261386837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2130927867795492174257891 3196391801693238261386837)
            ·
              refine ⟨37457716426092635875627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3196391801693238261386837 37457716426092635875627)
              ·
                rfl

theorem cell20_738605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 8].length) (baseStart_738605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738605 prefixEnd_738605 := by exact prefixLift 738605
  have htrace : WordTrace (prefixWord ++ tailWord_738605) baseStart_738605 baseEnd_738605 := by
    simpa [prefixWord, tailWord_738605, baseEnd_738605] using wordTrace_append hprefix tailTrace_738605
  have hstable : (prefixWord ++ tailWord_738605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738605).length < 2 ^ (prefixWord ++ tailWord_738605).sum := by decide
  have hdescent : baseEnd_738605 < baseStart_738605 := by decide
  rcases family_descends (prefixWord ++ tailWord_738605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738612 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_738612 : Nat := 118140960795 + 738612 * 2 ^ 59
def prefixEnd_738612 : Nat := 4983230072969 + 3 ^ 40 * 738612 * 2
def baseEnd_738612 : Nat := 337122642825572809647281

theorem tailTrace_738612 : CollatzResearch.WordTrace tailWord_738612 prefixEnd_738612 337122642825572809647281 := by
  unfold tailWord_738612
  simp only [CollatzResearch.WordTrace]
  refine ⟨13469696400071171865901045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17959595200094895821201393 13469696400071171865901045)
  ·
    refine ⟨1262784037506672362428223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13469696400071171865901045 1262784037506672362428223)
    ·
      refine ⟨1894176056260008543642335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1262784037506672362428223 1894176056260008543642335)
      ·
        refine ⟨2841264084390012815463503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1894176056260008543642335 2841264084390012815463503)
        ·
          refine ⟨4261896126585019223195255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2841264084390012815463503 4261896126585019223195255)
          ·
            refine ⟨6392844189877528834792883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4261896126585019223195255 6392844189877528834792883)
            ·
              refine ⟨9589266284816293252189325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6392844189877528834792883 9589266284816293252189325)
              ·
                refine ⟨3595974856806109969570997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9589266284816293252189325 3595974856806109969570997)
                ·
                  refine ⟨337122642825572809647281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3595974856806109969570997 337122642825572809647281)
                  ·
                    rfl

theorem cell20_738612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_738612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738612 prefixEnd_738612 := by exact prefixLift 738612
  have htrace : WordTrace (prefixWord ++ tailWord_738612) baseStart_738612 baseEnd_738612 := by
    simpa [prefixWord, tailWord_738612, baseEnd_738612] using wordTrace_append hprefix tailTrace_738612
  have hstable : (prefixWord ++ tailWord_738612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738612).length < 2 ^ (prefixWord ++ tailWord_738612).sum := by decide
  have hdescent : baseEnd_738612 < baseStart_738612 := by decide
  rcases family_descends (prefixWord ++ tailWord_738612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738640 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_738640 : Nat := 118140960795 + 738640 * 2 ^ 59
def prefixEnd_738640 : Nat := 4983230072969 + 3 ^ 40 * 738640 * 2
def baseEnd_738640 : Nat := 337135422788529156713833

theorem tailTrace_738640 : CollatzResearch.WordTrace tailWord_738640 prefixEnd_738640 337135422788529156713833 := by
  unfold tailWord_738640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470207022020452256910687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17960276029360603009214249 13470207022020452256910687)
  ·
    refine ⟨20205310533030678385366031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13470207022020452256910687 20205310533030678385366031)
    ·
      refine ⟨30307965799546017578049047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20205310533030678385366031 30307965799546017578049047)
      ·
        refine ⟨45461948699319026367073571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30307965799546017578049047 45461948699319026367073571)
        ·
          refine ⟨68192923048978539550610357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45461948699319026367073571 68192923048978539550610357)
          ·
            refine ⟨6393086535841738082869721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68192923048978539550610357 6393086535841738082869721)
            ·
              refine ⟨4794814901881303562152291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6393086535841738082869721 4794814901881303562152291)
              ·
                refine ⟨7192222352821955343228437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4794814901881303562152291 7192222352821955343228437)
                ·
                  refine ⟨337135422788529156713833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7192222352821955343228437 337135422788529156713833)
                  ·
                    rfl

theorem cell20_738640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_738640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738640 prefixEnd_738640 := by exact prefixLift 738640
  have htrace : WordTrace (prefixWord ++ tailWord_738640) baseStart_738640 baseEnd_738640 := by
    simpa [prefixWord, tailWord_738640, baseEnd_738640] using wordTrace_append hprefix tailTrace_738640
  have hstable : (prefixWord ++ tailWord_738640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738640).length < 2 ^ (prefixWord ++ tailWord_738640).sum := by decide
  have hdescent : baseEnd_738640 < baseStart_738640 := by decide
  rcases family_descends (prefixWord ++ tailWord_738640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738664 : List Nat := [2, 1, 4, 2, 3, 8]
def baseStart_738664 : Nat := 118140960795 + 738664 * 2 ^ 59
def prefixEnd_738664 : Nat := 4983230072969 + 3 ^ 40 * 738664 * 2
def baseEnd_738664 : Nat := 12486902853425619996805

theorem tailTrace_738664 : CollatzResearch.WordTrace tailWord_738664 prefixEnd_738664 12486902853425619996805 := by
  unfold tailWord_738664
  simp only [CollatzResearch.WordTrace]
  refine ⟨13470644697976978306347523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17960859597302637741796697 13470644697976978306347523)
  ·
    refine ⟨20205967046965467459521285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13470644697976978306347523 20205967046965467459521285)
    ·
      refine ⟨3788618821306025148660241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20205967046965467459521285 3788618821306025148660241)
      ·
        refine ⟨2841464115979518861495181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3788618821306025148660241 2841464115979518861495181)
        ·
          refine ⟨1065549043492319573060693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2841464115979518861495181 1065549043492319573060693)
          ·
            refine ⟨12486902853425619996805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1065549043492319573060693 12486902853425619996805)
            ·
              rfl

theorem cell20_738664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 8].length) (baseStart_738664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738664 prefixEnd_738664 := by exact prefixLift 738664
  have htrace : WordTrace (prefixWord ++ tailWord_738664) baseStart_738664 baseEnd_738664 := by
    simpa [prefixWord, tailWord_738664, baseEnd_738664] using wordTrace_append hprefix tailTrace_738664
  have hstable : (prefixWord ++ tailWord_738664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738664).length < 2 ^ (prefixWord ++ tailWord_738664).sum := by decide
  have hdescent : baseEnd_738664 < baseStart_738664 := by decide
  rcases family_descends (prefixWord ++ tailWord_738664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738670 : List Nat := [4, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_738670 : Nat := 118140960795 + 738670 * 2 ^ 59
def prefixEnd_738670 : Nat := 4983230072969 + 3 ^ 40 * 738670 * 2
def baseEnd_738670 : Nat := 337149115605982385713711

theorem tailTrace_738670 : CollatzResearch.WordTrace tailWord_738670 prefixEnd_738670 337149115605982385713711 := by
  unfold tailWord_738670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3367688529241527454676683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17961005489288146424942309 3367688529241527454676683)
  ·
    refine ⟨5051532793862291182015025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3367688529241527454676683 5051532793862291182015025)
    ·
      refine ⟨3788649595396718386511269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5051532793862291182015025 3788649595396718386511269)
      ·
        refine ⟨710371799136884697470863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3788649595396718386511269 710371799136884697470863)
        ·
          refine ⟨1065557698705327046206295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710371799136884697470863 1065557698705327046206295)
          ·
            refine ⟨1598336548057990569309443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065557698705327046206295 1598336548057990569309443)
            ·
              refine ⟨2397504822086985853964165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598336548057990569309443 2397504822086985853964165)
              ·
                refine ⟨449532154141309847618281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2397504822086985853964165 449532154141309847618281)
                ·
                  refine ⟨337149115605982385713711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449532154141309847618281 337149115605982385713711)
                  ·
                    rfl

theorem cell20_738670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_738670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738670 prefixEnd_738670 := by exact prefixLift 738670
  have htrace : WordTrace (prefixWord ++ tailWord_738670) baseStart_738670 baseEnd_738670 := by
    simpa [prefixWord, tailWord_738670, baseEnd_738670] using wordTrace_append hprefix tailTrace_738670
  have hstable : (prefixWord ++ tailWord_738670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738670).length < 2 ^ (prefixWord ++ tailWord_738670).sum := by decide
  have hdescent : baseEnd_738670 < baseStart_738670 := by decide
  rcases family_descends (prefixWord ++ tailWord_738670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738674 : List Nat := [3, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_738674 : Nat := 118140960795 + 738674 * 2 ^ 59
def prefixEnd_738674 : Nat := 4983230072969 + 3 ^ 40 * 738674 * 2
def baseEnd_738674 : Nat := 337150941314976149580361

theorem tailTrace_738674 : CollatzResearch.WordTrace tailWord_738674 prefixEnd_738674 337150941314976149580361 := by
  unfold tailWord_738674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6735413531479432080139769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17961102750611818880372717 6735413531479432080139769)
  ·
    refine ⟨5051560148609574060104827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6735413531479432080139769 5051560148609574060104827)
    ·
      refine ⟨7577340222914361090157241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5051560148609574060104827 7577340222914361090157241)
      ·
        refine ⟨5683005167185770817617931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7577340222914361090157241 5683005167185770817617931)
        ·
          refine ⟨8524507750778656226426897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5683005167185770817617931 8524507750778656226426897)
          ·
            refine ⟨6393380813083992169820173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8524507750778656226426897 6393380813083992169820173)
            ·
              refine ⟨2397517804906497063682565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6393380813083992169820173 2397517804906497063682565)
              ·
                refine ⟨449534588419968199440481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2397517804906497063682565 449534588419968199440481)
                ·
                  refine ⟨337150941314976149580361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449534588419968199440481 337150941314976149580361)
                  ·
                    rfl

theorem cell20_738674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_738674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738674 prefixEnd_738674 := by exact prefixLift 738674
  have htrace : WordTrace (prefixWord ++ tailWord_738674) baseStart_738674 baseEnd_738674 := by
    simpa [prefixWord, tailWord_738674, baseEnd_738674] using wordTrace_append hprefix tailTrace_738674
  have hstable : (prefixWord ++ tailWord_738674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738674).length < 2 ^ (prefixWord ++ tailWord_738674).sum := by decide
  have hdescent : baseEnd_738674 < baseStart_738674 := by decide
  rcases family_descends (prefixWord ++ tailWord_738674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738695 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_738695 : Nat := 118140960795 + 738695 * 2 ^ 59
def prefixEnd_738695 : Nat := 4983230072969 + 3 ^ 40 * 738695 * 2
def baseEnd_738695 : Nat := 337160526287193409880275

theorem tailTrace_738695 : CollatzResearch.WordTrace tailWord_738695 prefixEnd_738695 337160526287193409880275 := by
  unfold tailWord_738695
  simp only [CollatzResearch.WordTrace]
  refine ⟨26942420058841648907073539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17961613372561099271382359 26942420058841648907073539)
  ·
    refine ⟨40413630088262473360610309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26942420058841648907073539 40413630088262473360610309)
    ·
      refine ⟨7577555641549213755114433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40413630088262473360610309 7577555641549213755114433)
      ·
        refine ⟨5683166731161910316335825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7577555641549213755114433 5683166731161910316335825)
        ·
          refine ⟨4262375048371432737251869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5683166731161910316335825 4262375048371432737251869)
          ·
            refine ⟨1598390643139287276469451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4262375048371432737251869 1598390643139287276469451)
            ·
              refine ⟨2397585964708930914704177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598390643139287276469451 2397585964708930914704177)
              ·
                refine ⟨1798189473531698186028133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2397585964708930914704177 1798189473531698186028133)
                ·
                  refine ⟨337160526287193409880275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1798189473531698186028133 337160526287193409880275)
                  ·
                    rfl

theorem cell20_738695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_738695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738695 prefixEnd_738695 := by exact prefixLift 738695
  have htrace : WordTrace (prefixWord ++ tailWord_738695) baseStart_738695 baseEnd_738695 := by
    simpa [prefixWord, tailWord_738695, baseEnd_738695] using wordTrace_append hprefix tailTrace_738695
  have hstable : (prefixWord ++ tailWord_738695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738695).length < 2 ^ (prefixWord ++ tailWord_738695).sum := by decide
  have hdescent : baseEnd_738695 < baseStart_738695 := by decide
  rcases family_descends (prefixWord ++ tailWord_738695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738723 : List Nat := [1, 1, 1, 4, 1, 3, 9]
def baseStart_738723 : Nat := 118140960795 + 738723 * 2 ^ 59
def prefixEnd_738723 : Nat := 4983230072969 + 3 ^ 40 * 738723 * 2
def baseEnd_738723 : Nat := 37463700694461084105203

theorem tailTrace_738723 : CollatzResearch.WordTrace tailWord_738723 prefixEnd_738723 37463700694461084105203 := by
  unfold tailWord_738723
  simp only [CollatzResearch.WordTrace]
  refine ⟨26943441302740209689092823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17962294201826806459395215 26943441302740209689092823)
  ·
    refine ⟨40415161954110314533639235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26943441302740209689092823 40415161954110314533639235)
    ·
      refine ⟨60622742931165471800458853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40415161954110314533639235 60622742931165471800458853)
      ·
        refine ⟨11366764299593525962586035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60622742931165471800458853 11366764299593525962586035)
        ·
          refine ⟨17050146449390288943879053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11366764299593525962586035 17050146449390288943879053)
          ·
            refine ⟨6393804918521358353954645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17050146449390288943879053 6393804918521358353954645)
            ·
              refine ⟨37463700694461084105203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6393804918521358353954645 37463700694461084105203)
              ·
                rfl

theorem cell20_738723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 9].length) (baseStart_738723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738723 prefixEnd_738723 := by exact prefixLift 738723
  have htrace : WordTrace (prefixWord ++ tailWord_738723) baseStart_738723 baseEnd_738723 := by
    simpa [prefixWord, tailWord_738723, baseEnd_738723] using wordTrace_append hprefix tailTrace_738723
  have hstable : (prefixWord ++ tailWord_738723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738723).length < 2 ^ (prefixWord ++ tailWord_738723).sum := by decide
  have hdescent : baseEnd_738723 < baseStart_738723 := by decide
  rcases family_descends (prefixWord ++ tailWord_738723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738778 : List Nat := [3, 1, 1, 2, 3, 4, 6]
def baseStart_738778 : Nat := 118140960795 + 738778 * 2 ^ 59
def prefixEnd_738778 : Nat := 4983230072969 + 3 ^ 40 * 738778 * 2
def baseEnd_738778 : Nat := 37466489972090445568141

theorem tailTrace_738778 : CollatzResearch.WordTrace tailWord_738778 prefixEnd_738778 37466489972090445568141 := by
  unfold tailWord_738778
  simp only [CollatzResearch.WordTrace]
  refine ⟨6736361829385238520586247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17963631545027302721563325 6736361829385238520586247)
  ·
    refine ⟨10104542744077857780879371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6736361829385238520586247 10104542744077857780879371)
    ·
      refine ⟨15156814116116786671319057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10104542744077857780879371 15156814116116786671319057)
      ·
        refine ⟨11367610587087590003489293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15156814116116786671319057 11367610587087590003489293)
        ·
          refine ⟨4262853970157846251308485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11367610587087590003489293 4262853970157846251308485)
          ·
            refine ⟨799285119404596172120341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4262853970157846251308485 799285119404596172120341)
            ·
              refine ⟨37466489972090445568141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 799285119404596172120341 37466489972090445568141)
              ·
                rfl

theorem cell20_738778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 6].length) (baseStart_738778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738778 prefixEnd_738778 := by exact prefixLift 738778
  have htrace : WordTrace (prefixWord ++ tailWord_738778) baseStart_738778 baseEnd_738778 := by
    simpa [prefixWord, tailWord_738778, baseEnd_738778] using wordTrace_append hprefix tailTrace_738778
  have hstable : (prefixWord ++ tailWord_738778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738778).length < 2 ^ (prefixWord ++ tailWord_738778).sum := by decide
  have hdescent : baseEnd_738778 < baseStart_738778 := by decide
  rcases family_descends (prefixWord ++ tailWord_738778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738785 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 5]
def baseStart_738785 : Nat := 118140960795 + 738785 * 2 ^ 59
def prefixEnd_738785 : Nat := 4983230072969 + 3 ^ 40 * 738785 * 2
def baseEnd_738785 : Nat := 337201604739553096879907

theorem tailTrace_738785 : CollatzResearch.WordTrace tailWord_738785 prefixEnd_738785 337201604739553096879907 := by
  unfold tailWord_738785
  simp only [CollatzResearch.WordTrace]
  refine ⟨26945702628515594277849809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17963801752343729518566539 26945702628515594277849809)
  ·
    refine ⟨20209276971386695708387357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26945702628515594277849809 20209276971386695708387357)
    ·
      refine ⟨7578478864270010890645259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20209276971386695708387357 7578478864270010890645259)
      ·
        refine ⟨11367718296405016335967889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7578478864270010890645259 11367718296405016335967889)
        ·
          refine ⟨8525788722303762251975917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11367718296405016335967889 8525788722303762251975917)
          ·
            refine ⟨3197170770863910844490969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8525788722303762251975917 3197170770863910844490969)
            ·
              refine ⟨2397878078147933133368227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3197170770863910844490969 2397878078147933133368227)
              ·
                refine ⟨3596817117221899700052341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2397878078147933133368227 3596817117221899700052341)
                ·
                  refine ⟨337201604739553096879907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3596817117221899700052341 337201604739553096879907)
                  ·
                    rfl

theorem cell20_738785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_738785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738785 prefixEnd_738785 := by exact prefixLift 738785
  have htrace : WordTrace (prefixWord ++ tailWord_738785) baseStart_738785 baseEnd_738785 := by
    simpa [prefixWord, tailWord_738785, baseEnd_738785] using wordTrace_append hprefix tailTrace_738785
  have hstable : (prefixWord ++ tailWord_738785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738785).length < 2 ^ (prefixWord ++ tailWord_738785).sum := by decide
  have hdescent : baseEnd_738785 < baseStart_738785 := by decide
  rcases family_descends (prefixWord ++ tailWord_738785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738799 : List Nat := [1, 1, 2, 1, 4, 1, 3, 7]
def baseStart_738799 : Nat := 118140960795 + 738799 * 2 ^ 59
def prefixEnd_738799 : Nat := 4983230072969 + 3 ^ 40 * 738799 * 2
def baseEnd_738799 : Nat := 112402664907010423471061

theorem tailTrace_738799 : CollatzResearch.WordTrace tailWord_738799 prefixEnd_738799 112402664907010423471061 := by
  unfold tailWord_738799
  simp only [CollatzResearch.WordTrace]
  refine ⟨26946213250464874668859451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17964142166976583112572967 26946213250464874668859451)
  ·
    refine ⟨40419319875697312003289177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26946213250464874668859451 40419319875697312003289177)
    ·
      refine ⟨30314489906772984002466883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40419319875697312003289177 30314489906772984002466883)
      ·
        refine ⟨45471734860159476003700325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30314489906772984002466883 45471734860159476003700325)
        ·
          refine ⟨8525950286279901750693811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45471734860159476003700325 8525950286279901750693811)
          ·
            refine ⟨12788925429419852626040717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8525950286279901750693811 12788925429419852626040717)
            ·
              refine ⟨4795847036032444734765269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12788925429419852626040717 4795847036032444734765269)
              ·
                refine ⟨112402664907010423471061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4795847036032444734765269 112402664907010423471061)
                ·
                  rfl

theorem cell20_738799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_738799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738799 prefixEnd_738799 := by exact prefixLift 738799
  have htrace : WordTrace (prefixWord ++ tailWord_738799) baseStart_738799 baseEnd_738799 := by
    simpa [prefixWord, tailWord_738799, baseEnd_738799] using wordTrace_append hprefix tailTrace_738799
  have hstable : (prefixWord ++ tailWord_738799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738799).length < 2 ^ (prefixWord ++ tailWord_738799).sum := by decide
  have hdescent : baseEnd_738799 < baseStart_738799 := by decide
  rcases family_descends (prefixWord ++ tailWord_738799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738836 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_738836 : Nat := 118140960795 + 738836 * 2 ^ 59
def prefixEnd_738836 : Nat := 4983230072969 + 3 ^ 40 * 738836 * 2
def baseEnd_738836 : Nat := 337224882529223586179699

theorem tailTrace_738836 : CollatzResearch.WordTrace tailWord_738836 prefixEnd_738836 337224882529223586179699 := by
  unfold tailWord_738836
  simp only [CollatzResearch.WordTrace]
  refine ⟨13473781375665414993978181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17965041834220553325304241 13473781375665414993978181)
  ·
    refine ⟨2526334007937265311370909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13473781375665414993978181 2526334007937265311370909)
    ·
      refine ⟨947375252976474491764091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2526334007937265311370909 947375252976474491764091)
      ·
        refine ⟨1421062879464711737646137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 947375252976474491764091 1421062879464711737646137)
        ·
          refine ⟨1065797159598533803234603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1421062879464711737646137 1065797159598533803234603)
          ·
            refine ⟨1598695739397800704851905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1065797159598533803234603 1598695739397800704851905)
            ·
              refine ⟨1199021804548350528638929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598695739397800704851905 1199021804548350528638929)
              ·
                refine ⟨899266353411262896479197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1199021804548350528638929 899266353411262896479197)
                ·
                  refine ⟨337224882529223586179699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899266353411262896479197 337224882529223586179699)
                  ·
                    rfl

theorem cell20_738836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_738836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738836 prefixEnd_738836 := by exact prefixLift 738836
  have htrace : WordTrace (prefixWord ++ tailWord_738836) baseStart_738836 baseEnd_738836 := by
    simpa [prefixWord, tailWord_738836, baseEnd_738836] using wordTrace_append hprefix tailTrace_738836
  have hstable : (prefixWord ++ tailWord_738836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738836).length < 2 ^ (prefixWord ++ tailWord_738836).sum := by decide
  have hdescent : baseEnd_738836 < baseStart_738836 := by decide
  rcases family_descends (prefixWord ++ tailWord_738836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738837 : List Nat := [1, 3, 2, 1, 3, 10]
def baseStart_738837 : Nat := 118140960795 + 738837 * 2 ^ 59
def prefixEnd_738837 : Nat := 4983230072969 + 3 ^ 40 * 738837 * 2
def baseEnd_738837 : Nat := 12489827368758223227643

theorem tailTrace_738837 : CollatzResearch.WordTrace tailWord_738837 prefixEnd_738837 12489827368758223227643 := by
  unfold tailWord_738837
  simp only [CollatzResearch.WordTrace]
  refine ⟨26947599224327207158742765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17965066149551471439161843 26947599224327207158742765)
  ·
    refine ⟨10105349709122702684528537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26947599224327207158742765 10105349709122702684528537)
    ·
      refine ⟨7579012281842027013396403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10105349709122702684528537 7579012281842027013396403)
      ·
        refine ⟨11368518422763040520094605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7579012281842027013396403 11368518422763040520094605)
        ·
          refine ⟨4263194408536140195035477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11368518422763040520094605 4263194408536140195035477)
          ·
            refine ⟨12489827368758223227643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4263194408536140195035477 12489827368758223227643)
            ·
              rfl

theorem cell20_738837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 10].length) (baseStart_738837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738837 prefixEnd_738837 := by exact prefixLift 738837
  have htrace : WordTrace (prefixWord ++ tailWord_738837) baseStart_738837 baseEnd_738837 := by
    simpa [prefixWord, tailWord_738837, baseEnd_738837] using wordTrace_append hprefix tailTrace_738837
  have hstable : (prefixWord ++ tailWord_738837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738837).length < 2 ^ (prefixWord ++ tailWord_738837).sum := by decide
  have hdescent : baseEnd_738837 < baseStart_738837 := by decide
  rcases family_descends (prefixWord ++ tailWord_738837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738846 : List Nat := [4, 3, 3, 1, 1, 2, 1, 5]
def baseStart_738846 : Nat := 118140960795 + 738846 * 2 ^ 59
def prefixEnd_738846 : Nat := 4983230072969 + 3 ^ 40 * 738846 * 2
def baseEnd_738846 : Nat := 112409815600569331948775

theorem tailTrace_738846 : CollatzResearch.WordTrace tailWord_738846 prefixEnd_738846 112409815600569331948775 := by
  unfold tailWord_738846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368490935161825211977549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17965284987529734463880261 3368490935161825211977549)
  ·
    refine ⟨1263184100685684454491581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3368490935161825211977549 1263184100685684454491581)
    ·
      refine ⟨473694037757131670434343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1263184100685684454491581 473694037757131670434343)
      ·
        refine ⟨710541056635697505651515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 473694037757131670434343 710541056635697505651515)
        ·
          refine ⟨1065811584953546258477273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 710541056635697505651515 1065811584953546258477273)
          ·
            refine ⟨799358688715159693857955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065811584953546258477273 799358688715159693857955)
            ·
              refine ⟨1199038033072739540786933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 799358688715159693857955 1199038033072739540786933)
              ·
                refine ⟨112409815600569331948775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1199038033072739540786933 112409815600569331948775)
                ·
                  rfl

theorem cell20_738846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_738846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738846 prefixEnd_738846 := by exact prefixLift 738846
  have htrace : WordTrace (prefixWord ++ tailWord_738846) baseStart_738846 baseEnd_738846 := by
    simpa [prefixWord, tailWord_738846, baseEnd_738846] using wordTrace_append hprefix tailTrace_738846
  have hstable : (prefixWord ++ tailWord_738846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738846).length < 2 ^ (prefixWord ++ tailWord_738846).sum := by decide
  have hdescent : baseEnd_738846 < baseStart_738846 := by decide
  rcases family_descends (prefixWord ++ tailWord_738846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738913 : List Nat := [1, 2, 3, 1, 1, 3, 2, 7]
def baseStart_738913 : Nat := 118140960795 + 738913 * 2 ^ 59
def prefixEnd_738913 : Nat := 4983230072969 + 3 ^ 40 * 738913 * 2
def baseEnd_738913 : Nat := 112420009142451180204239

theorem tailTrace_738913 : CollatzResearch.WordTrace tailWord_738913 prefixEnd_738913 112420009142451180204239 := by
  unfold tailWord_738913
  simp only [CollatzResearch.WordTrace]
  refine ⟨26950371172051872138509393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17966914114701248092339595 26950371172051872138509393)
  ·
    refine ⟨20212778379038904103882045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26950371172051872138509393 20212778379038904103882045)
    ·
      refine ⟨7579791892139589038955767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20212778379038904103882045 7579791892139589038955767)
      ·
        refine ⟨11369687838209383558433651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7579791892139589038955767 11369687838209383558433651)
        ·
          refine ⟨17054531757314075337650477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11369687838209383558433651 17054531757314075337650477)
          ·
            refine ⟨6395449408992778251618929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17054531757314075337650477 6395449408992778251618929)
            ·
              refine ⟨4796587056744583688714197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6395449408992778251618929 4796587056744583688714197)
              ·
                refine ⟨112420009142451180204239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4796587056744583688714197 112420009142451180204239)
                ·
                  rfl

theorem cell20_738913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_738913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738913 prefixEnd_738913 := by exact prefixLift 738913
  have htrace : WordTrace (prefixWord ++ tailWord_738913) baseStart_738913 baseEnd_738913 := by
    simpa [prefixWord, tailWord_738913, baseEnd_738913] using wordTrace_append hprefix tailTrace_738913
  have hstable : (prefixWord ++ tailWord_738913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738913).length < 2 ^ (prefixWord ++ tailWord_738913).sum := by decide
  have hdescent : baseEnd_738913 < baseStart_738913 := by decide
  rcases family_descends (prefixWord ++ tailWord_738913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738926 : List Nat := [4, 1, 2, 2, 3, 2, 2, 4]
def baseStart_738926 : Nat := 118140960795 + 738926 * 2 ^ 59
def prefixEnd_738926 : Nat := 4983230072969 + 3 ^ 40 * 738926 * 2
def baseEnd_738926 : Nat := 112421986993861091059777

theorem tailTrace_738926 : CollatzResearch.WordTrace tailWord_738926 prefixEnd_738926 112421986993861091059777 := by
  unfold tailWord_738926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3368855665125596919841579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17967230214003183572488421 3368855665125596919841579)
  ·
    refine ⟨5053283497688395379762369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3368855665125596919841579 5053283497688395379762369)
    ·
      refine ⟨3789962623266296534821777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5053283497688395379762369 3789962623266296534821777)
      ·
        refine ⟨2842471967449722401116333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3789962623266296534821777 2842471967449722401116333)
        ·
          refine ⟨1065926987793645900418625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2842471967449722401116333 1065926987793645900418625)
          ·
            refine ⟨799445240845234425313969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065926987793645900418625 799445240845234425313969)
            ·
              refine ⟨599583930633925818985477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799445240845234425313969 599583930633925818985477)
              ·
                refine ⟨112421986993861091059777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599583930633925818985477 112421986993861091059777)
                ·
                  rfl

theorem cell20_738926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_738926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738926 prefixEnd_738926 := by exact prefixLift 738926
  have htrace : WordTrace (prefixWord ++ tailWord_738926) baseStart_738926 baseEnd_738926 := by
    simpa [prefixWord, tailWord_738926, baseEnd_738926] using wordTrace_append hprefix tailTrace_738926
  have hstable : (prefixWord ++ tailWord_738926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738926).length < 2 ^ (prefixWord ++ tailWord_738926).sum := by decide
  have hdescent : baseEnd_738926 < baseStart_738926 := by decide
  rcases family_descends (prefixWord ++ tailWord_738926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738930 : List Nat := [3, 2, 1, 2, 3, 2, 1, 6]
def baseStart_738930 : Nat := 118140960795 + 738930 * 2 ^ 59
def prefixEnd_738930 : Nat := 4983230072969 + 3 ^ 40 * 738930 * 2
def baseEnd_738930 : Nat := 112422595563525679015327

theorem tailTrace_738930 : CollatzResearch.WordTrace tailWord_738930 prefixEnd_738930 112422595563525679015327 := by
  unfold tailWord_738930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6737747803247571010469561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17967327475326856027918829 6737747803247571010469561)
  ·
    refine ⟨5053310852435678257852171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6737747803247571010469561 5053310852435678257852171)
    ·
      refine ⟨7579966278653517386778257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5053310852435678257852171 7579966278653517386778257)
      ·
        refine ⟨5684974708990138040083693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7579966278653517386778257 5684974708990138040083693)
        ·
          refine ⟨2131865515871301765031385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5684974708990138040083693 2131865515871301765031385)
          ·
            refine ⟨1598899136903476323773539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2131865515871301765031385 1598899136903476323773539)
            ·
              refine ⟨2398348705355214485660309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1598899136903476323773539 2398348705355214485660309)
              ·
                refine ⟨112422595563525679015327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2398348705355214485660309 112422595563525679015327)
                ·
                  rfl

theorem cell20_738930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_738930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738930 prefixEnd_738930 := by exact prefixLift 738930
  have htrace : WordTrace (prefixWord ++ tailWord_738930) baseStart_738930 baseEnd_738930 := by
    simpa [prefixWord, tailWord_738930, baseEnd_738930] using wordTrace_append hprefix tailTrace_738930
  have hstable : (prefixWord ++ tailWord_738930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738930).length < 2 ^ (prefixWord ++ tailWord_738930).sum := by decide
  have hdescent : baseEnd_738930 < baseStart_738930 := by decide
  rcases family_descends (prefixWord ++ tailWord_738930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738951 : List Nat := [1, 1, 4, 2, 1, 3, 8]
def baseStart_738951 : Nat := 118140960795 + 738951 * 2 ^ 59
def prefixEnd_738951 : Nat := 4983230072969 + 3 ^ 40 * 738951 * 2
def baseEnd_738951 : Nat := 37475263518088255260655

theorem tailTrace_738951 : CollatzResearch.WordTrace tailWord_738951 prefixEnd_738951 37475263518088255260655 := by
  unfold tailWord_738951
  simp only [CollatzResearch.WordTrace]
  refine ⟨26951757145914204628392707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17967838097276136418928471 26951757145914204628392707)
  ·
    refine ⟨40427635718871306942589061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26951757145914204628392707 40427635718871306942589061)
    ·
      refine ⟨7580181697288370051735449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40427635718871306942589061 7580181697288370051735449)
      ·
        refine ⟨5685136272966277538801587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7580181697288370051735449 5685136272966277538801587)
        ·
          refine ⟨8527704409449416308202381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685136272966277538801587 8527704409449416308202381)
          ·
            refine ⟨3197889153543531115575893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8527704409449416308202381 3197889153543531115575893)
            ·
              refine ⟨37475263518088255260655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3197889153543531115575893 37475263518088255260655)
              ·
                rfl

theorem cell20_738951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 8].length) (baseStart_738951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738951 prefixEnd_738951 := by exact prefixLift 738951
  have htrace : WordTrace (prefixWord ++ tailWord_738951) baseStart_738951 baseEnd_738951 := by
    simpa [prefixWord, tailWord_738951, baseEnd_738951] using wordTrace_append hprefix tailTrace_738951
  have hstable : (prefixWord ++ tailWord_738951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738951).length < 2 ^ (prefixWord ++ tailWord_738951).sum := by decide
  have hdescent : baseEnd_738951 < baseStart_738951 := by decide
  rcases family_descends (prefixWord ++ tailWord_738951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_738968 : List Nat := [2, 1, 2, 4, 1, 3, 2, 5]
def baseStart_738968 : Nat := 118140960795 + 738968 * 2 ^ 59
def prefixEnd_738968 : Nat := 4983230072969 + 3 ^ 40 * 738968 * 2
def baseEnd_738968 : Nat := 112428376975339264593053

theorem tailTrace_738968 : CollatzResearch.WordTrace tailWord_738968 prefixEnd_738968 112428376975339264593053 := by
  unfold tailWord_738968
  simp only [CollatzResearch.WordTrace]
  refine ⟨13476188593426308265880779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17968251457901744354507705 13476188593426308265880779)
  ·
    refine ⟨20214282890139462398821169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13476188593426308265880779 20214282890139462398821169)
    ·
      refine ⟨15160712167604596799115877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20214282890139462398821169 15160712167604596799115877)
      ·
        refine ⟨2842633531425861899834227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15160712167604596799115877 2842633531425861899834227)
        ·
          refine ⟨4263950297138792849751341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842633531425861899834227 4263950297138792849751341)
          ·
            refine ⟨1598981361427047318656753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4263950297138792849751341 1598981361427047318656753)
            ·
              refine ⟨1199236021070285488992565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1598981361427047318656753 1199236021070285488992565)
              ·
                refine ⟨112428376975339264593053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1199236021070285488992565 112428376975339264593053)
                ·
                  rfl

theorem cell20_738968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_738968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_738968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_738968 prefixEnd_738968 := by exact prefixLift 738968
  have htrace : WordTrace (prefixWord ++ tailWord_738968) baseStart_738968 baseEnd_738968 := by
    simpa [prefixWord, tailWord_738968, baseEnd_738968] using wordTrace_append hprefix tailTrace_738968
  have hstable : (prefixWord ++ tailWord_738968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_738968).length < 2 ^ (prefixWord ++ tailWord_738968).sum := by decide
  have hdescent : baseEnd_738968 < baseStart_738968 := by decide
  rcases family_descends (prefixWord ++ tailWord_738968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739044 : List Nat := [2, 3, 1, 1, 1, 3, 5, 4]
def baseStart_739044 : Nat := 118140960795 + 739044 * 2 ^ 59
def prefixEnd_739044 : Nat := 4983230072969 + 3 ^ 40 * 739044 * 2
def baseEnd_739044 : Nat := 112439939798966435748505

theorem tailTrace_739044 : CollatzResearch.WordTrace tailWord_739044 prefixEnd_739044 112439939798966435748505 := by
  unfold tailWord_739044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13477574567288640755764093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17970099423051521007685457 13477574567288640755764093)
  ·
    refine ⟨5054090462733240283411535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13477574567288640755764093 5054090462733240283411535)
    ·
      refine ⟨7581135694099860425117303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054090462733240283411535 7581135694099860425117303)
      ·
        refine ⟨11371703541149790637675955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7581135694099860425117303 11371703541149790637675955)
        ·
          refine ⟨17057555311724685956513933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11371703541149790637675955 17057555311724685956513933)
          ·
            refine ⟨6396583241896757233692725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17057555311724685956513933 6396583241896757233692725)
            ·
              refine ⟨599679678927820990658693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6396583241896757233692725 599679678927820990658693)
              ·
                refine ⟨112439939798966435748505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599679678927820990658693 112439939798966435748505)
                ·
                  rfl

theorem cell20_739044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_739044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739044 prefixEnd_739044 := by exact prefixLift 739044
  have htrace : WordTrace (prefixWord ++ tailWord_739044) baseStart_739044 baseEnd_739044 := by
    simpa [prefixWord, tailWord_739044, baseEnd_739044] using wordTrace_append hprefix tailTrace_739044
  have hstable : (prefixWord ++ tailWord_739044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739044).length < 2 ^ (prefixWord ++ tailWord_739044).sum := by decide
  have hdescent : baseEnd_739044 < baseStart_739044 := by decide
  rcases family_descends (prefixWord ++ tailWord_739044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739054 : List Nat := [4, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_739054 : Nat := 118140960795 + 739054 * 2 ^ 59
def prefixEnd_739054 : Nat := 4983230072969 + 3 ^ 40 * 739054 * 2
def baseEnd_739054 : Nat := 337324383669383716912141

theorem tailTrace_739054 : CollatzResearch.WordTrace tailWord_739054 prefixEnd_739054 337324383669383716912141 := by
  unfold tailWord_739054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3369439233067631652424027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17970342576360702146261477 3369439233067631652424027)
  ·
    refine ⟨5054158849601447478636041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3369439233067631652424027 5054158849601447478636041)
    ·
      refine ⟨3790619137201085608977031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5054158849601447478636041 3790619137201085608977031)
      ·
        refine ⟨5685928705801628413465547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3790619137201085608977031 5685928705801628413465547)
        ·
          refine ⟨8528893058702442620198321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5685928705801628413465547 8528893058702442620198321)
          ·
            refine ⟨6396669794026831965148741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8528893058702442620198321 6396669794026831965148741)
            ·
              refine ⟨1199375586380030993465389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6396669794026831965148741 1199375586380030993465389)
              ·
                refine ⟨449765844892511622549521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1199375586380030993465389 449765844892511622549521)
                ·
                  refine ⟨337324383669383716912141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449765844892511622549521 337324383669383716912141)
                  ·
                    rfl

theorem cell20_739054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_739054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739054 prefixEnd_739054 := by exact prefixLift 739054
  have htrace : WordTrace (prefixWord ++ tailWord_739054) baseStart_739054 baseEnd_739054 := by
    simpa [prefixWord, tailWord_739054, baseEnd_739054] using wordTrace_append hprefix tailTrace_739054
  have hstable : (prefixWord ++ tailWord_739054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739054).length < 2 ^ (prefixWord ++ tailWord_739054).sum := by decide
  have hdescent : baseEnd_739054 < baseStart_739054 := by decide
  rcases family_descends (prefixWord ++ tailWord_739054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739058 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 6]
def baseStart_739058 : Nat := 118140960795 + 739058 * 2 ^ 59
def prefixEnd_739058 : Nat := 4983230072969 + 3 ^ 40 * 739058 * 2
def baseEnd_739058 : Nat := 337326209378377480778791

theorem tailTrace_739058 : CollatzResearch.WordTrace tailWord_739058 prefixEnd_739058 337326209378377480778791 := by
  unfold tailWord_739058
  simp only [CollatzResearch.WordTrace]
  refine ⟨6738914939131640475634457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17970439837684374601691885 6738914939131640475634457)
  ·
    refine ⟨5054186204348730356725843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6738914939131640475634457 5054186204348730356725843)
    ·
      refine ⟨7581279306523095535088765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5054186204348730356725843 7581279306523095535088765)
      ·
        refine ⟨2842979739946160825658287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7581279306523095535088765 2842979739946160825658287)
        ·
          refine ⟨4264469609919241238487431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2842979739946160825658287 4264469609919241238487431)
          ·
            refine ⟨6396704414878861857731147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264469609919241238487431 6396704414878861857731147)
            ·
              refine ⟨9595056622318292786596721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6396704414878861857731147 9595056622318292786596721)
              ·
                refine ⟨7196292466738719589947541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9595056622318292786596721 7196292466738719589947541)
                ·
                  refine ⟨337326209378377480778791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7196292466738719589947541 337326209378377480778791)
                  ·
                    rfl

theorem cell20_739058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_739058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739058 prefixEnd_739058 := by exact prefixLift 739058
  have htrace : WordTrace (prefixWord ++ tailWord_739058) baseStart_739058 baseEnd_739058 := by
    simpa [prefixWord, tailWord_739058, baseEnd_739058] using wordTrace_append hprefix tailTrace_739058
  have hstable : (prefixWord ++ tailWord_739058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739058).length < 2 ^ (prefixWord ++ tailWord_739058).sum := by decide
  have hdescent : baseEnd_739058 < baseStart_739058 := by decide
  rcases family_descends (prefixWord ++ tailWord_739058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739072 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_739072 : Nat := 118140960795 + 739072 * 2 ^ 59
def prefixEnd_739072 : Nat := 4983230072969 + 3 ^ 40 * 739072 * 2
def baseEnd_739072 : Nat := 337332599359855654312067

theorem tailTrace_739072 : CollatzResearch.WordTrace tailWord_739072 prefixEnd_739072 337332599359855654312067 := by
  unfold tailWord_739072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13478085189237921146773735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17970780252317228195698313 13478085189237921146773735)
  ·
    refine ⟨20217127783856881720160603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13478085189237921146773735 20217127783856881720160603)
    ·
      refine ⟨30325691675785322580240905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20217127783856881720160603 30325691675785322580240905)
      ·
        refine ⟨22744268756838991935180679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30325691675785322580240905 22744268756838991935180679)
        ·
          refine ⟨34116403135258487902771019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22744268756838991935180679 34116403135258487902771019)
          ·
            refine ⟨51174604702887731854156529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34116403135258487902771019 51174604702887731854156529)
            ·
              refine ⟨38380953527165798890617397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51174604702887731854156529 38380953527165798890617397)
              ·
                refine ⟨3598214393171793645995381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38380953527165798890617397 3598214393171793645995381)
                ·
                  refine ⟨337332599359855654312067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3598214393171793645995381 337332599359855654312067)
                  ·
                    rfl

theorem cell20_739072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_739072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739072 prefixEnd_739072 := by exact prefixLift 739072
  have htrace : WordTrace (prefixWord ++ tailWord_739072) baseStart_739072 baseEnd_739072 := by
    simpa [prefixWord, tailWord_739072, baseEnd_739072] using wordTrace_append hprefix tailTrace_739072
  have hstable : (prefixWord ++ tailWord_739072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739072).length < 2 ^ (prefixWord ++ tailWord_739072).sum := by decide
  have hdescent : baseEnd_739072 < baseStart_739072 := by decide
  rcases family_descends (prefixWord ++ tailWord_739072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739075 : List Nat := [1, 1, 1, 3, 2, 2, 4, 4, 2]
def baseStart_739075 : Nat := 118140960795 + 739075 * 2 ^ 59
def prefixEnd_739075 : Nat := 4983230072969 + 3 ^ 40 * 739075 * 2
def baseEnd_739075 : Nat := 337333968641600977212055

theorem tailTrace_739075 : CollatzResearch.WordTrace tailWord_739075 prefixEnd_739075 337333968641600977212055 := by
  unfold tailWord_739075
  simp only [CollatzResearch.WordTrace]
  refine ⟨26956279797464973805906679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17970853198309982537271119 26956279797464973805906679)
  ·
    refine ⟨40434419696197460708860019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26956279797464973805906679 40434419696197460708860019)
    ·
      refine ⟨60651629544296191063290029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40434419696197460708860019 60651629544296191063290029)
      ·
        refine ⟨22744361079111071648733761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60651629544296191063290029 22744361079111071648733761)
        ·
          refine ⟨17058270809333303736550321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22744361079111071648733761 17058270809333303736550321)
          ·
            refine ⟨12793703106999977802412741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17058270809333303736550321 12793703106999977802412741)
            ·
              refine ⟨2398819332562495837952389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12793703106999977802412741 2398819332562495837952389)
              ·
                refine ⟨449778624855467969616073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2398819332562495837952389 449778624855467969616073)
                ·
                  refine ⟨337333968641600977212055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449778624855467969616073 337333968641600977212055)
                  ·
                    rfl

theorem cell20_739075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 4, 2].length) (baseStart_739075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739075 prefixEnd_739075 := by exact prefixLift 739075
  have htrace : WordTrace (prefixWord ++ tailWord_739075) baseStart_739075 baseEnd_739075 := by
    simpa [prefixWord, tailWord_739075, baseEnd_739075] using wordTrace_append hprefix tailTrace_739075
  have hstable : (prefixWord ++ tailWord_739075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739075).length < 2 ^ (prefixWord ++ tailWord_739075).sum := by decide
  have hdescent : baseEnd_739075 < baseStart_739075 := by decide
  rcases family_descends (prefixWord ++ tailWord_739075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739096 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_739096 : Nat := 118140960795 + 739096 * 2 ^ 59
def prefixEnd_739096 : Nat := 4983230072969 + 3 ^ 40 * 739096 * 2
def baseEnd_739096 : Nat := 337343553613818237511969

theorem tailTrace_739096 : CollatzResearch.WordTrace tailWord_739096 prefixEnd_739096 337343553613818237511969 := by
  unfold tailWord_739096
  simp only [CollatzResearch.WordTrace]
  refine ⟨13478522865194447196210571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17971363820259262928280761 13478522865194447196210571)
  ·
    refine ⟨20217784297791670794315857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13478522865194447196210571 20217784297791670794315857)
    ·
      refine ⟨15163338223343753095736893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20217784297791670794315857 15163338223343753095736893)
      ·
        refine ⟨5686251833753907410901335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15163338223343753095736893 5686251833753907410901335)
        ·
          refine ⟨8529377750630861116352003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5686251833753907410901335 8529377750630861116352003)
          ·
            refine ⟨12794066625946291674528005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8529377750630861116352003 12794066625946291674528005)
            ·
              refine ⟨2398887492364929688974001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12794066625946291674528005 2398887492364929688974001)
              ·
                refine ⟨1799165619273697266730501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2398887492364929688974001 1799165619273697266730501)
                ·
                  refine ⟨337343553613818237511969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799165619273697266730501 337343553613818237511969)
                  ·
                    rfl

theorem cell20_739096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_739096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739096 prefixEnd_739096 := by exact prefixLift 739096
  have htrace : WordTrace (prefixWord ++ tailWord_739096) baseStart_739096 baseEnd_739096 := by
    simpa [prefixWord, tailWord_739096, baseEnd_739096] using wordTrace_append hprefix tailTrace_739096
  have hstable : (prefixWord ++ tailWord_739096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739096).length < 2 ^ (prefixWord ++ tailWord_739096).sum := by decide
  have hdescent : baseEnd_739096 < baseStart_739096 := by decide
  rcases family_descends (prefixWord ++ tailWord_739096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739103 : List Nat := [1, 1, 2, 4, 2, 1, 3, 6]
def baseStart_739103 : Nat := 118140960795 + 739103 * 2 ^ 59
def prefixEnd_739103 : Nat := 4983230072969 + 3 ^ 40 * 739103 * 2
def baseEnd_739103 : Nat := 112448916201519108092869

theorem tailTrace_739103 : CollatzResearch.WordTrace tailWord_739103 prefixEnd_739103 112448916201519108092869 := by
  unfold tailWord_739103
  simp only [CollatzResearch.WordTrace]
  refine ⟨26957301041363534587925963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17971534027575689725283975 26957301041363534587925963)
  ·
    refine ⟨40435951562045301881888945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26957301041363534587925963 40435951562045301881888945)
    ·
      refine ⟨30326963671533976411416709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40435951562045301881888945 30326963671533976411416709)
      ·
        refine ⟨5686305688412620577140633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30326963671533976411416709 5686305688412620577140633)
        ·
          refine ⟨4264729266309465432855475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5686305688412620577140633 4264729266309465432855475)
          ·
            refine ⟨6397093899464198149283213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4264729266309465432855475 6397093899464198149283213)
            ·
              refine ⟨2398910212299074305981205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6397093899464198149283213 2398910212299074305981205)
              ·
                refine ⟨112448916201519108092869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2398910212299074305981205 112448916201519108092869)
                ·
                  rfl

theorem cell20_739103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_739103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739103 prefixEnd_739103 := by exact prefixLift 739103
  have htrace : WordTrace (prefixWord ++ tailWord_739103) baseStart_739103 baseEnd_739103 := by
    simpa [prefixWord, tailWord_739103, baseEnd_739103] using wordTrace_append hprefix tailTrace_739103
  have hstable : (prefixWord ++ tailWord_739103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739103).length < 2 ^ (prefixWord ++ tailWord_739103).sum := by decide
  have hdescent : baseEnd_739103 < baseStart_739103 := by decide
  rcases family_descends (prefixWord ++ tailWord_739103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739126 : List Nat := [5, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_739126 : Nat := 118140960795 + 739126 * 2 ^ 59
def prefixEnd_739126 : Nat := 4983230072969 + 3 ^ 40 * 739126 * 2
def baseEnd_739126 : Nat := 337357246431271466511847

theorem tailTrace_739126 : CollatzResearch.WordTrace tailWord_739126 prefixEnd_739126 337357246431271466511847 := by
  unfold tailWord_739126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1684883745017513094750827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17972093280186806344008821 1684883745017513094750827)
  ·
    refine ⟨2527325617526269642126241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1684883745017513094750827 2527325617526269642126241)
    ·
      refine ⟨1895494213144702231594681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2527325617526269642126241 1895494213144702231594681)
      ·
        refine ⟨1421620659858526673696011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1895494213144702231594681 1421620659858526673696011)
        ·
          refine ⟨2132430989787790010544017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421620659858526673696011 2132430989787790010544017)
          ·
            refine ⟨1599323242340842507908013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2132430989787790010544017 1599323242340842507908013)
            ·
              refine ⟨599746215877815940465505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1599323242340842507908013 599746215877815940465505)
              ·
                refine ⟨449809661908361955349129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 599746215877815940465505 449809661908361955349129)
                ·
                  refine ⟨337357246431271466511847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 449809661908361955349129 337357246431271466511847)
                  ·
                    rfl

theorem cell20_739126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_739126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739126 prefixEnd_739126 := by exact prefixLift 739126
  have htrace : WordTrace (prefixWord ++ tailWord_739126) baseStart_739126 baseEnd_739126 := by
    simpa [prefixWord, tailWord_739126, baseEnd_739126] using wordTrace_append hprefix tailTrace_739126
  have hstable : (prefixWord ++ tailWord_739126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739126).length < 2 ^ (prefixWord ++ tailWord_739126).sum := by decide
  have hdescent : baseEnd_739126 < baseStart_739126 := by decide
  rcases family_descends (prefixWord ++ tailWord_739126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739141 : List Nat := [1, 3, 1, 1, 1, 2, 6, 5]
def baseStart_739141 : Nat := 118140960795 + 739141 * 2 ^ 59
def prefixEnd_739141 : Nat := 4983230072969 + 3 ^ 40 * 739141 * 2
def baseEnd_739141 : Nat := 112454697613332693670595

theorem tailTrace_739141 : CollatzResearch.WordTrace tailWord_739141 prefixEnd_739141 112454697613332693670595 := by
  unfold tailWord_739141
  simp only [CollatzResearch.WordTrace]
  refine ⟨26958687015225867077809277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17972458010150578051872851 26958687015225867077809277)
  ·
    refine ⟨10109507630709700154178479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26958687015225867077809277 10109507630709700154178479)
    ·
      refine ⟨15164261446064550231267719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10109507630709700154178479 15164261446064550231267719)
      ·
        refine ⟨22746392169096825346901579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15164261446064550231267719 22746392169096825346901579)
        ·
          refine ⟨34119588253645238020352369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22746392169096825346901579 34119588253645238020352369)
          ·
            refine ⟨25589691190233928515264277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34119588253645238020352369 25589691190233928515264277)
            ·
              refine ⟨1199516774542215399153013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25589691190233928515264277 1199516774542215399153013)
              ·
                refine ⟨112454697613332693670595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1199516774542215399153013 112454697613332693670595)
                ·
                  rfl

theorem cell20_739141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_739141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739141 prefixEnd_739141 := by exact prefixLift 739141
  have htrace : WordTrace (prefixWord ++ tailWord_739141) baseStart_739141 baseEnd_739141 := by
    simpa [prefixWord, tailWord_739141, baseEnd_739141] using wordTrace_append hprefix tailTrace_739141
  have hstable : (prefixWord ++ tailWord_739141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739141).length < 2 ^ (prefixWord ++ tailWord_739141).sum := by decide
  have hdescent : baseEnd_739141 < baseStart_739141 := by decide
  rcases family_descends (prefixWord ++ tailWord_739141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739144 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_739144 : Nat := 118140960795 + 739144 * 2 ^ 59
def prefixEnd_739144 : Nat := 4983230072969 + 3 ^ 40 * 739144 * 2
def baseEnd_739144 : Nat := 337365462121743403911773

theorem tailTrace_739144 : CollatzResearch.WordTrace tailWord_739144 prefixEnd_739144 337365462121743403911773 := by
  unfold tailWord_739144
  simp only [CollatzResearch.WordTrace]
  refine ⟨13479398217107499295084243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17972530956143332393445657 13479398217107499295084243)
  ·
    refine ⟨20219097325661248942626365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13479398217107499295084243 20219097325661248942626365)
    ·
      refine ⟨7582161497122968353484887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20219097325661248942626365 7582161497122968353484887)
      ·
        refine ⟨11373242245684452530227331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7582161497122968353484887 11373242245684452530227331)
        ·
          refine ⟨17059863368526678795340997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11373242245684452530227331 17059863368526678795340997)
          ·
            refine ⟨3198724381598752274126437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17059863368526678795340997 3198724381598752274126437)
            ·
              refine ⟨599760821549766051398707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3198724381598752274126437 599760821549766051398707)
              ·
                refine ⟨899641232324649077098061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599760821549766051398707 899641232324649077098061)
                ·
                  refine ⟨337365462121743403911773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899641232324649077098061 337365462121743403911773)
                  ·
                    rfl

theorem cell20_739144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_739144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739144 prefixEnd_739144 := by exact prefixLift 739144
  have htrace : WordTrace (prefixWord ++ tailWord_739144) baseStart_739144 baseEnd_739144 := by
    simpa [prefixWord, tailWord_739144, baseEnd_739144] using wordTrace_append hprefix tailTrace_739144
  have hstable : (prefixWord ++ tailWord_739144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739144).length < 2 ^ (prefixWord ++ tailWord_739144).sum := by decide
  have hdescent : baseEnd_739144 < baseStart_739144 := by decide
  rcases family_descends (prefixWord ++ tailWord_739144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739182 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_739182 : Nat := 118140960795 + 739182 * 2 ^ 59
def prefixEnd_739182 : Nat := 4983230072969 + 3 ^ 40 * 739182 * 2
def baseEnd_739182 : Nat := 337382806357184160644951

theorem tailTrace_739182 : CollatzResearch.WordTrace tailWord_739182 prefixEnd_739182 337382806357184160644951 := by
  unfold tailWord_739182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3370022801009666385006475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17973454938718220720034533 3370022801009666385006475)
  ·
    refine ⟨5055034201514499577509713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3370022801009666385006475 5055034201514499577509713)
    ·
      refine ⟨3791275651135874683132285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5055034201514499577509713 3791275651135874683132285)
      ·
        refine ⟨1421728369175953006174607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3791275651135874683132285 1421728369175953006174607)
        ·
          refine ⟨2132592553763929509261911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1421728369175953006174607 2132592553763929509261911)
          ·
            refine ⟨3198888830645894263892867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132592553763929509261911 3198888830645894263892867)
            ·
              refine ⟨4798333245968841395839301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3198888830645894263892867 4798333245968841395839301)
              ·
                refine ⟨899687483619157761719869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4798333245968841395839301 899687483619157761719869)
                ·
                  refine ⟨337382806357184160644951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899687483619157761719869 337382806357184160644951)
                  ·
                    rfl

theorem cell20_739182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_739182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739182 prefixEnd_739182 := by exact prefixLift 739182
  have htrace : WordTrace (prefixWord ++ tailWord_739182) baseStart_739182 baseEnd_739182 := by
    simpa [prefixWord, tailWord_739182, baseEnd_739182] using wordTrace_append hprefix tailTrace_739182
  have hstable : (prefixWord ++ tailWord_739182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739182).length < 2 ^ (prefixWord ++ tailWord_739182).sum := by decide
  have hdescent : baseEnd_739182 < baseStart_739182 := by decide
  rcases family_descends (prefixWord ++ tailWord_739182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739203 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 3]
def baseStart_739203 : Nat := 118140960795 + 739203 * 2 ^ 59
def prefixEnd_739203 : Nat := 4983230072969 + 3 ^ 40 * 739203 * 2
def baseEnd_739203 : Nat := 337392391329401420944865

theorem tailTrace_739203 : CollatzResearch.WordTrace tailWord_739203 prefixEnd_739203 337392391329401420944865 := by
  unfold tailWord_739203
  simp only [CollatzResearch.WordTrace]
  refine ⟨26960948341001251666566263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17973965560667501111044175 26960948341001251666566263)
  ·
    refine ⟨40441422511501877499849395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26960948341001251666566263 40441422511501877499849395)
    ·
      refine ⟨60662133767252816249774093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40441422511501877499849395 60662133767252816249774093)
      ·
        refine ⟨22748300162719806093665285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60662133767252816249774093 22748300162719806093665285)
        ·
          refine ⟨4265306280509963642562241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22748300162719806093665285 4265306280509963642562241)
          ·
            refine ⟨3198979710382472731921681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4265306280509963642562241 3198979710382472731921681)
            ·
              refine ⟨2399234782786854548941261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3198979710382472731921681 2399234782786854548941261)
              ·
                refine ⟨899713043545070455852973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2399234782786854548941261 899713043545070455852973)
                ·
                  refine ⟨337392391329401420944865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899713043545070455852973 337392391329401420944865)
                  ·
                    rfl

theorem cell20_739203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 3].length) (baseStart_739203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739203 prefixEnd_739203 := by exact prefixLift 739203
  have htrace : WordTrace (prefixWord ++ tailWord_739203) baseStart_739203 baseEnd_739203 := by
    simpa [prefixWord, tailWord_739203, baseEnd_739203] using wordTrace_append hprefix tailTrace_739203
  have hstable : (prefixWord ++ tailWord_739203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739203).length < 2 ^ (prefixWord ++ tailWord_739203).sum := by decide
  have hdescent : baseEnd_739203 < baseStart_739203 := by decide
  rcases family_descends (prefixWord ++ tailWord_739203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739234 : List Nat := [3, 3, 1, 2, 3, 1, 7]
def baseStart_739234 : Nat := 118140960795 + 739234 * 2 ^ 59
def prefixEnd_739234 : Nat := 4983230072969 + 3 ^ 40 * 739234 * 2
def baseEnd_739234 : Nat := 37489615619344787879045

theorem tailTrace_739234 : CollatzResearch.WordTrace tailWord_739234 prefixEnd_739234 37489615619344787879045 := by
  unfold tailWord_739234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6740519750972235990236189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17974719335925962640629837 6740519750972235990236189)
  ·
    refine ⟨2527694906614588496338571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6740519750972235990236189 2527694906614588496338571)
    ·
      refine ⟨3791542359921882744507857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2527694906614588496338571 3791542359921882744507857)
      ·
        refine ⟨2843656769941412058380893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3791542359921882744507857 2843656769941412058380893)
        ·
          refine ⟨1066371288728029521892835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2843656769941412058380893 1066371288728029521892835)
          ·
            refine ⟨1599556933092044282839253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066371288728029521892835 1599556933092044282839253)
            ·
              refine ⟨37489615619344787879045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1599556933092044282839253 37489615619344787879045)
              ·
                rfl

theorem cell20_739234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 7].length) (baseStart_739234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739234 prefixEnd_739234 := by exact prefixLift 739234
  have htrace : WordTrace (prefixWord ++ tailWord_739234) baseStart_739234 baseEnd_739234 := by
    simpa [prefixWord, tailWord_739234, baseEnd_739234] using wordTrace_append hprefix tailTrace_739234
  have hstable : (prefixWord ++ tailWord_739234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739234).length < 2 ^ (prefixWord ++ tailWord_739234).sum := by decide
  have hdescent : baseEnd_739234 < baseStart_739234 := by decide
  rcases family_descends (prefixWord ++ tailWord_739234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739269 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 6]
def baseStart_739269 : Nat := 118140960795 + 739269 * 2 ^ 59
def prefixEnd_739269 : Nat := 4983230072969 + 3 ^ 40 * 739269 * 2
def baseEnd_739269 : Nat := 337422515527798524744595

theorem tailTrace_739269 : CollatzResearch.WordTrace tailWord_739269 prefixEnd_739269 337422515527798524744595 := by
  unfold tailWord_739269
  simp only [CollatzResearch.WordTrace]
  refine ⟨26963355558762144938468861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17975570372508096625645907 26963355558762144938468861)
  ·
    refine ⟨10111258334535804351925823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26963355558762144938468861 10111258334535804351925823)
    ·
      refine ⟨15166887501803706527888735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10111258334535804351925823 15166887501803706527888735)
      ·
        refine ⟨22750331252705559791833103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15166887501803706527888735 22750331252705559791833103)
        ·
          refine ⟨34125496879058339687749655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22750331252705559791833103 34125496879058339687749655)
          ·
            refine ⟨51188245318587509531624483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34125496879058339687749655 51188245318587509531624483)
            ·
              refine ⟨76782367977881264297436725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51188245318587509531624483 76782367977881264297436725)
              ·
                refine ⟨7198346997926368527884693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76782367977881264297436725 7198346997926368527884693)
                ·
                  refine ⟨337422515527798524744595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7198346997926368527884693 337422515527798524744595)
                  ·
                    rfl

theorem cell20_739269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_739269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739269 prefixEnd_739269 := by exact prefixLift 739269
  have htrace : WordTrace (prefixWord ++ tailWord_739269) baseStart_739269 baseEnd_739269 := by
    simpa [prefixWord, tailWord_739269, baseEnd_739269] using wordTrace_append hprefix tailTrace_739269
  have hstable : (prefixWord ++ tailWord_739269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739269).length < 2 ^ (prefixWord ++ tailWord_739269).sum := by decide
  have hdescent : baseEnd_739269 < baseStart_739269 := by decide
  rcases family_descends (prefixWord ++ tailWord_739269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739272 : List Nat := [2, 1, 3, 1, 4, 1, 4, 4]
def baseStart_739272 : Nat := 118140960795 + 739272 * 2 ^ 59
def prefixEnd_739272 : Nat := 4983230072969 + 3 ^ 40 * 739272 * 2
def baseEnd_739272 : Nat := 112474628269847949214861

theorem tailTrace_739272 : CollatzResearch.WordTrace tailWord_739272 prefixEnd_739272 112474628269847949214861 := by
  unfold tailWord_739272
  simp only [CollatzResearch.WordTrace]
  refine ⟨13481732488875638225414035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17975643318500850967218713 13481732488875638225414035)
  ·
    refine ⟨20222598733313457338121053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13481732488875638225414035 20222598733313457338121053)
    ·
      refine ⟨7583474524992546501795395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20222598733313457338121053 7583474524992546501795395)
      ·
        refine ⟨11375211787488819752693093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7583474524992546501795395 11375211787488819752693093)
        ·
          refine ⟨2132852210154153703629955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11375211787488819752693093 2132852210154153703629955)
          ·
            refine ⟨3199278315231230555444933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2132852210154153703629955 3199278315231230555444933)
            ·
              refine ⟨599864684105855729145925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3199278315231230555444933 599864684105855729145925)
              ·
                refine ⟨112474628269847949214861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 599864684105855729145925 112474628269847949214861)
                ·
                  rfl

theorem cell20_739272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_739272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739272 prefixEnd_739272 := by exact prefixLift 739272
  have htrace : WordTrace (prefixWord ++ tailWord_739272) baseStart_739272 baseEnd_739272 := by
    simpa [prefixWord, tailWord_739272, baseEnd_739272] using wordTrace_append hprefix tailTrace_739272
  have hstable : (prefixWord ++ tailWord_739272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739272).length < 2 ^ (prefixWord ++ tailWord_739272).sum := by decide
  have hdescent : baseEnd_739272 < baseStart_739272 := by decide
  rcases family_descends (prefixWord ++ tailWord_739272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739300 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_739300 : Nat := 118140960795 + 739300 * 2 ^ 59
def prefixEnd_739300 : Nat := 4983230072969 + 3 ^ 40 * 739300 * 2
def baseEnd_739300 : Nat := 337436664772500194711135

theorem tailTrace_739300 : CollatzResearch.WordTrace tailWord_739300 prefixEnd_739300 337436664772500194711135 := by
  unfold tailWord_739300
  simp only [CollatzResearch.WordTrace]
  refine ⟨13482243110824918616423677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17976324147766558155231569 13482243110824918616423677)
  ·
    refine ⟨5055841166559344481158879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13482243110824918616423677 5055841166559344481158879)
    ·
      refine ⟨7583761749839016721738319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5055841166559344481158879 7583761749839016721738319)
      ·
        refine ⟨11375642624758525082607479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7583761749839016721738319 11375642624758525082607479)
        ·
          refine ⟨17063463937137787623911219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11375642624758525082607479 17063463937137787623911219)
          ·
            refine ⟨25595195905706681435866829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17063463937137787623911219 25595195905706681435866829)
            ·
              refine ⟨9598198464640005538450061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25595195905706681435866829 9598198464640005538450061)
              ·
                refine ⟨3599324424240002076918773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9598198464640005538450061 3599324424240002076918773)
                ·
                  refine ⟨337436664772500194711135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3599324424240002076918773 337436664772500194711135)
                  ·
                    rfl

theorem cell20_739300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_739300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739300 prefixEnd_739300 := by exact prefixLift 739300
  have htrace : WordTrace (prefixWord ++ tailWord_739300) baseStart_739300 baseEnd_739300 := by
    simpa [prefixWord, tailWord_739300, baseEnd_739300] using wordTrace_append hprefix tailTrace_739300
  have hstable : (prefixWord ++ tailWord_739300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739300).length < 2 ^ (prefixWord ++ tailWord_739300).sum := by decide
  have hdescent : baseEnd_739300 < baseStart_739300 := by decide
  rcases family_descends (prefixWord ++ tailWord_739300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739309 : List Nat := [1, 5, 1, 4, 2, 1, 2, 1, 3]
def baseStart_739309 : Nat := 118140960795 + 739309 * 2 ^ 59
def prefixEnd_739309 : Nat := 4983230072969 + 3 ^ 40 * 739309 * 2
def baseEnd_739309 : Nat := 337440772617736163411099

theorem tailTrace_739309 : CollatzResearch.WordTrace tailWord_739309 prefixEnd_739309 337440772617736163411099 := by
  unfold tailWord_739309
  simp only [CollatzResearch.WordTrace]
  refine ⟨26964814478617231769924981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17976542985744821179949987 26964814478617231769924981)
  ·
    refine ⟨2527951357370365478430467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26964814478617231769924981 2527951357370365478430467)
    ·
      refine ⟨3791927036055548217645701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2527951357370365478430467 3791927036055548217645701)
      ·
        refine ⟨710986319260415290808569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3791927036055548217645701 710986319260415290808569)
        ·
          refine ⟨533239739445311468106427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 710986319260415290808569 533239739445311468106427)
          ·
            refine ⟨799859609167967202159641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533239739445311468106427 799859609167967202159641)
            ·
              refine ⟨599894706875975401619731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799859609167967202159641 599894706875975401619731)
              ·
                refine ⟨899842060313963102429597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599894706875975401619731 899842060313963102429597)
                ·
                  refine ⟨337440772617736163411099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899842060313963102429597 337440772617736163411099)
                  ·
                    rfl

theorem cell20_739309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_739309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739309 prefixEnd_739309 := by exact prefixLift 739309
  have htrace : WordTrace (prefixWord ++ tailWord_739309) baseStart_739309 baseEnd_739309 := by
    simpa [prefixWord, tailWord_739309, baseEnd_739309] using wordTrace_append hprefix tailTrace_739309
  have hstable : (prefixWord ++ tailWord_739309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739309).length < 2 ^ (prefixWord ++ tailWord_739309).sum := by decide
  have hdescent : baseEnd_739309 < baseStart_739309 := by decide
  rcases family_descends (prefixWord ++ tailWord_739309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739310 : List Nat := [4, 1, 2, 1, 3, 2, 2, 5]
def baseStart_739310 : Nat := 118140960795 + 739310 * 2 ^ 59
def prefixEnd_739310 : Nat := 4983230072969 + 3 ^ 40 * 739310 * 2
def baseEnd_739310 : Nat := 112480409681661534792587

theorem tailTrace_739310 : CollatzResearch.WordTrace tailWord_739310 prefixEnd_739310 112480409681661534792587 := by
  unfold tailWord_739310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3370606368951701117588923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17976567301075739293807589 3370606368951701117588923)
  ·
    refine ⟨5055909553427551676383385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3370606368951701117588923 5055909553427551676383385)
    ·
      refine ⟨3791932165070663757287539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5055909553427551676383385 3791932165070663757287539)
      ·
        refine ⟨5687898247605995635931309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3791932165070663757287539 5687898247605995635931309)
        ·
          refine ⟨2132961842852248363474241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5687898247605995635931309 2132961842852248363474241)
          ·
            refine ⟨1599721382139186272605681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2132961842852248363474241 1599721382139186272605681)
            ·
              refine ⟨1199791036604389704454261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1599721382139186272605681 1199791036604389704454261)
              ·
                refine ⟨112480409681661534792587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1199791036604389704454261 112480409681661534792587)
                ·
                  rfl

theorem cell20_739310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_739310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739310 prefixEnd_739310 := by exact prefixLift 739310
  have htrace : WordTrace (prefixWord ++ tailWord_739310) baseStart_739310 baseEnd_739310 := by
    simpa [prefixWord, tailWord_739310, baseEnd_739310] using wordTrace_append hprefix tailTrace_739310
  have hstable : (prefixWord ++ tailWord_739310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739310).length < 2 ^ (prefixWord ++ tailWord_739310).sum := by decide
  have hdescent : baseEnd_739310 < baseStart_739310 := by decide
  rcases family_descends (prefixWord ++ tailWord_739310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739313 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 3]
def baseStart_739313 : Nat := 118140960795 + 739313 * 2 ^ 59
def prefixEnd_739313 : Nat := 4983230072969 + 3 ^ 40 * 739313 * 2
def baseEnd_739313 : Nat := 337442598326729927277749

theorem tailTrace_739313 : CollatzResearch.WordTrace tailWord_739313 prefixEnd_739313 337442598326729927277749 := by
  unfold tailWord_739313
  simp only [CollatzResearch.WordTrace]
  refine ⟨26964960370602740453070593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17976640247068493635380395 26964960370602740453070593)
  ·
    refine ⟨20223720277952055339802945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26964960370602740453070593 20223720277952055339802945)
    ·
      refine ⟨15167790208464041504852209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20223720277952055339802945 15167790208464041504852209)
      ·
        refine ⟨11375842656348031128639157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15167790208464041504852209 11375842656348031128639157)
        ·
          refine ⟨1066485249032627918309921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11375842656348031128639157 1066485249032627918309921)
          ·
            refine ⟨799863936774470938732441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1066485249032627918309921 799863936774470938732441)
            ·
              refine ⟨599897952580853204049331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 799863936774470938732441 599897952580853204049331)
              ·
                refine ⟨899846928871279806073997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 599897952580853204049331 899846928871279806073997)
                ·
                  refine ⟨337442598326729927277749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 899846928871279806073997 337442598326729927277749)
                  ·
                    rfl

theorem cell20_739313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_739313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739313 prefixEnd_739313 := by exact prefixLift 739313
  have htrace : WordTrace (prefixWord ++ tailWord_739313) baseStart_739313 baseEnd_739313 := by
    simpa [prefixWord, tailWord_739313, baseEnd_739313] using wordTrace_append hprefix tailTrace_739313
  have hstable : (prefixWord ++ tailWord_739313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739313).length < 2 ^ (prefixWord ++ tailWord_739313).sum := by decide
  have hdescent : baseEnd_739313 < baseStart_739313 := by decide
  rcases family_descends (prefixWord ++ tailWord_739313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739348 : List Nat := [2, 4, 3, 2, 9]
def baseStart_739348 : Nat := 118140960795 + 739348 * 2 ^ 59
def prefixEnd_739348 : Nat := 4983230072969 + 3 ^ 40 * 739348 * 2
def baseEnd_739348 : Nat := 4166155225684263717419

theorem tailTrace_739348 : CollatzResearch.WordTrace tailWord_739348 prefixEnd_739348 4166155225684263717419 := by
  unfold tailWord_739348
  simp only [CollatzResearch.WordTrace]
  refine ⟨13483118462737970715297349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17977491283650627620396465 13483118462737970715297349)
  ·
    refine ⟨2528084711763369509118253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13483118462737970715297349 2528084711763369509118253)
    ·
      refine ⟨948031766911263565919345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2528084711763369509118253 948031766911263565919345)
      ·
        refine ⟨711023825183447674439509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948031766911263565919345 711023825183447674439509)
        ·
          refine ⟨4166155225684263717419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 711023825183447674439509 4166155225684263717419)
          ·
            rfl

theorem cell20_739348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 9].length) (baseStart_739348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739348 prefixEnd_739348 := by exact prefixLift 739348
  have htrace : WordTrace (prefixWord ++ tailWord_739348) baseStart_739348 baseEnd_739348 := by
    simpa [prefixWord, tailWord_739348, baseEnd_739348] using wordTrace_append hprefix tailTrace_739348
  have hstable : (prefixWord ++ tailWord_739348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739348).length < 2 ^ (prefixWord ++ tailWord_739348).sum := by decide
  have hdescent : baseEnd_739348 < baseStart_739348 := by decide
  rcases family_descends (prefixWord ++ tailWord_739348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739362 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_739362 : Nat := 118140960795 + 739362 * 2 ^ 59
def prefixEnd_739362 : Nat := 4983230072969 + 3 ^ 40 * 739362 * 2
def baseEnd_739362 : Nat := 337464963261903534644215

theorem tailTrace_739362 : CollatzResearch.WordTrace tailWord_739362 prefixEnd_739362 337464963261903534644215 := by
  unfold tailWord_739362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6741686886856305455401085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17977831698283481214402893 6741686886856305455401085)
  ·
    refine ⟨2528132582571114545775407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6741686886856305455401085 2528132582571114545775407)
    ·
      refine ⟨3792198873856671818663111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2528132582571114545775407 3792198873856671818663111)
      ·
        refine ⟨5688298310785007727994667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792198873856671818663111 5688298310785007727994667)
        ·
          refine ⟨8532447466177511591992001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5688298310785007727994667 8532447466177511591992001)
          ·
            refine ⟨6399335599633133693994001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8532447466177511591992001 6399335599633133693994001)
            ·
              refine ⟨4799501699724850270495501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6399335599633133693994001 4799501699724850270495501)
              ·
                refine ⟨1799813137396818851435813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4799501699724850270495501 1799813137396818851435813)
                ·
                  refine ⟨337464963261903534644215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799813137396818851435813 337464963261903534644215)
                  ·
                    rfl

theorem cell20_739362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_739362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739362 prefixEnd_739362 := by exact prefixLift 739362
  have htrace : WordTrace (prefixWord ++ tailWord_739362) baseStart_739362 baseEnd_739362 := by
    simpa [prefixWord, tailWord_739362, baseEnd_739362] using wordTrace_append hprefix tailTrace_739362
  have hstable : (prefixWord ++ tailWord_739362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739362).length < 2 ^ (prefixWord ++ tailWord_739362).sum := by decide
  have hdescent : baseEnd_739362 < baseStart_739362 := by decide
  rcases family_descends (prefixWord ++ tailWord_739362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739383 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 6]
def baseStart_739383 : Nat := 118140960795 + 739383 * 2 ^ 59
def prefixEnd_739383 : Nat := 4983230072969 + 3 ^ 40 * 739383 * 2
def baseEnd_739383 : Nat := 337474548234120794944129

theorem tailTrace_739383 : CollatzResearch.WordTrace tailWord_739383 prefixEnd_739383 337474548234120794944129 := by
  unfold tailWord_739383
  simp only [CollatzResearch.WordTrace]
  refine ⟨26967513480349142408118803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17978342320232761605412535 26967513480349142408118803)
  ·
    refine ⟨40451270220523713612178205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26967513480349142408118803 40451270220523713612178205)
    ·
      refine ⟨15169226332696392604566827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40451270220523713612178205 15169226332696392604566827)
      ·
        refine ⟨22753839499044588906850241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15169226332696392604566827 22753839499044588906850241)
        ·
          refine ⟨17065379624283441680137681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22753839499044588906850241 17065379624283441680137681)
          ·
            refine ⟨12799034718212581260103261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17065379624283441680137681 12799034718212581260103261)
            ·
              refine ⟨4799638019329717972538723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12799034718212581260103261 4799638019329717972538723)
              ·
                refine ⟨7199457028994576958808085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4799638019329717972538723 7199457028994576958808085)
                ·
                  refine ⟨337474548234120794944129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7199457028994576958808085 337474548234120794944129)
                  ·
                    rfl

theorem cell20_739383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_739383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739383 prefixEnd_739383 := by exact prefixLift 739383
  have htrace : WordTrace (prefixWord ++ tailWord_739383) baseStart_739383 baseEnd_739383 := by
    simpa [prefixWord, tailWord_739383, baseEnd_739383] using wordTrace_append hprefix tailTrace_739383
  have hstable : (prefixWord ++ tailWord_739383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739383).length < 2 ^ (prefixWord ++ tailWord_739383).sum := by decide
  have hdescent : baseEnd_739383 < baseStart_739383 := by decide
  rcases family_descends (prefixWord ++ tailWord_739383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739438 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_739438 : Nat := 118140960795 + 739438 * 2 ^ 59
def prefixEnd_739438 : Nat := 4983230072969 + 3 ^ 40 * 739438 * 2
def baseEnd_739438 : Nat := 337499651732785048110571

theorem tailTrace_739438 : CollatzResearch.WordTrace tailWord_739438 prefixEnd_739438 337499651732785048110571 := by
  unfold tailWord_739438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371189936893735850171371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17979679663433257867580645 3371189936893735850171371)
  ·
    refine ⟨5056784905340603775257057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371189936893735850171371 5056784905340603775257057)
    ·
      refine ⟨3792588679005452831442793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5056784905340603775257057 3792588679005452831442793)
      ·
        refine ⟨2844441509254089623582095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3792588679005452831442793 2844441509254089623582095)
        ·
          refine ⟨4266662263881134435373143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844441509254089623582095 4266662263881134435373143)
          ·
            refine ⟨6399993395821701653059715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266662263881134435373143 6399993395821701653059715)
            ·
              refine ⟨9599990093732552479589573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6399993395821701653059715 9599990093732552479589573)
              ·
                refine ⟨1799998142574853589923045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9599990093732552479589573 1799998142574853589923045)
                ·
                  refine ⟨337499651732785048110571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1799998142574853589923045 337499651732785048110571)
                  ·
                    rfl

theorem cell20_739438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_739438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739438 prefixEnd_739438 := by exact prefixLift 739438
  have htrace : WordTrace (prefixWord ++ tailWord_739438) baseStart_739438 baseEnd_739438 := by
    simpa [prefixWord, tailWord_739438, baseEnd_739438] using wordTrace_append hprefix tailTrace_739438
  have hstable : (prefixWord ++ tailWord_739438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739438).length < 2 ^ (prefixWord ++ tailWord_739438).sum := by decide
  have hdescent : baseEnd_739438 < baseStart_739438 := by decide
  rcases family_descends (prefixWord ++ tailWord_739438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739452 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_739452 : Nat := 118140960795 + 739452 * 2 ^ 59
def prefixEnd_739452 : Nat := 4983230072969 + 3 ^ 40 * 739452 * 2
def baseEnd_739452 : Nat := 337506041714263221643847

theorem tailTrace_739452 : CollatzResearch.WordTrace tailWord_739452 prefixEnd_739452 337506041714263221643847 := by
  unfold tailWord_739452
  simp only [CollatzResearch.WordTrace]
  refine ⟨13485015058549583596190305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17980020078066111461587073 13485015058549583596190305)
  ·
    refine ⟨10113761293912187697142729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13485015058549583596190305 10113761293912187697142729)
    ·
      refine ⟨7585320970434140772857047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10113761293912187697142729 7585320970434140772857047)
      ·
        refine ⟨11377981455651211159285571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7585320970434140772857047 11377981455651211159285571)
        ·
          refine ⟨17066972183476816738928357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377981455651211159285571 17066972183476816738928357)
          ·
            refine ⟨3200057284401903138549067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17066972183476816738928357 3200057284401903138549067)
            ·
              refine ⟨4800085926602854707823601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200057284401903138549067 4800085926602854707823601)
              ·
                refine ⟨3600064444952141030867701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800085926602854707823601 3600064444952141030867701)
                ·
                  refine ⟨337506041714263221643847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3600064444952141030867701 337506041714263221643847)
                  ·
                    rfl

theorem cell20_739452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_739452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739452 prefixEnd_739452 := by exact prefixLift 739452
  have htrace : WordTrace (prefixWord ++ tailWord_739452) baseStart_739452 baseEnd_739452 := by
    simpa [prefixWord, tailWord_739452, baseEnd_739452] using wordTrace_append hprefix tailTrace_739452
  have hstable : (prefixWord ++ tailWord_739452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739452).length < 2 ^ (prefixWord ++ tailWord_739452).sum := by decide
  have hdescent : baseEnd_739452 < baseStart_739452 := by decide
  rcases family_descends (prefixWord ++ tailWord_739452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739482 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 3]
def baseStart_739482 : Nat := 118140960795 + 739482 * 2 ^ 59
def prefixEnd_739482 : Nat := 4983230072969 + 3 ^ 40 * 739482 * 2
def baseEnd_739482 : Nat := 337519734531716450643725

theorem tailTrace_739482 : CollatzResearch.WordTrace tailWord_739482 prefixEnd_739482 337519734531716450643725 := by
  unfold tailWord_739482
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742781076747620578993175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17980749537993654877315133 6742781076747620578993175)
  ·
    refine ⟨10114171615121430868489763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6742781076747620578993175 10114171615121430868489763)
    ·
      refine ⟨15171257422682146302734645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114171615121430868489763 15171257422682146302734645)
      ·
        refine ⟨1422305383376451215881373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15171257422682146302734645 1422305383376451215881373)
        ·
          refine ⟨533364518766169205955515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1422305383376451215881373 533364518766169205955515)
          ·
            refine ⟨800046778149253808933273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533364518766169205955515 800046778149253808933273)
            ·
              refine ⟨600035083611940356699955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800046778149253808933273 600035083611940356699955)
              ·
                refine ⟨900052625417910535049933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600035083611940356699955 900052625417910535049933)
                ·
                  refine ⟨337519734531716450643725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900052625417910535049933 337519734531716450643725)
                  ·
                    rfl

theorem cell20_739482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 3].length) (baseStart_739482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739482 prefixEnd_739482 := by exact prefixLift 739482
  have htrace : WordTrace (prefixWord ++ tailWord_739482) baseStart_739482 baseEnd_739482 := by
    simpa [prefixWord, tailWord_739482, baseEnd_739482] using wordTrace_append hprefix tailTrace_739482
  have hstable : (prefixWord ++ tailWord_739482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739482).length < 2 ^ (prefixWord ++ tailWord_739482).sum := by decide
  have hdescent : baseEnd_739482 < baseStart_739482 := by decide
  rcases family_descends (prefixWord ++ tailWord_739482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739521 : List Nat := [1, 2, 6, 1, 10]
def baseStart_739521 : Nat := 118140960795 + 739521 * 2 ^ 59
def prefixEnd_739521 : Nat := 4983230072969 + 3 ^ 40 * 739521 * 2
def baseEnd_739521 : Nat := 4167130064128464794365

theorem tailTrace_739521 : CollatzResearch.WordTrace tailWord_739521 prefixEnd_739521 4167130064128464794365 := by
  unfold tailWord_739521
  simp only [CollatzResearch.WordTrace]
  refine ⟨26972546753849191976642417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17981697835899461317761611 26972546753849191976642417)
  ·
    refine ⟨20229410065386893982481813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26972546753849191976642417 20229410065386893982481813)
    ·
      refine ⟨948253596815010655428835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20229410065386893982481813 948253596815010655428835)
      ·
        refine ⟨1422380395222515983143253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948253596815010655428835 1422380395222515983143253)
        ·
          refine ⟨4167130064128464794365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1422380395222515983143253 4167130064128464794365)
          ·
            rfl

theorem cell20_739521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 10].length) (baseStart_739521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739521 prefixEnd_739521 := by exact prefixLift 739521
  have htrace : WordTrace (prefixWord ++ tailWord_739521) baseStart_739521 baseEnd_739521 := by
    simpa [prefixWord, tailWord_739521, baseEnd_739521] using wordTrace_append hprefix tailTrace_739521
  have hstable : (prefixWord ++ tailWord_739521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739521).length < 2 ^ (prefixWord ++ tailWord_739521).sum := by decide
  have hdescent : baseEnd_739521 < baseStart_739521 := by decide
  rcases family_descends (prefixWord ++ tailWord_739521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739524 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_739524 : Nat := 118140960795 + 739524 * 2 ^ 59
def prefixEnd_739524 : Nat := 4983230072969 + 3 ^ 40 * 739524 * 2
def baseEnd_739524 : Nat := 337538904476150971243553

theorem tailTrace_739524 : CollatzResearch.WordTrace tailWord_739524 prefixEnd_739524 337538904476150971243553 := by
  unfold tailWord_739524
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486328086419161744500813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17981770781892215659334417 13486328086419161744500813)
  ·
    refine ⟨5057373032407185654187805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13486328086419161744500813 5057373032407185654187805)
    ·
      refine ⟨1896514887152694620320427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5057373032407185654187805 1896514887152694620320427)
      ·
        refine ⟨2844772330729041930480641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896514887152694620320427 2844772330729041930480641)
        ·
          refine ⟨2133579248046781447860481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844772330729041930480641 2133579248046781447860481)
          ·
            refine ⟨1600184436035086085895361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2133579248046781447860481 1600184436035086085895361)
            ·
              refine ⟨1200138327026314564421521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600184436035086085895361 1200138327026314564421521)
              ·
                refine ⟨900103745269735923316141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200138327026314564421521 900103745269735923316141)
                ·
                  refine ⟨337538904476150971243553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900103745269735923316141 337538904476150971243553)
                  ·
                    rfl

theorem cell20_739524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_739524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739524 prefixEnd_739524 := by exact prefixLift 739524
  have htrace : WordTrace (prefixWord ++ tailWord_739524) baseStart_739524 baseEnd_739524 := by
    simpa [prefixWord, tailWord_739524, baseEnd_739524] using wordTrace_append hprefix tailTrace_739524
  have hstable : (prefixWord ++ tailWord_739524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739524).length < 2 ^ (prefixWord ++ tailWord_739524).sum := by decide
  have hdescent : baseEnd_739524 < baseStart_739524 := by decide
  rcases family_descends (prefixWord ++ tailWord_739524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739535 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 4]
def baseStart_739535 : Nat := 118140960795 + 739535 * 2 ^ 59
def prefixEnd_739535 : Nat := 4983230072969 + 3 ^ 40 * 739535 * 2
def baseEnd_739535 : Nat := 337543925175883821876841

theorem tailTrace_739535 : CollatzResearch.WordTrace tailWord_739535 prefixEnd_739535 337543925175883821876841 := by
  unfold tailWord_739535
  simp only [CollatzResearch.WordTrace]
  refine ⟨26973057375798472367652059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17982038250532314911768039 26973057375798472367652059)
  ·
    refine ⟨40459586063697708551478089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26973057375798472367652059 40459586063697708551478089)
    ·
      refine ⟨30344689547773281413608567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40459586063697708551478089 30344689547773281413608567)
      ·
        refine ⟨45517034321659922120412851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30344689547773281413608567 45517034321659922120412851)
        ·
          refine ⟨68275551482489883180619277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45517034321659922120412851 68275551482489883180619277)
          ·
            refine ⟨25603331805933706192732229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68275551482489883180619277 25603331805933706192732229)
            ·
              refine ⟨4800624713612569911137293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25603331805933706192732229 4800624713612569911137293)
              ·
                refine ⟨1800234267604713716676485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4800624713612569911137293 1800234267604713716676485)
                ·
                  refine ⟨337543925175883821876841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800234267604713716676485 337543925175883821876841)
                  ·
                    rfl

theorem cell20_739535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4].length) (baseStart_739535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739535 prefixEnd_739535 := by exact prefixLift 739535
  have htrace : WordTrace (prefixWord ++ tailWord_739535) baseStart_739535 baseEnd_739535 := by
    simpa [prefixWord, tailWord_739535, baseEnd_739535] using wordTrace_append hprefix tailTrace_739535
  have hstable : (prefixWord ++ tailWord_739535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739535).length < 2 ^ (prefixWord ++ tailWord_739535).sum := by decide
  have hdescent : baseEnd_739535 < baseStart_739535 := by decide
  rcases family_descends (prefixWord ++ tailWord_739535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739538 : List Nat := [3, 2, 2, 2, 1, 4, 1, 5]
def baseStart_739538 : Nat := 118140960795 + 739538 * 2 ^ 59
def prefixEnd_739538 : Nat := 4983230072969 + 3 ^ 40 * 739538 * 2
def baseEnd_739538 : Nat := 112515098152543048258943

theorem tailTrace_739538 : CollatzResearch.WordTrace tailWord_739538 prefixEnd_739538 112515098152543048258943 := by
  unfold tailWord_739538
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743291698696900970002817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17982111196525069253340845 6743291698696900970002817)
  ·
    refine ⟨5057468774022675727502113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6743291698696900970002817 5057468774022675727502113)
    ·
      refine ⟨3793101580517006795626585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5057468774022675727502113 3793101580517006795626585)
      ·
        refine ⟨2844826185387755096719939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3793101580517006795626585 2844826185387755096719939)
        ·
          refine ⟨4267239278081632645079909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844826185387755096719939 4267239278081632645079909)
          ·
            refine ⟨800107364640306120952483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4267239278081632645079909 800107364640306120952483)
            ·
              refine ⟨1200161046960459181428725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800107364640306120952483 1200161046960459181428725)
              ·
                refine ⟨112515098152543048258943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1200161046960459181428725 112515098152543048258943)
                ·
                  rfl

theorem cell20_739538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_739538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739538 prefixEnd_739538 := by exact prefixLift 739538
  have htrace : WordTrace (prefixWord ++ tailWord_739538) baseStart_739538 baseEnd_739538 := by
    simpa [prefixWord, tailWord_739538, baseEnd_739538] using wordTrace_append hprefix tailTrace_739538
  have hstable : (prefixWord ++ tailWord_739538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739538).length < 2 ^ (prefixWord ++ tailWord_739538).sum := by decide
  have hdescent : baseEnd_739538 < baseStart_739538 := by decide
  rcases family_descends (prefixWord ++ tailWord_739538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739548 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_739548 : Nat := 118140960795 + 739548 * 2 ^ 59
def prefixEnd_739548 : Nat := 4983230072969 + 3 ^ 40 * 739548 * 2
def baseEnd_739548 : Nat := 337549858730113554443455

theorem tailTrace_739548 : CollatzResearch.WordTrace tailWord_739548 prefixEnd_739548 337549858730113554443455 := by
  unfold tailWord_739548
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486765762375687793937649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17982354349834250391916865 13486765762375687793937649)
  ·
    refine ⟨10115074321781765845453237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13486765762375687793937649 10115074321781765845453237)
    ·
      refine ⟨948288217667040548011241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10115074321781765845453237 948288217667040548011241)
      ·
        refine ⟨711216163250280411008431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948288217667040548011241 711216163250280411008431)
        ·
          refine ⟨1066824244875420616512647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711216163250280411008431 1066824244875420616512647)
          ·
            refine ⟨1600236367313130924768971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066824244875420616512647 1600236367313130924768971)
            ·
              refine ⟨2400354550969696387153457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1600236367313130924768971 2400354550969696387153457)
              ·
                refine ⟨1800265913227272290365093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400354550969696387153457 1800265913227272290365093)
                ·
                  refine ⟨337549858730113554443455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800265913227272290365093 337549858730113554443455)
                  ·
                    rfl

theorem cell20_739548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_739548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739548 prefixEnd_739548 := by exact prefixLift 739548
  have htrace : WordTrace (prefixWord ++ tailWord_739548) baseStart_739548 baseEnd_739548 := by
    simpa [prefixWord, tailWord_739548, baseEnd_739548] using wordTrace_append hprefix tailTrace_739548
  have hstable : (prefixWord ++ tailWord_739548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739548).length < 2 ^ (prefixWord ++ tailWord_739548).sum := by decide
  have hdescent : baseEnd_739548 < baseStart_739548 := by decide
  rcases family_descends (prefixWord ++ tailWord_739548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739555 : List Nat := [1, 1, 1, 8, 1, 1, 3, 4]
def baseStart_739555 : Nat := 118140960795 + 739555 * 2 ^ 59
def prefixEnd_739555 : Nat := 4983230072969 + 3 ^ 40 * 739555 * 2
def baseEnd_739555 : Nat := 112517684573617547070031

theorem tailTrace_739555 : CollatzResearch.WordTrace tailWord_739555 prefixEnd_739555 112517684573617547070031 := by
  unfold tailWord_739555
  simp only [CollatzResearch.WordTrace]
  refine ⟨26973786835726015783380119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17982524557150677188920079 26973786835726015783380119)
  ·
    refine ⟨40460680253589023675070179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26973786835726015783380119 40460680253589023675070179)
    ·
      refine ⟨60691020380383535512605269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40460680253589023675070179 60691020380383535512605269)
      ·
        refine ⟨711222895082619556788343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 60691020380383535512605269 711222895082619556788343)
        ·
          refine ⟨1066834342623929335182515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711222895082619556788343 1066834342623929335182515)
          ·
            refine ⟨1600251513935894002773773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066834342623929335182515 1600251513935894002773773)
            ·
              refine ⟨600094317725960251040165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1600251513935894002773773 600094317725960251040165)
              ·
                refine ⟨112517684573617547070031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600094317725960251040165 112517684573617547070031)
                ·
                  rfl

theorem cell20_739555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 4].length) (baseStart_739555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739555 prefixEnd_739555 := by exact prefixLift 739555
  have htrace : WordTrace (prefixWord ++ tailWord_739555) baseStart_739555 baseEnd_739555 := by
    simpa [prefixWord, tailWord_739555, baseEnd_739555] using wordTrace_append hprefix tailTrace_739555
  have hstable : (prefixWord ++ tailWord_739555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739555).length < 2 ^ (prefixWord ++ tailWord_739555).sum := by decide
  have hdescent : baseEnd_739555 < baseStart_739555 := by decide
  rcases family_descends (prefixWord ++ tailWord_739555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739566 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_739566 : Nat := 118140960795 + 739566 * 2 ^ 59
def prefixEnd_739566 : Nat := 4983230072969 + 3 ^ 40 * 739566 * 2
def baseEnd_739566 : Nat := 337558074420585491843381

theorem tailTrace_739566 : CollatzResearch.WordTrace tailWord_739566 prefixEnd_739566 337558074420585491843381 := by
  unfold tailWord_739566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3371773504835770582753819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17982792025790776441353701 3371773504835770582753819)
  ·
    refine ⟨5057660257253655874130729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3371773504835770582753819 5057660257253655874130729)
    ·
      refine ⟨3793245192940241905598047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5057660257253655874130729 3793245192940241905598047)
      ·
        refine ⟨5689867789410362858397071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793245192940241905598047 5689867789410362858397071)
        ·
          refine ⟨8534801684115544287595607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5689867789410362858397071 8534801684115544287595607)
          ·
            refine ⟨12802202526173316431393411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8534801684115544287595607 12802202526173316431393411)
            ·
              refine ⟨19203303789259974647090117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12802202526173316431393411 19203303789259974647090117)
              ·
                refine ⟨3600619460486245246329397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19203303789259974647090117 3600619460486245246329397)
                ·
                  refine ⟨337558074420585491843381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3600619460486245246329397 337558074420585491843381)
                  ·
                    rfl

theorem cell20_739566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_739566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739566 prefixEnd_739566 := by exact prefixLift 739566
  have htrace : WordTrace (prefixWord ++ tailWord_739566) baseStart_739566 baseEnd_739566 := by
    simpa [prefixWord, tailWord_739566, baseEnd_739566] using wordTrace_append hprefix tailTrace_739566
  have hstable : (prefixWord ++ tailWord_739566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739566).length < 2 ^ (prefixWord ++ tailWord_739566).sum := by decide
  have hdescent : baseEnd_739566 < baseStart_739566 := by decide
  rcases family_descends (prefixWord ++ tailWord_739566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739586 : List Nat := [3, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_739586 : Nat := 118140960795 + 739586 * 2 ^ 59
def prefixEnd_739586 : Nat := 4983230072969 + 3 ^ 40 * 739586 * 2
def baseEnd_739586 : Nat := 337567202965554311176633

theorem tailTrace_739586 : CollatzResearch.WordTrace tailWord_739586 prefixEnd_739586 337567202965554311176633 := by
  unfold tailWord_739586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6743729374653427019439653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17983278332409138718505741 6743729374653427019439653)
  ·
    refine ⟨1264449257747517566144935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6743729374653427019439653 1264449257747517566144935)
    ·
      refine ⟨1896673886621276349217403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1264449257747517566144935 1896673886621276349217403)
      ·
        refine ⟨2845010829931914523826105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896673886621276349217403 2845010829931914523826105)
        ·
          refine ⟨2133758122448935892869579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2845010829931914523826105 2133758122448935892869579)
          ·
            refine ⟨3200637183673403839304369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133758122448935892869579 3200637183673403839304369)
            ·
              refine ⟨2400477887755052879478277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3200637183673403839304369 2400477887755052879478277)
              ·
                refine ⟨450089603954072414902177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2400477887755052879478277 450089603954072414902177)
                ·
                  refine ⟨337567202965554311176633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450089603954072414902177 337567202965554311176633)
                  ·
                    rfl

theorem cell20_739586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_739586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739586 prefixEnd_739586 := by exact prefixLift 739586
  have htrace : WordTrace (prefixWord ++ tailWord_739586) baseStart_739586 baseEnd_739586 := by
    simpa [prefixWord, tailWord_739586, baseEnd_739586] using wordTrace_append hprefix tailTrace_739586
  have hstable : (prefixWord ++ tailWord_739586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739586).length < 2 ^ (prefixWord ++ tailWord_739586).sum := by decide
  have hdescent : baseEnd_739586 < baseStart_739586 := by decide
  rcases family_descends (prefixWord ++ tailWord_739586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739611 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 4]
def baseStart_739611 : Nat := 118140960795 + 739611 * 2 ^ 59
def prefixEnd_739611 : Nat := 4983230072969 + 3 ^ 40 * 739611 * 2
def baseEnd_739611 : Nat := 337578613646765335343197

theorem tailTrace_739611 : CollatzResearch.WordTrace tailWord_739611 prefixEnd_739611 337578613646765335343197 := by
  unfold tailWord_739611
  simp only [CollatzResearch.WordTrace]
  refine ⟨26975829323523137347418687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17983886215682091564945791 26975829323523137347418687)
  ·
    refine ⟨40463743985284706021128031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26975829323523137347418687 40463743985284706021128031)
    ·
      refine ⟨60695615977927059031692047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40463743985284706021128031 60695615977927059031692047)
      ·
        refine ⟨91043423966890588547538071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60695615977927059031692047 91043423966890588547538071)
        ·
          refine ⟨136565135950335882821307107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91043423966890588547538071 136565135950335882821307107)
          ·
            refine ⟨204847703925503824231960661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136565135950335882821307107 204847703925503824231960661)
            ·
              refine ⟨2400559030376997940218289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 204847703925503824231960661 2400559030376997940218289)
              ·
                refine ⟨1800419272782748455163717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400559030376997940218289 1800419272782748455163717)
                ·
                  refine ⟨337578613646765335343197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800419272782748455163717 337578613646765335343197)
                  ·
                    rfl

theorem cell20_739611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_739611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739611 prefixEnd_739611 := by exact prefixLift 739611
  have htrace : WordTrace (prefixWord ++ tailWord_739611) baseStart_739611 baseEnd_739611 := by
    simpa [prefixWord, tailWord_739611, baseEnd_739611] using wordTrace_append hprefix tailTrace_739611
  have hstable : (prefixWord ++ tailWord_739611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739611).length < 2 ^ (prefixWord ++ tailWord_739611).sum := by decide
  have hdescent : baseEnd_739611 < baseStart_739611 := by decide
  rcases family_descends (prefixWord ++ tailWord_739611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739642 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_739642 : Nat := 118140960795 + 739642 * 2 ^ 59
def prefixEnd_739642 : Nat := 4983230072969 + 3 ^ 40 * 739642 * 2
def baseEnd_739642 : Nat := 337592762891467005309737

theorem tailTrace_739642 : CollatzResearch.WordTrace tailWord_739642 prefixEnd_739642 337592762891467005309737 := by
  unfold tailWord_739642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6744239996602707410449295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17984639990940553094531453 6744239996602707410449295)
  ·
    refine ⟨10116359994904061115673943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6744239996602707410449295 10116359994904061115673943)
    ·
      refine ⟨15174539992356091673510915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10116359994904061115673943 15174539992356091673510915)
      ·
        refine ⟨22761809988534137510266373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15174539992356091673510915 22761809988534137510266373)
        ·
          refine ⟨4267839372850150783174945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22761809988534137510266373 4267839372850150783174945)
          ·
            refine ⟨3200879529637613087381209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267839372850150783174945 3200879529637613087381209)
            ·
              refine ⟨2400659647228209815535907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3200879529637613087381209 2400659647228209815535907)
              ·
                refine ⟨3600989470842314723303861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400659647228209815535907 3600989470842314723303861)
                ·
                  refine ⟨337592762891467005309737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3600989470842314723303861 337592762891467005309737)
                  ·
                    rfl

theorem cell20_739642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_739642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739642 prefixEnd_739642 := by exact prefixLift 739642
  have htrace : WordTrace (prefixWord ++ tailWord_739642) baseStart_739642 baseEnd_739642 := by
    simpa [prefixWord, tailWord_739642, baseEnd_739642] using wordTrace_append hprefix tailTrace_739642
  have hstable : (prefixWord ++ tailWord_739642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739642).length < 2 ^ (prefixWord ++ tailWord_739642).sum := by decide
  have hdescent : baseEnd_739642 < baseStart_739642 := by decide
  rcases family_descends (prefixWord ++ tailWord_739642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739656 : List Nat := [2, 1, 3, 1, 1, 2, 3, 7]
def baseStart_739656 : Nat := 118140960795 + 739656 * 2 ^ 59
def prefixEnd_739656 : Nat := 4983230072969 + 3 ^ 40 * 739656 * 2
def baseEnd_739656 : Nat := 112533050957648392947671

theorem tailTrace_739656 : CollatzResearch.WordTrace tailWord_739656 prefixEnd_739656 112533050957648392947671 := by
  unfold tailWord_739656
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488735304180055016403411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17984980405573406688537881 13488735304180055016403411)
  ·
    refine ⟨20233102956270082524605117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13488735304180055016403411 20233102956270082524605117)
    ·
      refine ⟨7587413608601280946726919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20233102956270082524605117 7587413608601280946726919)
      ·
        refine ⟨11381120412901921420090379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7587413608601280946726919 11381120412901921420090379)
        ·
          refine ⟨17071680619352882130135569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11381120412901921420090379 17071680619352882130135569)
          ·
            refine ⟨12803760464514661597601677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17071680619352882130135569 12803760464514661597601677)
            ·
              refine ⟨4801410174192998099100629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12803760464514661597601677 4801410174192998099100629)
              ·
                refine ⟨112533050957648392947671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4801410174192998099100629 112533050957648392947671)
                ·
                  rfl

theorem cell20_739656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_739656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739656 prefixEnd_739656 := by exact prefixLift 739656
  have htrace : WordTrace (prefixWord ++ tailWord_739656) baseStart_739656 baseEnd_739656 := by
    simpa [prefixWord, tailWord_739656, baseEnd_739656] using wordTrace_append hprefix tailTrace_739656
  have hstable : (prefixWord ++ tailWord_739656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739656).length < 2 ^ (prefixWord ++ tailWord_739656).sum := by decide
  have hdescent : baseEnd_739656 < baseStart_739656 := by decide
  rcases family_descends (prefixWord ++ tailWord_739656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739663 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_739663 : Nat := 118140960795 + 739663 * 2 ^ 59
def prefixEnd_739663 : Nat := 4983230072969 + 3 ^ 40 * 739663 * 2
def baseEnd_739663 : Nat := 337602347863684265609651

theorem tailTrace_739663 : CollatzResearch.WordTrace tailWord_739663 prefixEnd_739663 337602347863684265609651 := by
  unfold tailWord_739663
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977725919334750228311643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17985150612889833485541095 26977725919334750228311643)
  ·
    refine ⟨40466588879002125342467465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26977725919334750228311643 40466588879002125342467465)
    ·
      refine ⟨30349941659251594006850599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40466588879002125342467465 30349941659251594006850599)
      ·
        refine ⟨45524912488877391010275899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30349941659251594006850599 45524912488877391010275899)
        ·
          refine ⟨68287368733316086515413849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45524912488877391010275899 68287368733316086515413849)
          ·
            refine ⟨51215526549987064886560387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68287368733316086515413849 51215526549987064886560387)
            ·
              refine ⟨76823289824980597329840581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51215526549987064886560387 76823289824980597329840581)
              ·
                refine ⟨14404366842183861999345109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76823289824980597329840581 14404366842183861999345109)
                ·
                  refine ⟨337602347863684265609651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14404366842183861999345109 337602347863684265609651)
                  ·
                    rfl

theorem cell20_739663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_739663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739663 prefixEnd_739663 := by exact prefixLift 739663
  have htrace : WordTrace (prefixWord ++ tailWord_739663) baseStart_739663 baseEnd_739663 := by
    simpa [prefixWord, tailWord_739663, baseEnd_739663] using wordTrace_append hprefix tailTrace_739663
  have hstable : (prefixWord ++ tailWord_739663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739663).length < 2 ^ (prefixWord ++ tailWord_739663).sum := by decide
  have hdescent : baseEnd_739663 < baseStart_739663 := by decide
  rcases family_descends (prefixWord ++ tailWord_739663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739694 : List Nat := [4, 1, 2, 13]
def baseStart_739694 : Nat := 118140960795 + 739694 * 2 ^ 59
def prefixEnd_739694 : Nat := 4983230072969 + 3 ^ 40 * 739694 * 2
def baseEnd_739694 : Nat := 1389368300857555290437

theorem tailTrace_739694 : CollatzResearch.WordTrace tailWord_739694 prefixEnd_739694 1389368300857555290437 := by
  unfold tailWord_739694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3372357072777805315336267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17985904388148295015126757 3372357072777805315336267)
  ·
    refine ⟨5058535609166707973004401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3372357072777805315336267 5058535609166707973004401)
    ·
      refine ⟨3793901706875030979753301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5058535609166707973004401 3793901706875030979753301)
      ·
        refine ⟨1389368300857555290437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3793901706875030979753301 1389368300857555290437)
        ·
          rfl

theorem cell20_739694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 13].length) (baseStart_739694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739694 prefixEnd_739694 := by exact prefixLift 739694
  have htrace : WordTrace (prefixWord ++ tailWord_739694) baseStart_739694 baseEnd_739694 := by
    simpa [prefixWord, tailWord_739694, baseEnd_739694] using wordTrace_append hprefix tailTrace_739694
  have hstable : (prefixWord ++ tailWord_739694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739694).length < 2 ^ (prefixWord ++ tailWord_739694).sum := by decide
  have hdescent : baseEnd_739694 < baseStart_739694 := by decide
  rcases family_descends (prefixWord ++ tailWord_739694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739752 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_739752 : Nat := 118140960795 + 739752 * 2 ^ 59
def prefixEnd_739752 : Nat := 4983230072969 + 3 ^ 40 * 739752 * 2
def baseEnd_739752 : Nat := 337642969888795511642621

theorem tailTrace_739752 : CollatzResearch.WordTrace tailWord_739752 prefixEnd_739752 337642969888795511642621 := by
  unfold tailWord_739752
  simp only [CollatzResearch.WordTrace]
  refine ⟨13490486008006159214150755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17987314677341545618867673 13490486008006159214150755)
  ·
    refine ⟨20235729012009238821226133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13490486008006159214150755 20235729012009238821226133)
    ·
      refine ⟨948549797437933069744975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20235729012009238821226133 948549797437933069744975)
      ·
        refine ⟨1422824696156899604617463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 948549797437933069744975 1422824696156899604617463)
        ·
          refine ⟨2134237044235349406926195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1422824696156899604617463 2134237044235349406926195)
          ·
            refine ⟨3201355566353024110389293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134237044235349406926195 3201355566353024110389293)
            ·
              refine ⟨1200508337382384041395985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201355566353024110389293 1200508337382384041395985)
              ·
                refine ⟨900381253036788031046989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200508337382384041395985 900381253036788031046989)
                ·
                  refine ⟨337642969888795511642621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900381253036788031046989 337642969888795511642621)
                  ·
                    rfl

theorem cell20_739752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_739752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739752 prefixEnd_739752 := by exact prefixLift 739752
  have htrace : WordTrace (prefixWord ++ tailWord_739752) baseStart_739752 baseEnd_739752 := by
    simpa [prefixWord, tailWord_739752, baseEnd_739752] using wordTrace_append hprefix tailTrace_739752
  have hstable : (prefixWord ++ tailWord_739752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739752).length < 2 ^ (prefixWord ++ tailWord_739752).sum := by decide
  have hdescent : baseEnd_739752 < baseStart_739752 := by decide
  rcases family_descends (prefixWord ++ tailWord_739752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739797 : List Nat := [1, 3, 2, 3, 1, 2, 3, 3, 2]
def baseStart_739797 : Nat := 118140960795 + 739797 * 2 ^ 59
def prefixEnd_739797 : Nat := 4983230072969 + 3 ^ 40 * 739797 * 2
def baseEnd_739797 : Nat := 337663509114975355142437

theorem tailTrace_739797 : CollatzResearch.WordTrace tailWord_739797 prefixEnd_739797 337663509114975355142437 := by
  unfold tailWord_739797
  simp only [CollatzResearch.WordTrace]
  refine ⟨26982613300849291113689645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17988408867232860742459763 26982613300849291113689645)
  ·
    refine ⟨10118479987818484167633617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26982613300849291113689645 10118479987818484167633617)
    ·
      refine ⟨7588859990863863125725213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10118479987818484167633617 7588859990863863125725213)
      ·
        refine ⟨2845822496573948672146955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7588859990863863125725213 2845822496573948672146955)
        ·
          refine ⟨4268733744860923008220433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845822496573948672146955 4268733744860923008220433)
          ·
            refine ⟨3201550308645692256165325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268733744860923008220433 3201550308645692256165325)
            ·
              refine ⟨1200581365742134596061997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201550308645692256165325 1200581365742134596061997)
              ·
                refine ⟨450218012153300473523249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1200581365742134596061997 450218012153300473523249)
                ·
                  refine ⟨337663509114975355142437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450218012153300473523249 337663509114975355142437)
                  ·
                    rfl

theorem cell20_739797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_739797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739797 prefixEnd_739797 := by exact prefixLift 739797
  have htrace : WordTrace (prefixWord ++ tailWord_739797) baseStart_739797 baseEnd_739797 := by
    simpa [prefixWord, tailWord_739797, baseEnd_739797] using wordTrace_append hprefix tailTrace_739797
  have hstable : (prefixWord ++ tailWord_739797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739797).length < 2 ^ (prefixWord ++ tailWord_739797).sum := by decide
  have hdescent : baseEnd_739797 < baseStart_739797 := by decide
  rcases family_descends (prefixWord ++ tailWord_739797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739810 : List Nat := [3, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_739810 : Nat := 118140960795 + 739810 * 2 ^ 59
def prefixEnd_739810 : Nat := 4983230072969 + 3 ^ 40 * 739810 * 2
def baseEnd_739810 : Nat := 337669442669205087709051

theorem tailTrace_739810 : CollatzResearch.WordTrace tailWord_739810 prefixEnd_739810 337669442669205087709051 := by
  unfold tailWord_739810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745771862450548583478221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17988724966534796222608589 6745771862450548583478221)
  ·
    refine ⟨2529664448418955718804333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6745771862450548583478221 2529664448418955718804333)
    ·
      refine ⟨948624168157108394551625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2529664448418955718804333 948624168157108394551625)
      ·
        refine ⟨711468126117831295913719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 948624168157108394551625 711468126117831295913719)
        ·
          refine ⟨1067202189176746943870579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711468126117831295913719 1067202189176746943870579)
          ·
            refine ⟨1600803283765120415805869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067202189176746943870579 1600803283765120415805869)
            ·
              refine ⟨600301231411920155927201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1600803283765120415805869 600301231411920155927201)
              ·
                refine ⟨450225923558940116945401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600301231411920155927201 450225923558940116945401)
                ·
                  refine ⟨337669442669205087709051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450225923558940116945401 337669442669205087709051)
                  ·
                    rfl

theorem cell20_739810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_739810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739810 prefixEnd_739810 := by exact prefixLift 739810
  have htrace : WordTrace (prefixWord ++ tailWord_739810) baseStart_739810 baseEnd_739810 := by
    simpa [prefixWord, tailWord_739810, baseEnd_739810] using wordTrace_append hprefix tailTrace_739810
  have hstable : (prefixWord ++ tailWord_739810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739810).length < 2 ^ (prefixWord ++ tailWord_739810).sum := by decide
  have hdescent : baseEnd_739810 < baseStart_739810 := by decide
  rcases family_descends (prefixWord ++ tailWord_739810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739818 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_739818 : Nat := 118140960795 + 739818 * 2 ^ 59
def prefixEnd_739818 : Nat := 4983230072969 + 3 ^ 40 * 739818 * 2
def baseEnd_739818 : Nat := 337673094087192615442351

theorem tailTrace_739818 : CollatzResearch.WordTrace tailWord_739818 prefixEnd_739818 337673094087192615442351 := by
  unfold tailWord_739818
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745844808443302925051027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17988919489182141133469405 6745844808443302925051027)
  ·
    refine ⟨10118767212664954387576541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6745844808443302925051027 10118767212664954387576541)
    ·
      refine ⟨3794537704749357895341203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10118767212664954387576541 3794537704749357895341203)
      ·
        refine ⟨5691806557124036843011805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794537704749357895341203 5691806557124036843011805)
        ·
          refine ⟨2134427458921513816129427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5691806557124036843011805 2134427458921513816129427)
          ·
            refine ⟨3201641188382270724194141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134427458921513816129427 3201641188382270724194141)
            ·
              refine ⟨1200615445643351521572803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3201641188382270724194141 1200615445643351521572803)
              ·
                refine ⟨1800923168465027282359205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1200615445643351521572803 1800923168465027282359205)
                ·
                  refine ⟨337673094087192615442351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1800923168465027282359205 337673094087192615442351)
                  ·
                    rfl

theorem cell20_739818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_739818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739818 prefixEnd_739818 := by exact prefixLift 739818
  have htrace : WordTrace (prefixWord ++ tailWord_739818) baseStart_739818 baseEnd_739818 := by
    simpa [prefixWord, tailWord_739818, baseEnd_739818] using wordTrace_append hprefix tailTrace_739818
  have hstable : (prefixWord ++ tailWord_739818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739818).length < 2 ^ (prefixWord ++ tailWord_739818).sum := by decide
  have hdescent : baseEnd_739818 < baseStart_739818 := by decide
  rcases family_descends (prefixWord ++ tailWord_739818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739832 : List Nat := [2, 1, 2, 1, 1, 4, 3, 3, 3]
def baseStart_739832 : Nat := 118140960795 + 739832 * 2 ^ 59
def prefixEnd_739832 : Nat := 4983230072969 + 3 ^ 40 * 739832 * 2
def baseEnd_739832 : Nat := 337679484068670788975627

theorem tailTrace_739832 : CollatzResearch.WordTrace tailWord_739832 prefixEnd_739832 337679484068670788975627 := by
  unfold tailWord_739832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13491944927861246045606875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17989259903814994727475833 13491944927861246045606875)
  ·
    refine ⟨20237917391791869068410313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13491944927861246045606875 20237917391791869068410313)
    ·
      refine ⟨15178438043843901801307735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20237917391791869068410313 15178438043843901801307735)
      ·
        refine ⟨22767657065765852701961603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15178438043843901801307735 22767657065765852701961603)
        ·
          refine ⟨34151485598648779052942405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22767657065765852701961603 34151485598648779052942405)
          ·
            refine ⟨6403403549746646072426701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34151485598648779052942405 6403403549746646072426701)
            ·
              refine ⟨2401276331154992277160013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6403403549746646072426701 2401276331154992277160013)
              ·
                refine ⟨900478624183122103935005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2401276331154992277160013 900478624183122103935005)
                ·
                  refine ⟨337679484068670788975627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900478624183122103935005 337679484068670788975627)
                  ·
                    rfl

theorem cell20_739832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_739832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739832 prefixEnd_739832 := by exact prefixLift 739832
  have htrace : WordTrace (prefixWord ++ tailWord_739832) baseStart_739832 baseEnd_739832 := by
    simpa [prefixWord, tailWord_739832, baseEnd_739832] using wordTrace_append hprefix tailTrace_739832
  have hstable : (prefixWord ++ tailWord_739832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739832).length < 2 ^ (prefixWord ++ tailWord_739832).sum := by decide
  have hdescent : baseEnd_739832 < baseStart_739832 := by decide
  rcases family_descends (prefixWord ++ tailWord_739832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739863 : List Nat := [1, 1, 3, 6, 1, 8]
def baseStart_739863 : Nat := 118140960795 + 739863 * 2 ^ 59
def prefixEnd_739863 : Nat := 4983230072969 + 3 ^ 40 * 739863 * 2
def baseEnd_739863 : Nat := 12507171604198979960821

theorem tailTrace_739863 : CollatzResearch.WordTrace tailWord_739863 prefixEnd_739863 12507171604198979960821 := by
  unfold tailWord_739863
  simp only [CollatzResearch.WordTrace]
  refine ⟨26985020518610184385592243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17990013679073456257061495 26985020518610184385592243)
  ·
    refine ⟨40477530777915276578388365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26985020518610184385592243 40477530777915276578388365)
    ·
      refine ⟨15179074041718228716895637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40477530777915276578388365 15179074041718228716895637)
      ·
        refine ⟨711519095705541971104483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15179074041718228716895637 711519095705541971104483)
        ·
          refine ⟨1067278643558312956656725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711519095705541971104483 1067278643558312956656725)
          ·
            refine ⟨12507171604198979960821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1067278643558312956656725 12507171604198979960821)
            ·
              rfl

theorem cell20_739863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 8].length) (baseStart_739863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739863 prefixEnd_739863 := by exact prefixLift 739863
  have htrace : WordTrace (prefixWord ++ tailWord_739863) baseStart_739863 baseEnd_739863 := by
    simpa [prefixWord, tailWord_739863, baseEnd_739863] using wordTrace_append hprefix tailTrace_739863
  have hstable : (prefixWord ++ tailWord_739863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739863).length < 2 ^ (prefixWord ++ tailWord_739863).sum := by decide
  have hdescent : baseEnd_739863 < baseStart_739863 := by decide
  rcases family_descends (prefixWord ++ tailWord_739863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739880 : List Nat := [2, 1, 5, 2, 1, 3, 1, 5]
def baseStart_739880 : Nat := 118140960795 + 739880 * 2 ^ 59
def prefixEnd_739880 : Nat := 4983230072969 + 3 ^ 40 * 739880 * 2
def baseEnd_739880 : Nat := 112567130858865318458477

theorem tailTrace_739880 : CollatzResearch.WordTrace tailWord_739880 prefixEnd_739880 112567130858865318458477 := by
  unfold tailWord_739880
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492820279774298144480547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17990427039699064192640729 13492820279774298144480547)
  ·
    refine ⟨20239230419661447216720821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13492820279774298144480547 20239230419661447216720821)
    ·
      refine ⟨1897427851843260676567577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20239230419661447216720821 1897427851843260676567577)
      ·
        refine ⟨1423070888882445507425683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1897427851843260676567577 1423070888882445507425683)
        ·
          refine ⟨2134606333323668261138525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423070888882445507425683 2134606333323668261138525)
          ·
            refine ⟨800477374996375597926947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2134606333323668261138525 800477374996375597926947)
            ·
              refine ⟨1200716062494563396890421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800477374996375597926947 1200716062494563396890421)
              ·
                refine ⟨112567130858865318458477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1200716062494563396890421 112567130858865318458477)
                ·
                  rfl

theorem cell20_739880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_739880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739880 prefixEnd_739880 := by exact prefixLift 739880
  have htrace : WordTrace (prefixWord ++ tailWord_739880) baseStart_739880 baseEnd_739880 := by
    simpa [prefixWord, tailWord_739880, baseEnd_739880] using wordTrace_append hprefix tailTrace_739880
  have hstable : (prefixWord ++ tailWord_739880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739880).length < 2 ^ (prefixWord ++ tailWord_739880).sum := by decide
  have hdescent : baseEnd_739880 < baseStart_739880 := by decide
  rcases family_descends (prefixWord ++ tailWord_739880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739894 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_739894 : Nat := 118140960795 + 739894 * 2 ^ 59
def prefixEnd_739894 : Nat := 4983230072969 + 3 ^ 40 * 739894 * 2
def baseEnd_739894 : Nat := 337707782558074128908707

theorem tailTrace_739894 : CollatzResearch.WordTrace tailWord_739894 prefixEnd_739894 337707782558074128908707 := by
  unfold tailWord_739894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1686634448843617292498171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17990767454331917786647157 1686634448843617292498171)
  ·
    refine ⟨2529951673265425938747257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1686634448843617292498171 2529951673265425938747257)
    ·
      refine ⟨1897463754949069454060443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2529951673265425938747257 1897463754949069454060443)
      ·
        refine ⟨2846195632423604181090665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897463754949069454060443 2846195632423604181090665)
        ·
          refine ⟨2134646724317703135817999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2846195632423604181090665 2134646724317703135817999)
          ·
            refine ⟨3201970086476554703726999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134646724317703135817999 3201970086476554703726999)
            ·
              refine ⟨4802955129714832055590499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201970086476554703726999 4802955129714832055590499)
              ·
                refine ⟨7204432694572248083385749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802955129714832055590499 7204432694572248083385749)
                ·
                  refine ⟨337707782558074128908707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7204432694572248083385749 337707782558074128908707)
                  ·
                    rfl

theorem cell20_739894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_739894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739894 prefixEnd_739894 := by exact prefixLift 739894
  have htrace : WordTrace (prefixWord ++ tailWord_739894) baseStart_739894 baseEnd_739894 := by
    simpa [prefixWord, tailWord_739894, baseEnd_739894] using wordTrace_append hprefix tailTrace_739894
  have hstable : (prefixWord ++ tailWord_739894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739894).length < 2 ^ (prefixWord ++ tailWord_739894).sum := by decide
  have hdescent : baseEnd_739894 < baseStart_739894 := by decide
  rcases family_descends (prefixWord ++ tailWord_739894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739911 : List Nat := [1, 1, 4, 1, 4, 2, 2, 3, 2]
def baseStart_739911 : Nat := 118140960795 + 739911 * 2 ^ 59
def prefixEnd_739911 : Nat := 4983230072969 + 3 ^ 40 * 739911 * 2
def baseEnd_739911 : Nat := 337715541821297625341971

theorem tailTrace_739911 : CollatzResearch.WordTrace tailWord_739911 prefixEnd_739911 337715541821297625341971 := by
  unfold tailWord_739911
  simp only [CollatzResearch.WordTrace]
  refine ⟨26986771222436288583339587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17991180814957525722226391 26986771222436288583339587)
  ·
    refine ⟨40480156833654432875009381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26986771222436288583339587 40480156833654432875009381)
    ·
      refine ⟨7590029406310206164064259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40480156833654432875009381 7590029406310206164064259)
      ·
        refine ⟨11385044109465309246096389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590029406310206164064259 11385044109465309246096389)
        ·
          refine ⟨2134695770524745483643073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11385044109465309246096389 2134695770524745483643073)
          ·
            refine ⟨1601021827893559112732305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2134695770524745483643073 1601021827893559112732305)
            ·
              refine ⟨1200766370920169334549229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601021827893559112732305 1200766370920169334549229)
              ·
                refine ⟨450287389095063500455961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1200766370920169334549229 450287389095063500455961)
                ·
                  refine ⟨337715541821297625341971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450287389095063500455961 337715541821297625341971)
                  ·
                    rfl

theorem cell20_739911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 3, 2].length) (baseStart_739911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739911 prefixEnd_739911 := by exact prefixLift 739911
  have htrace : WordTrace (prefixWord ++ tailWord_739911) baseStart_739911 baseEnd_739911 := by
    simpa [prefixWord, tailWord_739911, baseEnd_739911] using wordTrace_append hprefix tailTrace_739911
  have hstable : (prefixWord ++ tailWord_739911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739911).length < 2 ^ (prefixWord ++ tailWord_739911).sum := by decide
  have hdescent : baseEnd_739911 < baseStart_739911 := by decide
  rcases family_descends (prefixWord ++ tailWord_739911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739922 : List Nat := [3, 2, 2, 1, 2, 1, 9]
def baseStart_739922 : Nat := 118140960795 + 739922 * 2 ^ 59
def prefixEnd_739922 : Nat := 4983230072969 + 3 ^ 40 * 739922 * 2
def baseEnd_739922 : Nat := 37524506946781163997251

theorem tailTrace_739922 : CollatzResearch.WordTrace tailWord_739922 prefixEnd_739922 37524506946781163997251 := by
  unfold tailWord_739922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6746793106349109365497505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17991448283597624974660013 6746793106349109365497505)
  ·
    refine ⟨5060094829761832024123129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6746793106349109365497505 5060094829761832024123129)
    ·
      refine ⟨3795071122321374018092347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5060094829761832024123129 3795071122321374018092347)
      ·
        refine ⟨5692606683482061027138521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795071122321374018092347 5692606683482061027138521)
        ·
          refine ⟨4269455012611545770353891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5692606683482061027138521 4269455012611545770353891)
          ·
            refine ⟨6404182518917318655530837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269455012611545770353891 6404182518917318655530837)
            ·
              refine ⟨37524506946781163997251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6404182518917318655530837 37524506946781163997251)
              ·
                rfl

theorem cell20_739922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 9].length) (baseStart_739922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739922 prefixEnd_739922 := by exact prefixLift 739922
  have htrace : WordTrace (prefixWord ++ tailWord_739922) baseStart_739922 baseEnd_739922 := by
    simpa [prefixWord, tailWord_739922, baseEnd_739922] using wordTrace_append hprefix tailTrace_739922
  have hstable : (prefixWord ++ tailWord_739922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739922).length < 2 ^ (prefixWord ++ tailWord_739922).sum := by decide
  have hdescent : baseEnd_739922 < baseStart_739922 := by decide
  rcases family_descends (prefixWord ++ tailWord_739922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_739994 : List Nat := [3, 1, 1, 6, 1, 1, 2, 5]
def baseStart_739994 : Nat := 118140960795 + 739994 * 2 ^ 59
def prefixEnd_739994 : Nat := 4983230072969 + 3 ^ 40 * 739994 * 2
def baseEnd_739994 : Nat := 112584475094306075191655

theorem tailTrace_739994 : CollatzResearch.WordTrace tailWord_739994 prefixEnd_739994 112584475094306075191655 := by
  unfold tailWord_739994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747449620283898439652759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17993198987423729172407357 6747449620283898439652759)
  ·
    refine ⟨10121174430425847659479139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6747449620283898439652759 10121174430425847659479139)
    ·
      refine ⟨15181761645638771489218709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10121174430425847659479139 15181761645638771489218709)
      ·
        refine ⟨711645077139317413557127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15181761645638771489218709 711645077139317413557127)
        ·
          refine ⟨1067467615708976120335691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711645077139317413557127 1067467615708976120335691)
          ·
            refine ⟨1601201423563464180503537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067467615708976120335691 1601201423563464180503537)
            ·
              refine ⟨1200901067672598135377653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1601201423563464180503537 1200901067672598135377653)
              ·
                refine ⟨112584475094306075191655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1200901067672598135377653 112584475094306075191655)
                ·
                  rfl

theorem cell20_739994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_739994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_739994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_739994 prefixEnd_739994 := by exact prefixLift 739994
  have htrace : WordTrace (prefixWord ++ tailWord_739994) baseStart_739994 baseEnd_739994 := by
    simpa [prefixWord, tailWord_739994, baseEnd_739994] using wordTrace_append hprefix tailTrace_739994
  have hstable : (prefixWord ++ tailWord_739994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_739994).length < 2 ^ (prefixWord ++ tailWord_739994).sum := by decide
  have hdescent : baseEnd_739994 < baseStart_739994 := by decide
  rcases family_descends (prefixWord ++ tailWord_739994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740001 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 3]
def baseStart_740001 : Nat := 118140960795 + 740001 * 2 ^ 59
def prefixEnd_740001 : Nat := 4983230072969 + 3 ^ 40 * 740001 * 2
def baseEnd_740001 : Nat := 337756620273657312341603

theorem tailTrace_740001 : CollatzResearch.WordTrace tailWord_740001 prefixEnd_740001 337756620273657312341603 := by
  unfold tailWord_740001
  simp only [CollatzResearch.WordTrace]
  refine ⟨26990053792110233954115857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17993369194740155969410571 26990053792110233954115857)
  ·
    refine ⟨20242540344082675465586893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26990053792110233954115857 20242540344082675465586893)
    ·
      refine ⟨7590952629031003299595085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20242540344082675465586893 7590952629031003299595085)
      ·
        refine ⟨2846607235886626237348157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7590952629031003299595085 2846607235886626237348157)
        ·
          refine ⟨1067477713457484839005559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2846607235886626237348157 1067477713457484839005559)
          ·
            refine ⟨1601216570186227258508339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067477713457484839005559 1601216570186227258508339)
            ·
              refine ⟨2401824855279340887762509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601216570186227258508339 2401824855279340887762509)
              ·
                refine ⟨900684320729752832910941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2401824855279340887762509 900684320729752832910941)
                ·
                  refine ⟨337756620273657312341603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900684320729752832910941 337756620273657312341603)
                  ·
                    rfl

theorem cell20_740001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_740001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740001 prefixEnd_740001 := by exact prefixLift 740001
  have htrace : WordTrace (prefixWord ++ tailWord_740001) baseStart_740001 baseEnd_740001 := by
    simpa [prefixWord, tailWord_740001, baseEnd_740001] using wordTrace_append hprefix tailTrace_740001
  have hstable : (prefixWord ++ tailWord_740001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740001).length < 2 ^ (prefixWord ++ tailWord_740001).sum := by decide
  have hdescent : baseEnd_740001 < baseStart_740001 := by decide
  rcases family_descends (prefixWord ++ tailWord_740001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740036 : List Nat := [2, 3, 3, 1, 1, 10]
def baseStart_740036 : Nat := 118140960795 + 740036 * 2 ^ 59
def prefixEnd_740036 : Nat := 4983230072969 + 3 ^ 40 * 740036 * 2
def baseEnd_740036 : Nat := 12510096119531583191659

theorem tailTrace_740036 : CollatzResearch.WordTrace tailWord_740036 prefixEnd_740036 12510096119531583191659 := by
  unfold tailWord_740036
  simp only [CollatzResearch.WordTrace]
  refine ⟨13495665173491717465819981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17994220231322289954426641 13495665173491717465819981)
  ·
    refine ⟨5060874440059394049682493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13495665173491717465819981 5060874440059394049682493)
    ·
      refine ⟨1897827915022272768630935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5060874440059394049682493 1897827915022272768630935)
      ·
        refine ⟨2846741872533409152946403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897827915022272768630935 2846741872533409152946403)
        ·
          refine ⟨4270112808800113729419605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846741872533409152946403 4270112808800113729419605)
          ·
            refine ⟨12510096119531583191659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4270112808800113729419605 12510096119531583191659)
            ·
              rfl

theorem cell20_740036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 10].length) (baseStart_740036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740036 prefixEnd_740036 := by exact prefixLift 740036
  have htrace : WordTrace (prefixWord ++ tailWord_740036) baseStart_740036 baseEnd_740036 := by
    simpa [prefixWord, tailWord_740036, baseEnd_740036] using wordTrace_append hprefix tailTrace_740036
  have hstable : (prefixWord ++ tailWord_740036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740036).length < 2 ^ (prefixWord ++ tailWord_740036).sum := by decide
  have hdescent : baseEnd_740036 < baseStart_740036 := by decide
  rcases family_descends (prefixWord ++ tailWord_740036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740042 : List Nat := [3, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_740042 : Nat := 118140960795 + 740042 * 2 ^ 59
def prefixEnd_740042 : Nat := 4983230072969 + 3 ^ 40 * 740042 * 2
def baseEnd_740042 : Nat := 337775333790843391974769

theorem tailTrace_740042 : CollatzResearch.WordTrace tailWord_740042 prefixEnd_740042 337775333790843391974769 := by
  unfold tailWord_740042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6747887296240424489089595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17994366123307798637572253 6747887296240424489089595)
  ·
    refine ⟨10121830944360636733634393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6747887296240424489089595 10121830944360636733634393)
    ·
      refine ⟨7591373208270477550225795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10121830944360636733634393 7591373208270477550225795)
      ·
        refine ⟨11387059812405716325338693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7591373208270477550225795 11387059812405716325338693)
        ·
          refine ⟨2135073714826071811001005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11387059812405716325338693 2135073714826071811001005)
          ·
            refine ⟨800652643059776929125377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2135073714826071811001005 800652643059776929125377)
            ·
              refine ⟨600489482294832696844033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800652643059776929125377 600489482294832696844033)
              ·
                refine ⟨450367111721124522633025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 600489482294832696844033 450367111721124522633025)
                ·
                  refine ⟨337775333790843391974769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450367111721124522633025 337775333790843391974769)
                  ·
                    rfl

theorem cell20_740042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_740042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740042 prefixEnd_740042 := by exact prefixLift 740042
  have htrace : WordTrace (prefixWord ++ tailWord_740042) baseStart_740042 baseEnd_740042 := by
    simpa [prefixWord, tailWord_740042, baseEnd_740042] using wordTrace_append hprefix tailTrace_740042
  have hstable : (prefixWord ++ tailWord_740042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740042).length < 2 ^ (prefixWord ++ tailWord_740042).sum := by decide
  have hdescent : baseEnd_740042 < baseStart_740042 := by decide
  rcases family_descends (prefixWord ++ tailWord_740042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740067 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 6]
def baseStart_740067 : Nat := 118140960795 + 740067 * 2 ^ 59
def prefixEnd_740067 : Nat := 4983230072969 + 3 ^ 40 * 740067 * 2
def baseEnd_740067 : Nat := 337786744472054416141333

theorem tailTrace_740067 : CollatzResearch.WordTrace tailWord_740067 prefixEnd_740067 337786744472054416141333 := by
  unfold tailWord_740067
  simp only [CollatzResearch.WordTrace]
  refine ⟨26992461009871127226018455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17994974006580751484012303 26992461009871127226018455)
  ·
    refine ⟨40488691514806690839027683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26992461009871127226018455 40488691514806690839027683)
    ·
      refine ⟨60733037272210036258541525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40488691514806690839027683 60733037272210036258541525)
      ·
        refine ⟨1423430561067422724809567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 60733037272210036258541525 1423430561067422724809567)
        ·
          refine ⟨2135145841601134087214351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1423430561067422724809567 2135145841601134087214351)
          ·
            refine ⟨3202718762401701130821527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135145841601134087214351 3202718762401701130821527)
            ·
              refine ⟨4804078143602551696232291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202718762401701130821527 4804078143602551696232291)
              ·
                refine ⟨7206117215403827544348437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804078143602551696232291 7206117215403827544348437)
                ·
                  refine ⟨337786744472054416141333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7206117215403827544348437 337786744472054416141333)
                  ·
                    rfl

theorem cell20_740067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 6].length) (baseStart_740067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740067 prefixEnd_740067 := by exact prefixLift 740067
  have htrace : WordTrace (prefixWord ++ tailWord_740067) baseStart_740067 baseEnd_740067 := by
    simpa [prefixWord, tailWord_740067, baseEnd_740067] using wordTrace_append hprefix tailTrace_740067
  have hstable : (prefixWord ++ tailWord_740067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740067).length < 2 ^ (prefixWord ++ tailWord_740067).sum := by decide
  have hdescent : baseEnd_740067 < baseStart_740067 := by decide
  rcases family_descends (prefixWord ++ tailWord_740067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740081 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 5]
def baseStart_740081 : Nat := 118140960795 + 740081 * 2 ^ 59
def prefixEnd_740081 : Nat := 4983230072969 + 3 ^ 40 * 740081 * 2
def baseEnd_740081 : Nat := 337793134453532589674609

theorem tailTrace_740081 : CollatzResearch.WordTrace tailWord_740081 prefixEnd_740081 337793134453532589674609 := by
  unfold tailWord_740081
  simp only [CollatzResearch.WordTrace]
  refine ⟨26992971631820407617028097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17995314421213605078018731 26992971631820407617028097)
  ·
    refine ⟨20244728723865305712771073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26992971631820407617028097 20244728723865305712771073)
    ·
      refine ⟨15183546542898979284578305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20244728723865305712771073 15183546542898979284578305)
      ·
        refine ⟨11387659907174234463433729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15183546542898979284578305 11387659907174234463433729)
        ·
          refine ⟨8540744930380675847575297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11387659907174234463433729 8540744930380675847575297)
          ·
            refine ⟨6405558697785506885681473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8540744930380675847575297 6405558697785506885681473)
            ·
              refine ⟨4804169023339130164261105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6405558697785506885681473 4804169023339130164261105)
              ·
                refine ⟨3603126767504347623195829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4804169023339130164261105 3603126767504347623195829)
                ·
                  refine ⟨337793134453532589674609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3603126767504347623195829 337793134453532589674609)
                  ·
                    rfl

theorem cell20_740081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_740081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740081 prefixEnd_740081 := by exact prefixLift 740081
  have htrace : WordTrace (prefixWord ++ tailWord_740081) baseStart_740081 baseEnd_740081 := by
    simpa [prefixWord, tailWord_740081, baseEnd_740081] using wordTrace_append hprefix tailTrace_740081
  have hstable : (prefixWord ++ tailWord_740081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740081).length < 2 ^ (prefixWord ++ tailWord_740081).sum := by decide
  have hdescent : baseEnd_740081 < baseStart_740081 := by decide
  rcases family_descends (prefixWord ++ tailWord_740081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740088 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_740088 : Nat := 118140960795 + 740088 * 2 ^ 59
def prefixEnd_740088 : Nat := 4983230072969 + 3 ^ 40 * 740088 * 2
def baseEnd_740088 : Nat := 337796329444271676441247

theorem tailTrace_740088 : CollatzResearch.WordTrace tailWord_740088 prefixEnd_740088 337796329444271676441247 := by
  unfold tailWord_740088
  simp only [CollatzResearch.WordTrace]
  refine ⟨13496613471397523906266459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17995484628530031875021945 13496613471397523906266459)
  ·
    refine ⟨20244920207096285859399689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13496613471397523906266459 20244920207096285859399689)
    ·
      refine ⟨15183690155322214394549767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20244920207096285859399689 15183690155322214394549767)
      ·
        refine ⟨22775535232983321591824651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15183690155322214394549767 22775535232983321591824651)
        ·
          refine ⟨34163302849474982387736977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22775535232983321591824651 34163302849474982387736977)
          ·
            refine ⟨25622477137106236790802733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34163302849474982387736977 25622477137106236790802733)
            ·
              refine ⟨9608428926414838796551025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25622477137106236790802733 9608428926414838796551025)
              ·
                refine ⟨7206321694811129097413269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9608428926414838796551025 7206321694811129097413269)
                ·
                  refine ⟨337796329444271676441247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7206321694811129097413269 337796329444271676441247)
                  ·
                    rfl

theorem cell20_740088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_740088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740088 prefixEnd_740088 := by exact prefixLift 740088
  have htrace : WordTrace (prefixWord ++ tailWord_740088) baseStart_740088 baseEnd_740088 := by
    simpa [prefixWord, tailWord_740088, baseEnd_740088] using wordTrace_append hprefix tailTrace_740088
  have hstable : (prefixWord ++ tailWord_740088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740088).length < 2 ^ (prefixWord ++ tailWord_740088).sum := by decide
  have hdescent : baseEnd_740088 < baseStart_740088 := by decide
  rcases family_descends (prefixWord ++ tailWord_740088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740094 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_740094 : Nat := 118140960795 + 740094 * 2 ^ 59
def prefixEnd_740094 : Nat := 4983230072969 + 3 ^ 40 * 740094 * 2
def baseEnd_740094 : Nat := 337799068007762322241223

theorem tailTrace_740094 : CollatzResearch.WordTrace tailWord_740094 prefixEnd_740094 337799068007762322241223 := by
  unfold tailWord_740094
  simp only [CollatzResearch.WordTrace]
  refine ⟨3374180722596663854656417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17995630520515540558167557 3374180722596663854656417)
  ·
    refine ⟨2530635541947497890992313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3374180722596663854656417 2530635541947497890992313)
    ·
      refine ⟨1897976656460623418244235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2530635541947497890992313 1897976656460623418244235)
      ·
        refine ⟨2846964984690935127366353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897976656460623418244235 2846964984690935127366353)
        ·
          refine ⟨2135223738518201345524765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2846964984690935127366353 2135223738518201345524765)
          ·
            refine ⟨800708901944325504571787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2135223738518201345524765 800708901944325504571787)
            ·
              refine ⟨1201063352916488256857681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800708901944325504571787 1201063352916488256857681)
              ·
                refine ⟨900797514687366192643261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201063352916488256857681 900797514687366192643261)
                ·
                  refine ⟨337799068007762322241223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900797514687366192643261 337799068007762322241223)
                  ·
                    rfl

theorem cell20_740094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_740094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740094 prefixEnd_740094 := by exact prefixLift 740094
  have htrace : WordTrace (prefixWord ++ tailWord_740094) baseStart_740094 baseEnd_740094 := by
    simpa [prefixWord, tailWord_740094, baseEnd_740094] using wordTrace_append hprefix tailTrace_740094
  have hstable : (prefixWord ++ tailWord_740094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740094).length < 2 ^ (prefixWord ++ tailWord_740094).sum := by decide
  have hdescent : baseEnd_740094 < baseStart_740094 := by decide
  rcases family_descends (prefixWord ++ tailWord_740094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740125 : List Nat := [1, 4, 2, 4, 1, 2, 2, 4]
def baseStart_740125 : Nat := 118140960795 + 740125 * 2 ^ 59
def prefixEnd_740125 : Nat := 4983230072969 + 3 ^ 40 * 740125 * 2
def baseEnd_740125 : Nat := 112604405750821330735921

theorem tailTrace_740125 : CollatzResearch.WordTrace tailWord_740125 prefixEnd_740125 112604405750821330735921 := by
  unfold tailWord_740125
  simp only [CollatzResearch.WordTrace]
  refine ⟨26994576443661003131629829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17996384295774002087753219 26994576443661003131629829)
  ·
    refine ⟨5061483083186438087180593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26994576443661003131629829 5061483083186438087180593)
    ·
      refine ⟨3796112312389828565385445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5061483083186438087180593 3796112312389828565385445)
      ·
        refine ⟨711771058573092856009771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3796112312389828565385445 711771058573092856009771)
        ·
          refine ⟨1067656587859639284014657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711771058573092856009771 1067656587859639284014657)
          ·
            refine ⟨800742440894729463010993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1067656587859639284014657 800742440894729463010993)
            ·
              refine ⟨600556830671047097258245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800742440894729463010993 600556830671047097258245)
              ·
                refine ⟨112604405750821330735921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600556830671047097258245 112604405750821330735921)
                ·
                  rfl

theorem cell20_740125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_740125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740125 prefixEnd_740125 := by exact prefixLift 740125
  have htrace : WordTrace (prefixWord ++ tailWord_740125) baseStart_740125 baseEnd_740125 := by
    simpa [prefixWord, tailWord_740125, baseEnd_740125] using wordTrace_append hprefix tailTrace_740125
  have hstable : (prefixWord ++ tailWord_740125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740125).length < 2 ^ (prefixWord ++ tailWord_740125).sum := by decide
  have hdescent : baseEnd_740125 < baseStart_740125 := by decide
  rcases family_descends (prefixWord ++ tailWord_740125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740166 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_740166 : Nat := 118140960795 + 740166 * 2 ^ 59
def prefixEnd_740166 : Nat := 4983230072969 + 3 ^ 40 * 740166 * 2
def baseEnd_740166 : Nat := 337831930769650071840929

theorem tailTrace_740166 : CollatzResearch.WordTrace tailWord_740166 prefixEnd_740166 337831930769650071840929 := by
  unfold tailWord_740166
  simp only [CollatzResearch.WordTrace]
  refine ⟨843627244891014597933511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17997381224341644755914901 843627244891014597933511)
  ·
    refine ⟨1265440867336521896900267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 843627244891014597933511 1265440867336521896900267)
    ·
      refine ⟨1898161301004782845350401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1265440867336521896900267 1898161301004782845350401)
      ·
        refine ⟨1423620975753587134012801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1898161301004782845350401 1423620975753587134012801)
        ·
          refine ⟨1067715731815190350509601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1423620975753587134012801 1067715731815190350509601)
          ·
            refine ⟨800786798861392762882201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1067715731815190350509601 800786798861392762882201)
            ·
              refine ⟨600590099146044572161651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800786798861392762882201 600590099146044572161651)
              ·
                refine ⟨900885148719066858242477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600590099146044572161651 900885148719066858242477)
                ·
                  refine ⟨337831930769650071840929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 900885148719066858242477 337831930769650071840929)
                  ·
                    rfl

theorem cell20_740166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_740166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740166 prefixEnd_740166 := by exact prefixLift 740166
  have htrace : WordTrace (prefixWord ++ tailWord_740166) baseStart_740166 baseEnd_740166 := by
    simpa [prefixWord, tailWord_740166, baseEnd_740166] using wordTrace_append hprefix tailTrace_740166
  have hstable : (prefixWord ++ tailWord_740166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740166).length < 2 ^ (prefixWord ++ tailWord_740166).sum := by decide
  have hdescent : baseEnd_740166 < baseStart_740166 := by decide
  rcases family_descends (prefixWord ++ tailWord_740166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740209 : List Nat := [1, 2, 2, 2, 1, 12]
def baseStart_740209 : Nat := 118140960795 + 740209 * 2 ^ 59
def prefixEnd_740209 : Nat := 4983230072969 + 3 ^ 40 * 740209 * 2
def baseEnd_740209 : Nat := 12513020634864186422497

theorem tailTrace_740209 : CollatzResearch.WordTrace tailWord_740209 prefixEnd_740209 12513020634864186422497 := by
  unfold tailWord_740209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26997640175356685477687681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17998426783571123651791787 26997640175356685477687681)
  ·
    refine ⟨20248230131517514108265761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26997640175356685477687681 20248230131517514108265761)
    ·
      refine ⟨15186172598638135581199321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20248230131517514108265761 15186172598638135581199321)
      ·
        refine ⟨11389629448978601685899491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15186172598638135581199321 11389629448978601685899491)
        ·
          refine ⟨17084444173467902528849237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11389629448978601685899491 17084444173467902528849237)
          ·
            refine ⟨12513020634864186422497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17084444173467902528849237 12513020634864186422497)
            ·
              rfl

theorem cell20_740209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 12].length) (baseStart_740209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740209 prefixEnd_740209 := by exact prefixLift 740209
  have htrace : WordTrace (prefixWord ++ tailWord_740209) baseStart_740209 baseEnd_740209 := by
    simpa [prefixWord, tailWord_740209, baseEnd_740209] using wordTrace_append hprefix tailTrace_740209
  have hstable : (prefixWord ++ tailWord_740209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740209).length < 2 ^ (prefixWord ++ tailWord_740209).sum := by decide
  have hdescent : baseEnd_740209 < baseStart_740209 := by decide
  rcases family_descends (prefixWord ++ tailWord_740209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740271 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 3]
def baseStart_740271 : Nat := 118140960795 + 740271 * 2 ^ 59
def prefixEnd_740271 : Nat := 4983230072969 + 3 ^ 40 * 740271 * 2
def baseEnd_740271 : Nat := 337879855630736373340499

theorem tailTrace_740271 : CollatzResearch.WordTrace tailWord_740271 prefixEnd_740271 337879855630736373340499 := by
  unfold tailWord_740271
  simp only [CollatzResearch.WordTrace]
  refine ⟨26999901501132070066444667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17999934334088046710963111 26999901501132070066444667)
  ·
    refine ⟨40499852251698105099667001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26999901501132070066444667 40499852251698105099667001)
    ·
      refine ⟨30374889188773578824750251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40499852251698105099667001 30374889188773578824750251)
      ·
        refine ⟨45562333783160368237125377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30374889188773578824750251 45562333783160368237125377)
        ·
          refine ⟨34171750337370276177844033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45562333783160368237125377 34171750337370276177844033)
          ·
            refine ⟨25628812753027707133383025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34171750337370276177844033 25628812753027707133383025)
            ·
              refine ⟨19221609564770780350037269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25628812753027707133383025 19221609564770780350037269)
              ·
                refine ⟨901012948348630328907997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19221609564770780350037269 901012948348630328907997)
                ·
                  refine ⟨337879855630736373340499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901012948348630328907997 337879855630736373340499)
                  ·
                    rfl

theorem cell20_740271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 3].length) (baseStart_740271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740271 prefixEnd_740271 := by exact prefixLift 740271
  have htrace : WordTrace (prefixWord ++ tailWord_740271) baseStart_740271 baseEnd_740271 := by
    simpa [prefixWord, tailWord_740271, baseEnd_740271] using wordTrace_append hprefix tailTrace_740271
  have hstable : (prefixWord ++ tailWord_740271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740271).length < 2 ^ (prefixWord ++ tailWord_740271).sum := by decide
  have hdescent : baseEnd_740271 < baseStart_740271 := by decide
  rcases family_descends (prefixWord ++ tailWord_740271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740294 : List Nat := [6, 1, 3, 1, 1, 1, 1, 6]
def baseStart_740294 : Nat := 118140960795 + 740294 * 2 ^ 59
def prefixEnd_740294 : Nat := 4983230072969 + 3 ^ 40 * 740294 * 2
def baseEnd_740294 : Nat := 112630117819150171857913

theorem tailTrace_740294 : CollatzResearch.WordTrace tailWord_740294 prefixEnd_740294 112630117819150171857913 := by
  unfold tailWord_740294
  simp only [CollatzResearch.WordTrace]
  refine ⟨843773136876523281079123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18000493586699163329687957 843773136876523281079123)
  ·
    refine ⟨1265659705314784921618685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 843773136876523281079123 1265659705314784921618685)
    ·
      refine ⟨474622389493044345607007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1265659705314784921618685 474622389493044345607007)
      ·
        refine ⟨711933584239566518410511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474622389493044345607007 711933584239566518410511)
        ·
          refine ⟨1067900376359349777615767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711933584239566518410511 1067900376359349777615767)
          ·
            refine ⟨1601850564539024666423651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1067900376359349777615767 1601850564539024666423651)
            ·
              refine ⟨2402775846808536999635477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601850564539024666423651 2402775846808536999635477)
              ·
                refine ⟨112630117819150171857913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2402775846808536999635477 112630117819150171857913)
                ·
                  rfl

theorem cell20_740294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_740294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740294 prefixEnd_740294 := by exact prefixLift 740294
  have htrace : WordTrace (prefixWord ++ tailWord_740294) baseStart_740294 baseEnd_740294 := by
    simpa [prefixWord, tailWord_740294, baseEnd_740294] using wordTrace_append hprefix tailTrace_740294
  have hstable : (prefixWord ++ tailWord_740294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740294).length < 2 ^ (prefixWord ++ tailWord_740294).sum := by decide
  have hdescent : baseEnd_740294 < baseStart_740294 := by decide
  rcases family_descends (prefixWord ++ tailWord_740294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740302 : List Nat := [4, 1, 1, 1, 2, 4, 1, 6]
def baseStart_740302 : Nat := 118140960795 + 740302 * 2 ^ 59
def prefixEnd_740302 : Nat := 4983230072969 + 3 ^ 40 * 740302 * 2
def baseEnd_740302 : Nat := 112631334958479347769013

theorem tailTrace_740302 : CollatzResearch.WordTrace tailWord_740302 prefixEnd_740302 112631334958479347769013 := by
  unfold tailWord_740302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375129020502470295102895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18000688109346508240548773 3375129020502470295102895)
  ·
    refine ⟨5062693530753705442654343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375129020502470295102895 5062693530753705442654343)
    ·
      refine ⟨7594040296130558163981515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062693530753705442654343 7594040296130558163981515)
      ·
        refine ⟨11391060444195837245972273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7594040296130558163981515 11391060444195837245972273)
        ·
          refine ⟨8543295333146877934479205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11391060444195837245972273 8543295333146877934479205)
          ·
            refine ⟨1601867874965039612714851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8543295333146877934479205 1601867874965039612714851)
            ·
              refine ⟨2402801812447559419072277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1601867874965039612714851 2402801812447559419072277)
              ·
                refine ⟨112631334958479347769013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2402801812447559419072277 112631334958479347769013)
                ·
                  rfl

theorem cell20_740302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_740302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740302 prefixEnd_740302 := by exact prefixLift 740302
  have htrace : WordTrace (prefixWord ++ tailWord_740302) baseStart_740302 baseEnd_740302 := by
    simpa [prefixWord, tailWord_740302, baseEnd_740302] using wordTrace_append hprefix tailTrace_740302
  have hstable : (prefixWord ++ tailWord_740302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740302).length < 2 ^ (prefixWord ++ tailWord_740302).sum := by decide
  have hdescent : baseEnd_740302 < baseStart_740302 := by decide
  rcases family_descends (prefixWord ++ tailWord_740302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740312 : List Nat := [2, 1, 2, 2, 2, 3, 3, 3, 2]
def baseStart_740312 : Nat := 118140960795 + 740312 * 2 ^ 59
def prefixEnd_740312 : Nat := 4983230072969 + 3 ^ 40 * 740312 * 2
def baseEnd_740312 : Nat := 337898569147922452973665

theorem tailTrace_740312 : CollatzResearch.WordTrace tailWord_740312 prefixEnd_740312 337898569147922452973665 := by
  unfold tailWord_740312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500698446991767034343595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18000931262655689379124793 13500698446991767034343595)
  ·
    refine ⟨20251047670487650551515393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13500698446991767034343595 20251047670487650551515393)
    ·
      refine ⟨15188285752865737913636545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20251047670487650551515393 15188285752865737913636545)
      ·
        refine ⟨11391214314649303435227409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15188285752865737913636545 11391214314649303435227409)
        ·
          refine ⟨8543410735986977576420557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11391214314649303435227409 8543410735986977576420557)
          ·
            refine ⟨3203779025995116591157709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8543410735986977576420557 3203779025995116591157709)
            ·
              refine ⟨1201417134748168721684141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3203779025995116591157709 1201417134748168721684141)
              ·
                refine ⟨450531425530563270631553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201417134748168721684141 450531425530563270631553)
                ·
                  refine ⟨337898569147922452973665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450531425530563270631553 337898569147922452973665)
                  ·
                    rfl

theorem cell20_740312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_740312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740312 prefixEnd_740312 := by exact prefixLift 740312
  have htrace : WordTrace (prefixWord ++ tailWord_740312) baseStart_740312 baseEnd_740312 := by
    simpa [prefixWord, tailWord_740312, baseEnd_740312] using wordTrace_append hprefix tailTrace_740312
  have hstable : (prefixWord ++ tailWord_740312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740312).length < 2 ^ (prefixWord ++ tailWord_740312).sum := by decide
  have hdescent : baseEnd_740312 < baseStart_740312 := by decide
  rcases family_descends (prefixWord ++ tailWord_740312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740319 : List Nat := [1, 1, 2, 3, 6, 1, 6]
def baseStart_740319 : Nat := 118140960795 + 740319 * 2 ^ 59
def prefixEnd_740319 : Nat := 4983230072969 + 3 ^ 40 * 740319 * 2
def baseEnd_740319 : Nat := 37544640459851282193367

theorem tailTrace_740319 : CollatzResearch.WordTrace tailWord_740319 prefixEnd_740319 37544640459851282193367 := by
  unfold tailWord_740319
  simp only [CollatzResearch.WordTrace]
  refine ⟨27001652204958174264192011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18001101469972116176128007 27001652204958174264192011)
  ·
    refine ⟨40502478307437261396288017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27001652204958174264192011 40502478307437261396288017)
    ·
      refine ⟨30376858730577946047216013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40502478307437261396288017 30376858730577946047216013)
      ·
        refine ⟨11391322023966729767706005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30376858730577946047216013 11391322023966729767706005)
        ·
          refine ⟨533968219873440457861219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11391322023966729767706005 533968219873440457861219)
          ·
            refine ⟨800952329810160686791829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533968219873440457861219 800952329810160686791829)
            ·
              refine ⟨37544640459851282193367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 800952329810160686791829 37544640459851282193367)
              ·
                rfl

theorem cell20_740319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 6].length) (baseStart_740319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740319 prefixEnd_740319 := by exact prefixLift 740319
  have htrace : WordTrace (prefixWord ++ tailWord_740319) baseStart_740319 baseEnd_740319 := by
    simpa [prefixWord, tailWord_740319, baseEnd_740319] using wordTrace_append hprefix tailTrace_740319
  have hstable : (prefixWord ++ tailWord_740319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740319).length < 2 ^ (prefixWord ++ tailWord_740319).sum := by decide
  have hdescent : baseEnd_740319 < baseStart_740319 := by decide
  rcases family_descends (prefixWord ++ tailWord_740319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740371 : List Nat := [1, 1, 1, 2, 1, 4, 1, 7, 2]
def baseStart_740371 : Nat := 118140960795 + 740371 * 2 ^ 59
def prefixEnd_740371 : Nat := 4983230072969 + 3 ^ 40 * 740371 * 2
def baseEnd_740371 : Nat := 337925498355580470006757

theorem tailTrace_740371 : CollatzResearch.WordTrace tailWord_740371 prefixEnd_740371 337925498355580470006757 := by
  unfold tailWord_740371
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003548800769787145084967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18002365867179858096723311 27003548800769787145084967)
  ·
    refine ⟨40505323201154680717627451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27003548800769787145084967 40505323201154680717627451)
    ·
      refine ⟨60757984801732021076441177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40505323201154680717627451 60757984801732021076441177)
      ·
        refine ⟨45568488601299015807330883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60757984801732021076441177 45568488601299015807330883)
        ·
          refine ⟨68352732901948523710996325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45568488601299015807330883 68352732901948523710996325)
          ·
            refine ⟨12816137419115348195811811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68352732901948523710996325 12816137419115348195811811)
            ·
              refine ⟨19224206128673022293717717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12816137419115348195811811 19224206128673022293717717)
              ·
                refine ⟨450567331140773960009009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19224206128673022293717717 450567331140773960009009)
                ·
                  refine ⟨337925498355580470006757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450567331140773960009009 337925498355580470006757)
                  ·
                    rfl

theorem cell20_740371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 2].length) (baseStart_740371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740371 prefixEnd_740371 := by exact prefixLift 740371
  have htrace : WordTrace (prefixWord ++ tailWord_740371) baseStart_740371 baseEnd_740371 := by
    simpa [prefixWord, tailWord_740371, baseEnd_740371] using wordTrace_append hprefix tailTrace_740371
  have hstable : (prefixWord ++ tailWord_740371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740371).length < 2 ^ (prefixWord ++ tailWord_740371).sum := by decide
  have hdescent : baseEnd_740371 < baseStart_740371 := by decide
  rcases family_descends (prefixWord ++ tailWord_740371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740381 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 3]
def baseStart_740381 : Nat := 118140960795 + 740381 * 2 ^ 59
def prefixEnd_740381 : Nat := 4983230072969 + 3 ^ 40 * 740381 * 2
def baseEnd_740381 : Nat := 337930062628064879673383

theorem tailTrace_740381 : CollatzResearch.WordTrace tailWord_740381 prefixEnd_740381 337930062628064879673383 := by
  unfold tailWord_740381
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003913530733558852948997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18002609020489039235299331 27003913530733558852948997)
  ·
    refine ⟨5063233787012542284927937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27003913530733558852948997 5063233787012542284927937)
    ·
      refine ⟨3797425340259406713695953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5063233787012542284927937 3797425340259406713695953)
      ·
        refine ⟨2848069005194555035271965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3797425340259406713695953 2848069005194555035271965)
        ·
          refine ⟨1068025876947958138226987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2848069005194555035271965 1068025876947958138226987)
          ·
            refine ⟨1602038815421937207340481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068025876947958138226987 1602038815421937207340481)
            ·
              refine ⟨1201529111566452905505361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602038815421937207340481 1201529111566452905505361)
              ·
                refine ⟨901146833674839679129021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201529111566452905505361 901146833674839679129021)
                ·
                  refine ⟨337930062628064879673383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901146833674839679129021 337930062628064879673383)
                  ·
                    rfl

theorem cell20_740381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_740381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740381 prefixEnd_740381 := by exact prefixLift 740381
  have htrace : WordTrace (prefixWord ++ tailWord_740381) baseStart_740381 baseEnd_740381 := by
    simpa [prefixWord, tailWord_740381, baseEnd_740381] using wordTrace_append hprefix tailTrace_740381
  have hstable : (prefixWord ++ tailWord_740381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740381).length < 2 ^ (prefixWord ++ tailWord_740381).sum := by decide
  have hdescent : baseEnd_740381 < baseStart_740381 := by decide
  rcases family_descends (prefixWord ++ tailWord_740381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740409 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 4]
def baseStart_740409 : Nat := 118140960795 + 740409 * 2 ^ 59
def prefixEnd_740409 : Nat := 4983230072969 + 3 ^ 40 * 740409 * 2
def baseEnd_740409 : Nat := 337942842591021226739935

theorem tailTrace_740409 : CollatzResearch.WordTrace tailWord_740409 prefixEnd_740409 337942842591021226739935 := by
  unfold tailWord_740409
  simp only [CollatzResearch.WordTrace]
  refine ⟨27004934774632119634968281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18003289849754746423312187 27004934774632119634968281)
  ·
    refine ⟨20253701080974089726226211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27004934774632119634968281 20253701080974089726226211)
    ·
      refine ⟨30380551621461134589339317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20253701080974089726226211 30380551621461134589339317)
      ·
        refine ⟨2848176714511981367750561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30380551621461134589339317 2848176714511981367750561)
        ·
          refine ⟨2136132535883986025812921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848176714511981367750561 2136132535883986025812921)
          ·
            refine ⟨1602099401912989519359691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2136132535883986025812921 1602099401912989519359691)
            ·
              refine ⟨2403149102869484279039537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602099401912989519359691 2403149102869484279039537)
              ·
                refine ⟨1802361827152113209279653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403149102869484279039537 1802361827152113209279653)
                ·
                  refine ⟨337942842591021226739935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802361827152113209279653 337942842591021226739935)
                  ·
                    rfl

theorem cell20_740409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_740409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740409 prefixEnd_740409 := by exact prefixLift 740409
  have htrace : WordTrace (prefixWord ++ tailWord_740409) baseStart_740409 baseEnd_740409 := by
    simpa [prefixWord, tailWord_740409, baseEnd_740409] using wordTrace_append hprefix tailTrace_740409
  have hstable : (prefixWord ++ tailWord_740409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740409).length < 2 ^ (prefixWord ++ tailWord_740409).sum := by decide
  have hdescent : baseEnd_740409 < baseStart_740409 := by decide
  rcases family_descends (prefixWord ++ tailWord_740409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740416 : List Nat := [2, 1, 1, 2, 2, 3, 5, 4]
def baseStart_740416 : Nat := 118140960795 + 740416 * 2 ^ 59
def prefixEnd_740416 : Nat := 4983230072969 + 3 ^ 40 * 740416 * 2
def baseEnd_740416 : Nat := 112648679193920104502191

theorem tailTrace_740416 : CollatzResearch.WordTrace tailWord_740416 prefixEnd_740416 112648679193920104502191 := by
  unfold tailWord_740416
  simp only [CollatzResearch.WordTrace]
  refine ⟨13502595042803379915236551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18003460057071173220315401 13502595042803379915236551)
  ·
    refine ⟨20253892564205069872854827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13502595042803379915236551 20253892564205069872854827)
    ·
      refine ⟨30380838846307604809282241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20253892564205069872854827 30380838846307604809282241)
      ·
        refine ⟨22785629134730703606961681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30380838846307604809282241 22785629134730703606961681)
        ·
          refine ⟨17089221851048027705221261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22785629134730703606961681 17089221851048027705221261)
          ·
            refine ⟨6408458194143010389457973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17089221851048027705221261 6408458194143010389457973)
            ·
              refine ⟨600792955700907224011685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6408458194143010389457973 600792955700907224011685)
              ·
                refine ⟨112648679193920104502191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600792955700907224011685 112648679193920104502191)
                ·
                  rfl

theorem cell20_740416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_740416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740416 prefixEnd_740416 := by exact prefixLift 740416
  have htrace : WordTrace (prefixWord ++ tailWord_740416) baseStart_740416 baseEnd_740416 := by
    simpa [prefixWord, tailWord_740416, baseEnd_740416] using wordTrace_append hprefix tailTrace_740416
  have hstable : (prefixWord ++ tailWord_740416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740416).length < 2 ^ (prefixWord ++ tailWord_740416).sum := by decide
  have hdescent : baseEnd_740416 < baseStart_740416 := by decide
  rcases family_descends (prefixWord ++ tailWord_740416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740422 : List Nat := [6, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_740422 : Nat := 118140960795 + 740422 * 2 ^ 59
def prefixEnd_740422 : Nat := 4983230072969 + 3 ^ 40 * 740422 * 2
def baseEnd_740422 : Nat := 337948776145250959306549

theorem tailTrace_740422 : CollatzResearch.WordTrace tailWord_740422 prefixEnd_740422 337948776145250959306549 := by
  unfold tailWord_740422
  simp only [CollatzResearch.WordTrace]
  refine ⟨843919028862031964224735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 18003605949056681903461013 843919028862031964224735)
  ·
    refine ⟨1265878543293047946337103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 843919028862031964224735 1265878543293047946337103)
    ·
      refine ⟨1898817814939571919505655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1265878543293047946337103 1898817814939571919505655)
      ·
        refine ⟨2848226722409357879258483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1898817814939571919505655 2848226722409357879258483)
        ·
          refine ⟨4272340083614036818887725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848226722409357879258483 4272340083614036818887725)
          ·
            refine ⟨1602127531355263807082897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4272340083614036818887725 1602127531355263807082897)
            ·
              refine ⟨1201595648516447855312173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602127531355263807082897 1201595648516447855312173)
              ·
                refine ⟨450598368193667945742065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201595648516447855312173 450598368193667945742065)
                ·
                  refine ⟨337948776145250959306549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450598368193667945742065 337948776145250959306549)
                  ·
                    rfl

theorem cell20_740422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_740422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740422 prefixEnd_740422 := by exact prefixLift 740422
  have htrace : WordTrace (prefixWord ++ tailWord_740422) baseStart_740422 baseEnd_740422 := by
    simpa [prefixWord, tailWord_740422, baseEnd_740422] using wordTrace_append hprefix tailTrace_740422
  have hstable : (prefixWord ++ tailWord_740422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740422).length < 2 ^ (prefixWord ++ tailWord_740422).sum := by decide
  have hdescent : baseEnd_740422 < baseStart_740422 := by decide
  rcases family_descends (prefixWord ++ tailWord_740422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740430 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_740430 : Nat := 118140960795 + 740430 * 2 ^ 59
def prefixEnd_740430 : Nat := 4983230072969 + 3 ^ 40 * 740430 * 2
def baseEnd_740430 : Nat := 337952427563238487039849

theorem tailTrace_740430 : CollatzResearch.WordTrace tailWord_740430 prefixEnd_740430 337952427563238487039849 := by
  unfold tailWord_740430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375712588444505027685343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18003800471704026814321829 3375712588444505027685343)
  ·
    refine ⟨5063568882666757541528015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375712588444505027685343 5063568882666757541528015)
    ·
      refine ⟨7595353324000136312292023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063568882666757541528015 7595353324000136312292023)
      ·
        refine ⟨11393029986000204468438035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595353324000136312292023 11393029986000204468438035)
        ·
          refine ⟨17089544979000306702657053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393029986000204468438035 17089544979000306702657053)
          ·
            refine ⟨6408579367125115013496395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17089544979000306702657053 6408579367125115013496395)
            ·
              refine ⟨9612869050687672520244593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408579367125115013496395 9612869050687672520244593)
              ·
                refine ⟨7209651788015754390183445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9612869050687672520244593 7209651788015754390183445)
                ·
                  refine ⟨337952427563238487039849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7209651788015754390183445 337952427563238487039849)
                  ·
                    rfl

theorem cell20_740430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_740430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740430 prefixEnd_740430 := by exact prefixLift 740430
  have htrace : WordTrace (prefixWord ++ tailWord_740430) baseStart_740430 baseEnd_740430 := by
    simpa [prefixWord, tailWord_740430, baseEnd_740430] using wordTrace_append hprefix tailTrace_740430
  have hstable : (prefixWord ++ tailWord_740430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740430).length < 2 ^ (prefixWord ++ tailWord_740430).sum := by decide
  have hdescent : baseEnd_740430 < baseStart_740430 := by decide
  rcases family_descends (prefixWord ++ tailWord_740430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740437 : List Nat := [1, 3, 2, 2, 1, 2, 9]
def baseStart_740437 : Nat := 118140960795 + 740437 * 2 ^ 59
def prefixEnd_740437 : Nat := 4983230072969 + 3 ^ 40 * 740437 * 2
def baseEnd_740437 : Nat := 37550624728219730422943

theorem tailTrace_740437 : CollatzResearch.WordTrace tailWord_740437 prefixEnd_740437 37550624728219730422943 := by
  unfold tailWord_740437
  simp only [CollatzResearch.WordTrace]
  refine ⟨27005956018530680416987565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18003970679020453611325043 27005956018530680416987565)
  ·
    refine ⟨10127233506949005156370337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27005956018530680416987565 10127233506949005156370337)
    ·
      refine ⟨7595425130211753867277753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10127233506949005156370337 7595425130211753867277753)
      ·
        refine ⟨5696568847658815400458315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7595425130211753867277753 5696568847658815400458315)
        ·
          refine ⟨8544853271488223100687473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696568847658815400458315 8544853271488223100687473)
          ·
            refine ⟨6408639953616167325515605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8544853271488223100687473 6408639953616167325515605)
            ·
              refine ⟨37550624728219730422943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6408639953616167325515605 37550624728219730422943)
              ·
                rfl

theorem cell20_740437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 9].length) (baseStart_740437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740437 prefixEnd_740437 := by exact prefixLift 740437
  have htrace : WordTrace (prefixWord ++ tailWord_740437) baseStart_740437 baseEnd_740437 := by
    simpa [prefixWord, tailWord_740437, baseEnd_740437] using wordTrace_append hprefix tailTrace_740437
  have hstable : (prefixWord ++ tailWord_740437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740437).length < 2 ^ (prefixWord ++ tailWord_740437).sum := by decide
  have hdescent : baseEnd_740437 < baseStart_740437 := by decide
  rcases family_descends (prefixWord ++ tailWord_740437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740447 : List Nat := [1, 1, 2, 3, 1, 1, 3, 6, 2]
def baseStart_740447 : Nat := 118140960795 + 740447 * 2 ^ 59
def prefixEnd_740447 : Nat := 4983230072969 + 3 ^ 40 * 740447 * 2
def baseEnd_740447 : Nat := 337960186826461983473113

theorem tailTrace_740447 : CollatzResearch.WordTrace tailWord_740447 prefixEnd_740447 337960186826461983473113 := by
  unfold tailWord_740447
  simp only [CollatzResearch.WordTrace]
  refine ⟨27006320748494452124851595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18004213832329634749901063 27006320748494452124851595)
  ·
    refine ⟨40509481122741678187277393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27006320748494452124851595 40509481122741678187277393)
    ·
      refine ⟨30382110842056258640458045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40509481122741678187277393 30382110842056258640458045)
      ·
        refine ⟨11393291565771096990171767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30382110842056258640458045 11393291565771096990171767)
        ·
          refine ⟨17089937348656645485257651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393291565771096990171767 17089937348656645485257651)
          ·
            refine ⟨25634906022984968227886477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17089937348656645485257651 25634906022984968227886477)
            ·
              refine ⟨9613089758619363085457429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25634906022984968227886477 9613089758619363085457429)
              ·
                refine ⟨450613582435282644630817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9613089758619363085457429 450613582435282644630817)
                ·
                  refine ⟨337960186826461983473113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450613582435282644630817 337960186826461983473113)
                  ·
                    rfl

theorem cell20_740447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 2].length) (baseStart_740447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740447 prefixEnd_740447 := by exact prefixLift 740447
  have htrace : WordTrace (prefixWord ++ tailWord_740447) baseStart_740447 baseEnd_740447 := by
    simpa [prefixWord, tailWord_740447, baseEnd_740447] using wordTrace_append hprefix tailTrace_740447
  have hstable : (prefixWord ++ tailWord_740447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740447).length < 2 ^ (prefixWord ++ tailWord_740447).sum := by decide
  have hdescent : baseEnd_740447 < baseStart_740447 := by decide
  rcases family_descends (prefixWord ++ tailWord_740447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740481 : List Nat := [1, 2, 4, 2, 2, 3, 1, 3, 2]
def baseStart_740481 : Nat := 118140960795 + 740481 * 2 ^ 59
def prefixEnd_740481 : Nat := 4983230072969 + 3 ^ 40 * 740481 * 2
def baseEnd_740481 : Nat := 337975705352908976339641

theorem tailTrace_740481 : CollatzResearch.WordTrace tailWord_740481 prefixEnd_740481 337975705352908976339641 := by
  unfold tailWord_740481
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007560830371275931589297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18005040553580850621059531 27007560830371275931589297)
  ·
    refine ⟨20255670622778456948691973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27007560830371275931589297 20255670622778456948691973)
    ·
      refine ⟨3797938241770960677879745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20255670622778456948691973 3797938241770960677879745)
      ·
        refine ⟨2848453681328220508409809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3797938241770960677879745 2848453681328220508409809)
        ·
          refine ⟨2136340260996165381307357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848453681328220508409809 2136340260996165381307357)
          ·
            refine ⟨801127597873562017990259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2136340260996165381307357 801127597873562017990259)
            ·
              refine ⟨1201691396810343026985389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801127597873562017990259 1201691396810343026985389)
              ·
                refine ⟨450634273803878635119521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201691396810343026985389 450634273803878635119521)
                ·
                  refine ⟨337975705352908976339641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 450634273803878635119521 337975705352908976339641)
                  ·
                    rfl

theorem cell20_740481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_740481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740481 prefixEnd_740481 := by exact prefixLift 740481
  have htrace : WordTrace (prefixWord ++ tailWord_740481) baseStart_740481 baseEnd_740481 := by
    simpa [prefixWord, tailWord_740481, baseEnd_740481] using wordTrace_append hprefix tailTrace_740481
  have hstable : (prefixWord ++ tailWord_740481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740481).length < 2 ^ (prefixWord ++ tailWord_740481).sum := by decide
  have hdescent : baseEnd_740481 < baseStart_740481 := by decide
  rcases family_descends (prefixWord ++ tailWord_740481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740516 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 3]
def baseStart_740516 : Nat := 118140960795 + 740516 * 2 ^ 59
def prefixEnd_740516 : Nat := 4983230072969 + 3 ^ 40 * 740516 * 2
def baseEnd_740516 : Nat := 337991680306604410172831

theorem tailTrace_740516 : CollatzResearch.WordTrace tailWord_740516 prefixEnd_740516 337991680306604410172831 := by
  unfold tailWord_740516
  simp only [CollatzResearch.WordTrace]
  refine ⟨13504418692622238454556701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18005891590162984606075601 13504418692622238454556701)
  ·
    refine ⟨5064157009733339420458763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13504418692622238454556701 5064157009733339420458763)
    ·
      refine ⟨7596235514600009130688145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5064157009733339420458763 7596235514600009130688145)
      ·
        refine ⟨5697176635950006848016109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7596235514600009130688145 5697176635950006848016109)
        ·
          refine ⟨2136441238481252568006041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5697176635950006848016109 2136441238481252568006041)
          ·
            refine ⟨1602330928860939426004531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2136441238481252568006041 1602330928860939426004531)
            ·
              refine ⟨2403496393291409139006797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1602330928860939426004531 2403496393291409139006797)
              ·
                refine ⟨901311147484278427127549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2403496393291409139006797 901311147484278427127549)
                ·
                  refine ⟨337991680306604410172831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901311147484278427127549 337991680306604410172831)
                  ·
                    rfl

theorem cell20_740516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_740516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740516 prefixEnd_740516 := by exact prefixLift 740516
  have htrace : WordTrace (prefixWord ++ tailWord_740516) baseStart_740516 baseEnd_740516 := by
    simpa [prefixWord, tailWord_740516, baseEnd_740516] using wordTrace_append hprefix tailTrace_740516
  have hstable : (prefixWord ++ tailWord_740516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740516).length < 2 ^ (prefixWord ++ tailWord_740516).sum := by decide
  have hdescent : baseEnd_740516 < baseStart_740516 := by decide
  rcases family_descends (prefixWord ++ tailWord_740516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740554 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_740554 : Nat := 118140960795 + 740554 * 2 ^ 59
def prefixEnd_740554 : Nat := 4983230072969 + 3 ^ 40 * 740554 * 2
def baseEnd_740554 : Nat := 338009024542045166906009

theorem tailTrace_740554 : CollatzResearch.WordTrace tailWord_740554 prefixEnd_740554 338009024542045166906009 := by
  unfold tailWord_740554
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752555839776702349749179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18006815572737872932664477 6752555839776702349749179)
  ·
    refine ⟨10128833759665053524623769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6752555839776702349749179 10128833759665053524623769)
    ·
      refine ⟨7596625319748790143467827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10128833759665053524623769 7596625319748790143467827)
      ·
        refine ⟨11394937979623185215201741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7596625319748790143467827 11394937979623185215201741)
        ·
          refine ⟨4273101742358694455700653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11394937979623185215201741 4273101742358694455700653)
          ·
            refine ⟨1602413153384510420887745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4273101742358694455700653 1602413153384510420887745)
            ·
              refine ⟨1201809865038382815665809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602413153384510420887745 1201809865038382815665809)
              ·
                refine ⟨901357398778787111749357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1201809865038382815665809 901357398778787111749357)
                ·
                  refine ⟨338009024542045166906009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901357398778787111749357 338009024542045166906009)
                  ·
                    rfl

theorem cell20_740554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_740554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740554 prefixEnd_740554 := by exact prefixLift 740554
  have htrace : WordTrace (prefixWord ++ tailWord_740554) baseStart_740554 baseEnd_740554 := by
    simpa [prefixWord, tailWord_740554, baseEnd_740554] using wordTrace_append hprefix tailTrace_740554
  have hstable : (prefixWord ++ tailWord_740554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740554).length < 2 ^ (prefixWord ++ tailWord_740554).sum := by decide
  have hdescent : baseEnd_740554 < baseStart_740554 := by decide
  rcases family_descends (prefixWord ++ tailWord_740554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740564 : List Nat := [2, 4, 1, 4, 1, 2, 1, 5]
def baseStart_740564 : Nat := 118140960795 + 740564 * 2 ^ 59
def prefixEnd_740564 : Nat := 4983230072969 + 3 ^ 40 * 740564 * 2
def baseEnd_740564 : Nat := 112671196271509858857545

theorem tailTrace_740564 : CollatzResearch.WordTrace tailWord_740564 prefixEnd_740564 112671196271509858857545 := by
  unfold tailWord_740564
  simp only [CollatzResearch.WordTrace]
  refine ⟨13505294044535290553430373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18007058726047054071240497 13505294044535290553430373)
  ·
    refine ⟨2532242633350366978768195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13505294044535290553430373 2532242633350366978768195)
    ·
      refine ⟨3798363950025550468152293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2532242633350366978768195 3798363950025550468152293)
      ·
        refine ⟨712193240629790712778555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3798363950025550468152293 712193240629790712778555)
        ·
          refine ⟨1068289860944686069167833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712193240629790712778555 1068289860944686069167833)
          ·
            refine ⟨801217395708514551875875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068289860944686069167833 801217395708514551875875)
            ·
              refine ⟨1201826093562771827813813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801217395708514551875875 1201826093562771827813813)
              ·
                refine ⟨112671196271509858857545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1201826093562771827813813 112671196271509858857545)
                ·
                  rfl

theorem cell20_740564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_740564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740564 prefixEnd_740564 := by exact prefixLift 740564
  have htrace : WordTrace (prefixWord ++ tailWord_740564) baseStart_740564 baseEnd_740564 := by
    simpa [prefixWord, tailWord_740564, baseEnd_740564] using wordTrace_append hprefix tailTrace_740564
  have hstable : (prefixWord ++ tailWord_740564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740564).length < 2 ^ (prefixWord ++ tailWord_740564).sum := by decide
  have hdescent : baseEnd_740564 < baseStart_740564 := by decide
  rcases family_descends (prefixWord ++ tailWord_740564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740575 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 3]
def baseStart_740575 : Nat := 118140960795 + 740575 * 2 ^ 59
def prefixEnd_740575 : Nat := 4983230072969 + 3 ^ 40 * 740575 * 2
def baseEnd_740575 : Nat := 338018609514262427205923

theorem tailTrace_740575 : CollatzResearch.WordTrace tailWord_740575 prefixEnd_740575 338018609514262427205923 := by
  unfold tailWord_740575
  simp only [CollatzResearch.WordTrace]
  refine ⟨27010989292030729985511179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18007326194687153323674119 27010989292030729985511179)
  ·
    refine ⟨40516483938046094978266769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27010989292030729985511179 40516483938046094978266769)
    ·
      refine ⟨30387362953534571233700077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40516483938046094978266769 30387362953534571233700077)
      ·
        refine ⟨11395261107575464212637529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30387362953534571233700077 11395261107575464212637529)
        ·
          refine ⟨8546445830681598159478147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11395261107575464212637529 8546445830681598159478147)
          ·
            refine ⟨12819668746022397239217221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8546445830681598159478147 12819668746022397239217221)
            ·
              refine ⟨2403687889879199482353229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12819668746022397239217221 2403687889879199482353229)
              ·
                refine ⟨901382958704699805882461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2403687889879199482353229 901382958704699805882461)
                ·
                  refine ⟨338018609514262427205923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901382958704699805882461 338018609514262427205923)
                  ·
                    rfl

theorem cell20_740575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_740575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740575 prefixEnd_740575 := by exact prefixLift 740575
  have htrace : WordTrace (prefixWord ++ tailWord_740575) baseStart_740575 baseEnd_740575 := by
    simpa [prefixWord, tailWord_740575, baseEnd_740575] using wordTrace_append hprefix tailTrace_740575
  have hstable : (prefixWord ++ tailWord_740575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740575).length < 2 ^ (prefixWord ++ tailWord_740575).sum := by decide
  have hdescent : baseEnd_740575 < baseStart_740575 := by decide
  rcases family_descends (prefixWord ++ tailWord_740575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740606 : List Nat := [4, 2, 2, 1, 1, 3, 7]
def baseStart_740606 : Nat := 118140960795 + 740606 * 2 ^ 59
def prefixEnd_740606 : Nat := 4983230072969 + 3 ^ 40 * 740606 * 2
def baseEnd_740606 : Nat := 37559195417662677463607

theorem tailTrace_740606 : CollatzResearch.WordTrace tailWord_740606 prefixEnd_740606 37559195417662677463607 := by
  unfold tailWord_740606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376514994364802784986209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 18008079969945614853259781 3376514994364802784986209)
  ·
    refine ⟨2532386245773602088739657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3376514994364802784986209 2532386245773602088739657)
    ·
      refine ⟨1899289684330201566554743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2532386245773602088739657 1899289684330201566554743)
      ·
        refine ⟨2848934526495302349832115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899289684330201566554743 2848934526495302349832115)
        ·
          refine ⟨4273401789742953524748173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848934526495302349832115 4273401789742953524748173)
          ·
            refine ⟨1602525671153607571780565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4273401789742953524748173 1602525671153607571780565)
            ·
              refine ⟨37559195417662677463607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1602525671153607571780565 37559195417662677463607)
              ·
                rfl

theorem cell20_740606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 7].length) (baseStart_740606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740606 prefixEnd_740606 := by exact prefixLift 740606
  have htrace : WordTrace (prefixWord ++ tailWord_740606) baseStart_740606 baseEnd_740606 := by
    simpa [prefixWord, tailWord_740606, baseEnd_740606] using wordTrace_append hprefix tailTrace_740606
  have hstable : (prefixWord ++ tailWord_740606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740606).length < 2 ^ (prefixWord ++ tailWord_740606).sum := by decide
  have hdescent : baseEnd_740606 < baseStart_740606 := by decide
  rcases family_descends (prefixWord ++ tailWord_740606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740620 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_740620 : Nat := 118140960795 + 740620 * 2 ^ 59
def prefixEnd_740620 : Nat := 4983230072969 + 3 ^ 40 * 740620 * 2
def baseEnd_740620 : Nat := 338039148740442270705739

theorem tailTrace_740620 : CollatzResearch.WordTrace tailWord_740620 prefixEnd_740620 338039148740442270705739 := by
  unfold tailWord_740620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506315288433851335449657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18008420384578468447266209 13506315288433851335449657)
  ·
    refine ⟨10129736466325388501587243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13506315288433851335449657 10129736466325388501587243)
    ·
      refine ⟨15194604699488082752380865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10129736466325388501587243 15194604699488082752380865)
      ·
        refine ⟨11395953524616062064285649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15194604699488082752380865 11395953524616062064285649)
        ·
          refine ⟨8546965143462046548214237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11395953524616062064285649 8546965143462046548214237)
          ·
            refine ⟨3205111928798267455580339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8546965143462046548214237 3205111928798267455580339)
            ·
              refine ⟨4807667893197401183370509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205111928798267455580339 4807667893197401183370509)
              ·
                refine ⟨1802875459949025443763941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4807667893197401183370509 1802875459949025443763941)
                ·
                  refine ⟨338039148740442270705739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802875459949025443763941 338039148740442270705739)
                  ·
                    rfl

theorem cell20_740620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_740620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740620 prefixEnd_740620 := by exact prefixLift 740620
  have htrace : WordTrace (prefixWord ++ tailWord_740620) baseStart_740620 baseEnd_740620 := by
    simpa [prefixWord, tailWord_740620, baseEnd_740620] using wordTrace_append hprefix tailTrace_740620
  have hstable : (prefixWord ++ tailWord_740620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740620).length < 2 ^ (prefixWord ++ tailWord_740620).sum := by decide
  have hdescent : baseEnd_740620 < baseStart_740620 := by decide
  rcases family_descends (prefixWord ++ tailWord_740620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740637 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_740637 : Nat := 118140960795 + 740637 * 2 ^ 59
def prefixEnd_740637 : Nat := 4983230072969 + 3 ^ 40 * 740637 * 2
def baseEnd_740637 : Nat := 338046908003665767139003

theorem tailTrace_740637 : CollatzResearch.WordTrace tailWord_740637 prefixEnd_740637 338046908003665767139003 := by
  unfold tailWord_740637
  simp only [CollatzResearch.WordTrace]
  refine ⟨27013250617806114574268165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18008833745204076382845443 27013250617806114574268165)
  ·
    refine ⟨5064984490838646482675281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27013250617806114574268165 5064984490838646482675281)
    ·
      refine ⟨3798738368128984862006461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5064984490838646482675281 3798738368128984862006461)
      ·
        refine ⟨1424526888048369323252423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3798738368128984862006461 1424526888048369323252423)
        ·
          refine ⟨2136790332072553984878635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424526888048369323252423 2136790332072553984878635)
          ·
            refine ⟨3205185498108830977317953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136790332072553984878635 3205185498108830977317953)
            ·
              refine ⟨2403889123581623232988465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205185498108830977317953 2403889123581623232988465)
              ·
                refine ⟨1802916842686217424741349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403889123581623232988465 1802916842686217424741349)
                ·
                  refine ⟨338046908003665767139003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1802916842686217424741349 338046908003665767139003)
                  ·
                    rfl

theorem cell20_740637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_740637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740637 prefixEnd_740637 := by exact prefixLift 740637
  have htrace : WordTrace (prefixWord ++ tailWord_740637) baseStart_740637 baseEnd_740637 := by
    simpa [prefixWord, tailWord_740637, baseEnd_740637] using wordTrace_append hprefix tailTrace_740637
  have hstable : (prefixWord ++ tailWord_740637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740637).length < 2 ^ (prefixWord ++ tailWord_740637).sum := by decide
  have hdescent : baseEnd_740637 < baseStart_740637 := by decide
  rcases family_descends (prefixWord ++ tailWord_740637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740640 : List Nat := [2, 1, 1, 5, 4, 1, 2, 4]
def baseStart_740640 : Nat := 118140960795 + 740640 * 2 ^ 59
def prefixEnd_740640 : Nat := 4983230072969 + 3 ^ 40 * 740640 * 2
def baseEnd_740640 : Nat := 112682759095137030012997

theorem tailTrace_740640 : CollatzResearch.WordTrace tailWord_740640 prefixEnd_740640 112682759095137030012997 := by
  unfold tailWord_740640
  simp only [CollatzResearch.WordTrace]
  refine ⟨13506680018397623043313687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18008906691196830724418249 13506680018397623043313687)
  ·
    refine ⟨20260020027596434564970531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13506680018397623043313687 20260020027596434564970531)
    ·
      refine ⟨30390030041394651847455797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20260020027596434564970531 30390030041394651847455797)
      ·
        refine ⟨2849065316380748610698981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30390030041394651847455797 2849065316380748610698981)
        ·
          refine ⟨534199746821390364506059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2849065316380748610698981 534199746821390364506059)
          ·
            refine ⟨801299620232085546759089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 534199746821390364506059 801299620232085546759089)
            ·
              refine ⟨600974715174064160069317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 801299620232085546759089 600974715174064160069317)
              ·
                refine ⟨112682759095137030012997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600974715174064160069317 112682759095137030012997)
                ·
                  rfl

theorem cell20_740640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 4].length) (baseStart_740640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740640 prefixEnd_740640 := by exact prefixLift 740640
  have htrace : WordTrace (prefixWord ++ tailWord_740640) baseStart_740640 baseEnd_740640 := by
    simpa [prefixWord, tailWord_740640, baseEnd_740640] using wordTrace_append hprefix tailTrace_740640
  have hstable : (prefixWord ++ tailWord_740640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740640).length < 2 ^ (prefixWord ++ tailWord_740640).sum := by decide
  have hdescent : baseEnd_740640 < baseStart_740640 := by decide
  rcases family_descends (prefixWord ++ tailWord_740640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740672 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_740672 : Nat := 118140960795 + 740672 * 2 ^ 59
def prefixEnd_740672 : Nat := 4983230072969 + 3 ^ 40 * 740672 * 2
def baseEnd_740672 : Nat := 338062882957361200972193

theorem tailTrace_740672 : CollatzResearch.WordTrace tailWord_740672 prefixEnd_740672 338062882957361200972193 := by
  unfold tailWord_740672
  simp only [CollatzResearch.WordTrace]
  refine ⟨13507263586339657775896135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18009684781786210367861513 13507263586339657775896135)
  ·
    refine ⟨20260895379509486663844203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13507263586339657775896135 20260895379509486663844203)
    ·
      refine ⟨30391343069264229995766305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20260895379509486663844203 30391343069264229995766305)
      ·
        refine ⟨22793507301948172496824729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30391343069264229995766305 22793507301948172496824729)
        ·
          refine ⟨17095130476461129372618547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22793507301948172496824729 17095130476461129372618547)
          ·
            refine ⟨25642695714691694058927821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17095130476461129372618547 25642695714691694058927821)
            ·
              refine ⟨9616010893009385272097933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25642695714691694058927821 9616010893009385272097933)
              ·
                refine ⟨3606004084878519477036725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9616010893009385272097933 3606004084878519477036725)
                ·
                  refine ⟨338062882957361200972193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3606004084878519477036725 338062882957361200972193)
                  ·
                    rfl

theorem cell20_740672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_740672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740672 prefixEnd_740672 := by exact prefixLift 740672
  have htrace : WordTrace (prefixWord ++ tailWord_740672) baseStart_740672 baseEnd_740672 := by
    simpa [prefixWord, tailWord_740672, baseEnd_740672] using wordTrace_append hprefix tailTrace_740672
  have hstable : (prefixWord ++ tailWord_740672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740672).length < 2 ^ (prefixWord ++ tailWord_740672).sum := by decide
  have hdescent : baseEnd_740672 < baseStart_740672 := by decide
  rcases family_descends (prefixWord ++ tailWord_740672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740689 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 3]
def baseStart_740689 : Nat := 118140960795 + 740689 * 2 ^ 59
def prefixEnd_740689 : Nat := 4983230072969 + 3 ^ 40 * 740689 * 2
def baseEnd_740689 : Nat := 338070642220584697405457

theorem tailTrace_740689 : CollatzResearch.WordTrace tailWord_740689 prefixEnd_740689 338070642220584697405457 := by
  unfold tailWord_740689
  simp only [CollatzResearch.WordTrace]
  refine ⟨27015147213617727455161121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18010098142411818303440747 27015147213617727455161121)
  ·
    refine ⟨20261360410213295591370841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27015147213617727455161121 20261360410213295591370841)
    ·
      refine ⟨15196020307659971693528131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20261360410213295591370841 15196020307659971693528131)
      ·
        refine ⟨22794030461489957540292197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15196020307659971693528131 22794030461489957540292197)
        ·
          refine ⟨4273880711529367038804787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22794030461489957540292197 4273880711529367038804787)
          ·
            refine ⟨6410821067294050558207181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273880711529367038804787 6410821067294050558207181)
            ·
              refine ⟨2404057900235268959327693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6410821067294050558207181 2404057900235268959327693)
              ·
                refine ⟨901521712588225859747885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2404057900235268959327693 901521712588225859747885)
                ·
                  refine ⟨338070642220584697405457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901521712588225859747885 338070642220584697405457)
                  ·
                    rfl

theorem cell20_740689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 3].length) (baseStart_740689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740689 prefixEnd_740689 := by exact prefixLift 740689
  have htrace : WordTrace (prefixWord ++ tailWord_740689) baseStart_740689 baseEnd_740689 := by
    simpa [prefixWord, tailWord_740689, baseEnd_740689] using wordTrace_append hprefix tailTrace_740689
  have hstable : (prefixWord ++ tailWord_740689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740689).length < 2 ^ (prefixWord ++ tailWord_740689).sum := by decide
  have hdescent : baseEnd_740689 < baseStart_740689 := by decide
  rcases family_descends (prefixWord ++ tailWord_740689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740727 : List Nat := [1, 1, 3, 1, 1, 2, 6, 2, 3]
def baseStart_740727 : Nat := 118140960795 + 740727 * 2 ^ 59
def prefixEnd_740727 : Nat := 4983230072969 + 3 ^ 40 * 740727 * 2
def baseEnd_740727 : Nat := 338087986456025454138635

theorem tailTrace_740727 : CollatzResearch.WordTrace tailWord_740727 prefixEnd_740727 338087986456025454138635 := by
  unfold tailWord_740727
  simp only [CollatzResearch.WordTrace]
  refine ⟨27016533187480059945044435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18011022124986706630029623 27016533187480059945044435)
  ·
    refine ⟨40524799781220089917566653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27016533187480059945044435 40524799781220089917566653)
    ·
      refine ⟨15196799917957533719087495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40524799781220089917566653 15196799917957533719087495)
      ·
        refine ⟨22795199876936300578631243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15196799917957533719087495 22795199876936300578631243)
        ·
          refine ⟨34192799815404450867946865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22795199876936300578631243 34192799815404450867946865)
          ·
            refine ⟨25644599861553338150960149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34192799815404450867946865 25644599861553338150960149)
            ·
              refine ⟨1202090618510312725826257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25644599861553338150960149 1202090618510312725826257)
              ·
                refine ⟨901567963882734544369693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1202090618510312725826257 901567963882734544369693)
                ·
                  refine ⟨338087986456025454138635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 901567963882734544369693 338087986456025454138635)
                  ·
                    rfl

theorem cell20_740727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_740727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740727 prefixEnd_740727 := by exact prefixLift 740727
  have htrace : WordTrace (prefixWord ++ tailWord_740727) baseStart_740727 baseEnd_740727 := by
    simpa [prefixWord, tailWord_740727, baseEnd_740727] using wordTrace_append hprefix tailTrace_740727
  have hstable : (prefixWord ++ tailWord_740727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740727).length < 2 ^ (prefixWord ++ tailWord_740727).sum := by decide
  have hdescent : baseEnd_740727 < baseStart_740727 := by decide
  rcases family_descends (prefixWord ++ tailWord_740727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740737 : List Nat := [1, 2, 4, 3, 2, 2, 1, 5]
def baseStart_740737 : Nat := 118140960795 + 740737 * 2 ^ 59
def prefixEnd_740737 : Nat := 4983230072969 + 3 ^ 40 * 740737 * 2
def baseEnd_740737 : Nat := 112697516909503287935087

theorem tailTrace_740737 : CollatzResearch.WordTrace tailWord_740737 prefixEnd_740737 112697516909503287935087 := by
  unfold tailWord_740737
  simp only [CollatzResearch.WordTrace]
  refine ⟨27016897917443831652908465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18011265278295887768605643 27016897917443831652908465)
  ·
    refine ⟨20262673438082873739681349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27016897917443831652908465 20262673438082873739681349)
    ·
      refine ⟨3799251269640538826190253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20262673438082873739681349 3799251269640538826190253)
      ·
        refine ⟨1424719226115202059821345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3799251269640538826190253 1424719226115202059821345)
        ·
          refine ⟨1068539419586401544866009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1424719226115202059821345 1068539419586401544866009)
          ·
            refine ⟨801404564689801158649507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1068539419586401544866009 801404564689801158649507)
            ·
              refine ⟨1202106847034701737974261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 801404564689801158649507 1202106847034701737974261)
              ·
                refine ⟨112697516909503287935087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1202106847034701737974261 112697516909503287935087)
                ·
                  rfl

theorem cell20_740737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_740737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740737 prefixEnd_740737 := by exact prefixLift 740737
  have htrace : WordTrace (prefixWord ++ tailWord_740737) baseStart_740737 baseEnd_740737 := by
    simpa [prefixWord, tailWord_740737, baseEnd_740737] using wordTrace_append hprefix tailTrace_740737
  have hstable : (prefixWord ++ tailWord_740737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740737).length < 2 ^ (prefixWord ++ tailWord_740737).sum := by decide
  have hdescent : baseEnd_740737 < baseStart_740737 := by decide
  rcases family_descends (prefixWord ++ tailWord_740737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740741 : List Nat := [1, 3, 1, 1, 3, 1, 5, 5]
def baseStart_740741 : Nat := 118140960795 + 740741 * 2 ^ 59
def prefixEnd_740741 : Nat := 4983230072969 + 3 ^ 40 * 740741 * 2
def baseEnd_740741 : Nat := 112698125479167875890637

theorem tailTrace_740741 : CollatzResearch.WordTrace tailWord_740741 prefixEnd_740741 112698125479167875890637 := by
  unfold tailWord_740741
  simp only [CollatzResearch.WordTrace]
  refine ⟨27017043809429340336054077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18011362539619560224036051 27017043809429340336054077)
  ·
    refine ⟨10131391428536002626020279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27017043809429340336054077 10131391428536002626020279)
    ·
      refine ⟨15197087142804003939030419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10131391428536002626020279 15197087142804003939030419)
      ·
        refine ⟨22795630714206005908545629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15197087142804003939030419 22795630714206005908545629)
        ·
          refine ⟨8548361517827252215704611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22795630714206005908545629 8548361517827252215704611)
          ·
            refine ⟨12822542276740878323556917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8548361517827252215704611 12822542276740878323556917)
            ·
              refine ⟨1202113338444457342833461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12822542276740878323556917 1202113338444457342833461)
              ·
                refine ⟨112698125479167875890637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1202113338444457342833461 112698125479167875890637)
                ·
                  rfl

theorem cell20_740741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_740741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740741 prefixEnd_740741 := by exact prefixLift 740741
  have htrace : WordTrace (prefixWord ++ tailWord_740741) baseStart_740741 baseEnd_740741 := by
    simpa [prefixWord, tailWord_740741, baseEnd_740741] using wordTrace_append hprefix tailTrace_740741
  have hstable : (prefixWord ++ tailWord_740741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740741).length < 2 ^ (prefixWord ++ tailWord_740741).sum := by decide
  have hdescent : baseEnd_740741 < baseStart_740741 := by decide
  rcases family_descends (prefixWord ++ tailWord_740741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740754 : List Nat := [3, 2, 3, 3, 1, 1, 3, 4]
def baseStart_740754 : Nat := 118140960795 + 740754 * 2 ^ 59
def prefixEnd_740754 : Nat := 4983230072969 + 3 ^ 40 * 740754 * 2
def baseEnd_740754 : Nat := 112700103330577786746175

theorem tailTrace_740754 : CollatzResearch.WordTrace tailWord_740754 prefixEnd_740754 112700103330577786746175 := by
  unfold tailWord_740754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754379489595560889069329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18011678638921495704184877 6754379489595560889069329)
  ·
    refine ⟨5065784617196670666801997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6754379489595560889069329 5065784617196670666801997)
    ·
      refine ⟨1899669231448751500050749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5065784617196670666801997 1899669231448751500050749)
      ·
        refine ⟨712375961793281812519031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1899669231448751500050749 712375961793281812519031)
        ·
          refine ⟨1068563942689922718778547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 712375961793281812519031 1068563942689922718778547)
          ·
            refine ⟨1602845914034884078167821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1068563942689922718778547 1602845914034884078167821)
            ·
              refine ⟨601067217763081529312933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1602845914034884078167821 601067217763081529312933)
              ·
                refine ⟨112700103330577786746175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 601067217763081529312933 112700103330577786746175)
                ·
                  rfl

theorem cell20_740754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_740754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740754 prefixEnd_740754 := by exact prefixLift 740754
  have htrace : WordTrace (prefixWord ++ tailWord_740754) baseStart_740754 baseEnd_740754 := by
    simpa [prefixWord, tailWord_740754, baseEnd_740754] using wordTrace_append hprefix tailTrace_740754
  have hstable : (prefixWord ++ tailWord_740754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740754).length < 2 ^ (prefixWord ++ tailWord_740754).sum := by decide
  have hdescent : baseEnd_740754 < baseStart_740754 := by decide
  rcases family_descends (prefixWord ++ tailWord_740754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740789 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_740789 : Nat := 118140960795 + 740789 * 2 ^ 59
def prefixEnd_740789 : Nat := 4983230072969 + 3 ^ 40 * 740789 * 2
def baseEnd_740789 : Nat := 338116284945428794071715

theorem tailTrace_740789 : CollatzResearch.WordTrace tailWord_740789 prefixEnd_740789 338116284945428794071715 := by
  unfold tailWord_740789
  simp only [CollatzResearch.WordTrace]
  refine ⟨27018794513255444533801421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18012529675503629689200947 27018794513255444533801421)
  ·
    refine ⟨10132047942470791700175533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27018794513255444533801421 10132047942470791700175533)
    ·
      refine ⟨3799517978426546887565825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10132047942470791700175533 3799517978426546887565825)
      ·
        refine ⟨2849638483819910165674369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3799517978426546887565825 2849638483819910165674369)
        ·
          refine ⟨2137228862864932624255777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2849638483819910165674369 2137228862864932624255777)
          ·
            refine ⟨1602921647148699468191833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2137228862864932624255777 1602921647148699468191833)
            ·
              refine ⟨1202191235361524601143875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1602921647148699468191833 1202191235361524601143875)
              ·
                refine ⟨1803286853042286901715813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202191235361524601143875 1803286853042286901715813)
                ·
                  refine ⟨338116284945428794071715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803286853042286901715813 338116284945428794071715)
                  ·
                    rfl

theorem cell20_740789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_740789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740789 prefixEnd_740789 := by exact prefixLift 740789
  have htrace : WordTrace (prefixWord ++ tailWord_740789) baseStart_740789 baseEnd_740789 := by
    simpa [prefixWord, tailWord_740789, baseEnd_740789] using wordTrace_append hprefix tailTrace_740789
  have hstable : (prefixWord ++ tailWord_740789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740789).length < 2 ^ (prefixWord ++ tailWord_740789).sum := by decide
  have hdescent : baseEnd_740789 < baseStart_740789 := by decide
  rcases family_descends (prefixWord ++ tailWord_740789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740810 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_740810 : Nat := 118140960795 + 740810 * 2 ^ 59
def prefixEnd_740810 : Nat := 4983230072969 + 3 ^ 40 * 740810 * 2
def baseEnd_740810 : Nat := 338125869917646054371629

theorem tailTrace_740810 : CollatzResearch.WordTrace tailWord_740810 prefixEnd_740810 338125869917646054371629 := by
  unfold tailWord_740810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6754890111544841280078971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 18013040297452910080210589 6754890111544841280078971)
  ·
    refine ⟨10132335167317261920118457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6754890111544841280078971 10132335167317261920118457)
    ·
      refine ⟨7599251375487946440088843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10132335167317261920118457 7599251375487946440088843)
      ·
        refine ⟨11398877063231919660133265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7599251375487946440088843 11398877063231919660133265)
        ·
          refine ⟨8549157797423939745099949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11398877063231919660133265 8549157797423939745099949)
          ·
            refine ⟨3205934174033977404412481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8549157797423939745099949 3205934174033977404412481)
            ·
              refine ⟨2404450630525483053309361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205934174033977404412481 2404450630525483053309361)
              ·
                refine ⟨1803337972894112289982021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2404450630525483053309361 1803337972894112289982021)
                ·
                  refine ⟨338125869917646054371629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803337972894112289982021 338125869917646054371629)
                  ·
                    rfl

theorem cell20_740810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_740810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740810 prefixEnd_740810 := by exact prefixLift 740810
  have htrace : WordTrace (prefixWord ++ tailWord_740810) baseStart_740810 baseEnd_740810 := by
    simpa [prefixWord, tailWord_740810, baseEnd_740810] using wordTrace_append hprefix tailTrace_740810
  have hstable : (prefixWord ++ tailWord_740810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740810).length < 2 ^ (prefixWord ++ tailWord_740810).sum := by decide
  have hdescent : baseEnd_740810 < baseStart_740810 := by decide
  rcases family_descends (prefixWord ++ tailWord_740810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740824 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_740824 : Nat := 118140960795 + 740824 * 2 ^ 59
def prefixEnd_740824 : Nat := 4983230072969 + 3 ^ 40 * 740824 * 2
def baseEnd_740824 : Nat := 338132259899124227904905

theorem tailTrace_740824 : CollatzResearch.WordTrace tailWord_740824 prefixEnd_740824 338132259899124227904905 := by
  unfold tailWord_740824
  simp only [CollatzResearch.WordTrace]
  refine ⟨13510035534064322755662763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18013380712085763674217017 13510035534064322755662763)
  ·
    refine ⟨20265053301096484133494145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13510035534064322755662763 20265053301096484133494145)
    ·
      refine ⟨15198789975822363100120609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20265053301096484133494145 15198789975822363100120609)
      ·
        refine ⟨11399092481866772325090457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15198789975822363100120609 11399092481866772325090457)
        ·
          refine ⟨8549319361400079243817843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11399092481866772325090457 8549319361400079243817843)
          ·
            refine ⟨12823979042100118865726765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549319361400079243817843 12823979042100118865726765)
            ·
              refine ⟨4808992140787544574647537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12823979042100118865726765 4808992140787544574647537)
              ·
                refine ⟨3606744105590658430985653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4808992140787544574647537 3606744105590658430985653)
                ·
                  refine ⟨338132259899124227904905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3606744105590658430985653 338132259899124227904905)
                  ·
                    rfl

theorem cell20_740824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_740824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740824 prefixEnd_740824 := by exact prefixLift 740824
  have htrace : WordTrace (prefixWord ++ tailWord_740824) baseStart_740824 baseEnd_740824 := by
    simpa [prefixWord, tailWord_740824, baseEnd_740824] using wordTrace_append hprefix tailTrace_740824
  have hstable : (prefixWord ++ tailWord_740824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740824).length < 2 ^ (prefixWord ++ tailWord_740824).sum := by decide
  have hdescent : baseEnd_740824 < baseStart_740824 := by decide
  rcases family_descends (prefixWord ++ tailWord_740824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740848 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_740848 : Nat := 118140960795 + 740848 * 2 ^ 59
def prefixEnd_740848 : Nat := 4983230072969 + 3 ^ 40 * 740848 * 2
def baseEnd_740848 : Nat := 338143214153086811104807

theorem tailTrace_740848 : CollatzResearch.WordTrace tailWord_740848 prefixEnd_740848 338143214153086811104807 := by
  unfold tailWord_740848
  simp only [CollatzResearch.WordTrace]
  refine ⟨13510473210020848805099599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 18013964280027798406799465 13510473210020848805099599)
  ·
    refine ⟨20265709815031273207649399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13510473210020848805099599 20265709815031273207649399)
    ·
      refine ⟨30398564722546909811474099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20265709815031273207649399 30398564722546909811474099)
      ·
        refine ⟨45597847083820364717211149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30398564722546909811474099 45597847083820364717211149)
        ·
          refine ⟨17099192656432636768954181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45597847083820364717211149 17099192656432636768954181)
          ·
            refine ⟨3206098623081119394178909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17099192656432636768954181 3206098623081119394178909)
            ·
              refine ⟨1202286983655419772817091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3206098623081119394178909 1202286983655419772817091)
              ·
                refine ⟨1803430475483129659225637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1202286983655419772817091 1803430475483129659225637)
                ·
                  refine ⟨338143214153086811104807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1803430475483129659225637 338143214153086811104807)
                  ·
                    rfl

theorem cell20_740848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_740848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740848 prefixEnd_740848 := by exact prefixLift 740848
  have htrace : WordTrace (prefixWord ++ tailWord_740848) baseStart_740848 baseEnd_740848 := by
    simpa [prefixWord, tailWord_740848, baseEnd_740848] using wordTrace_append hprefix tailTrace_740848
  have hstable : (prefixWord ++ tailWord_740848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740848).length < 2 ^ (prefixWord ++ tailWord_740848).sum := by decide
  have hdescent : baseEnd_740848 < baseStart_740848 := by decide
  rcases family_descends (prefixWord ++ tailWord_740848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_740869 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 6]
def baseStart_740869 : Nat := 118140960795 + 740869 * 2 ^ 59
def prefixEnd_740869 : Nat := 4983230072969 + 3 ^ 40 * 740869 * 2
def baseEnd_740869 : Nat := 338152799125304071404721

theorem tailTrace_740869 : CollatzResearch.WordTrace tailWord_740869 prefixEnd_740869 338152799125304071404721 := by
  unfold tailWord_740869
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021712352965618196713661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 18014474901977078797809107 27021712352965618196713661)
  ·
    refine ⟨10133142132362106823767623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27021712352965618196713661 10133142132362106823767623)
    ·
      refine ⟨15199713198543160235651435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10133142132362106823767623 15199713198543160235651435)
      ·
        refine ⟨22799569797814740353477153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15199713198543160235651435 22799569797814740353477153)
        ·
          refine ⟨17099677348361055265107865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22799569797814740353477153 17099677348361055265107865)
          ·
            refine ⟨12824758011270791448830899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17099677348361055265107865 12824758011270791448830899)
            ·
              refine ⟨19237137016906187173246349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12824758011270791448830899 19237137016906187173246349)
              ·
                refine ⟨7213926381339820189967381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19237137016906187173246349 7213926381339820189967381)
                ·
                  refine ⟨338152799125304071404721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7213926381339820189967381 338152799125304071404721)
                  ·
                    rfl

theorem cell20_740869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_740869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_740869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_740869 prefixEnd_740869 := by exact prefixLift 740869
  have htrace : WordTrace (prefixWord ++ tailWord_740869) baseStart_740869 baseEnd_740869 := by
    simpa [prefixWord, tailWord_740869, baseEnd_740869] using wordTrace_append hprefix tailTrace_740869
  have hstable : (prefixWord ++ tailWord_740869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_740869).length < 2 ^ (prefixWord ++ tailWord_740869).sum := by decide
  have hdescent : baseEnd_740869 < baseStart_740869 := by decide
  rcases family_descends (prefixWord ++ tailWord_740869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
