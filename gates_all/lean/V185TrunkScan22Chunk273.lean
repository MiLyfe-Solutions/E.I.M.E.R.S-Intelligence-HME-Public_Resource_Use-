import V185TrunkScan22Chunk272

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2434290 : List Nat := [3, 2, 1, 3, 3, 2, 2, 2, 4]
def baseStart_2434290 : Nat := 118140960795 + 2434290 * 2 ^ 59
def prefixEnd_2434290 : Nat := 4983230072969 + 3 ^ 40 * 2434290 * 2
def baseEnd_2434290 : Nat := 277769071651863569528869

theorem tailTrace_2434290 : CollatzResearch.WordTrace tailWord_2434290 prefixEnd_2434290 277769071651863569528869 := by
  unfold tailWord_2434290
  simp only [CollatzResearch.WordTrace]
  refine ⟨22196462587747637119517081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59190566900660365652045549 22196462587747637119517081)
  ·
    refine ⟨16647346940810727839637811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22196462587747637119517081 16647346940810727839637811)
    ·
      refine ⟨24971020411216091759456717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16647346940810727839637811 24971020411216091759456717)
      ·
        refine ⟨9364132654206034409796269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24971020411216091759456717 9364132654206034409796269)
        ·
          refine ⟨3511549745327262903673601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9364132654206034409796269 3511549745327262903673601)
          ·
            refine ⟨2633662308995447177755201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511549745327262903673601 2633662308995447177755201)
            ·
              refine ⟨1975246731746585383316401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2633662308995447177755201 1975246731746585383316401)
              ·
                refine ⟨1481435048809939037487301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975246731746585383316401 1481435048809939037487301)
                ·
                  refine ⟨277769071651863569528869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481435048809939037487301 277769071651863569528869)
                  ·
                    rfl

theorem cell22_2434290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_2434290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434290 prefixEnd_2434290 := by exact prefixLift 2434290
  have htrace : WordTrace (prefixWord ++ tailWord_2434290) baseStart_2434290 baseEnd_2434290 := by
    simpa [prefixWord, tailWord_2434290, baseEnd_2434290] using wordTrace_append hprefix tailTrace_2434290
  have hstable : (prefixWord ++ tailWord_2434290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434290).length < 2 ^ (prefixWord ++ tailWord_2434290).sum := by decide
  have hdescent : baseEnd_2434290 < baseStart_2434290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434297 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_2434297 : Nat := 118140960795 + 2434297 * 2 ^ 59
def prefixEnd_2434297 : Nat := 4983230072969 + 3 ^ 40 * 2434297 * 2
def baseEnd_2434297 : Nat := 833309611198645023661585

theorem tailTrace_2434297 : CollatzResearch.WordTrace tailWord_2434297 prefixEnd_2434297 833309611198645023661585 := by
  unfold tailWord_2434297
  simp only [CollatzResearch.WordTrace]
  refine ⟨88786105661965188673573145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59190737107976792449048763 88786105661965188673573145)
  ·
    refine ⟨66589579246473891505179859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88786105661965188673573145 66589579246473891505179859)
    ·
      refine ⟨99884368869710837257769789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66589579246473891505179859 99884368869710837257769789)
      ·
        refine ⟨37456638326141563971663671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99884368869710837257769789 37456638326141563971663671)
        ·
          refine ⟨56184957489212345957495507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37456638326141563971663671 56184957489212345957495507)
          ·
            refine ⟨84277436233818518936243261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56184957489212345957495507 84277436233818518936243261)
            ·
              refine ⟨31604038587681944601091223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84277436233818518936243261 31604038587681944601091223)
              ·
                refine ⟨47406057881522916901636835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31604038587681944601091223 47406057881522916901636835)
                ·
                  refine ⟨71109086822284375352455253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47406057881522916901636835 71109086822284375352455253)
                  ·
                    refine ⟨833309611198645023661585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71109086822284375352455253 833309611198645023661585)
                    ·
                      rfl

theorem cell22_2434297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_2434297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434297 prefixEnd_2434297 := by exact prefixLift 2434297
  have htrace : WordTrace (prefixWord ++ tailWord_2434297) baseStart_2434297 baseEnd_2434297 := by
    simpa [prefixWord, tailWord_2434297, baseEnd_2434297] using wordTrace_append hprefix tailTrace_2434297
  have hstable : (prefixWord ++ tailWord_2434297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434297).length < 2 ^ (prefixWord ++ tailWord_2434297).sum := by decide
  have hdescent : baseEnd_2434297 < baseStart_2434297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434316 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 3, 3]
def baseStart_2434316 : Nat := 118140960795 + 2434316 * 2 ^ 59
def prefixEnd_2434316 : Nat := 4983230072969 + 3 ^ 40 * 2434316 * 2
def baseEnd_2434316 : Nat := 833316115286935307436527

theorem tailTrace_2434316 : CollatzResearch.WordTrace tailWord_2434316 prefixEnd_2434316 833316115286935307436527 := by
  unfold tailWord_2434316
  simp only [CollatzResearch.WordTrace]
  refine ⟨44393399324448177459257401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59191199099264236612343201 44393399324448177459257401)
  ·
    refine ⟨33295049493336133094443051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44393399324448177459257401 33295049493336133094443051)
    ·
      refine ⟨49942574240004199641664577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33295049493336133094443051 49942574240004199641664577)
      ·
        refine ⟨37456930680003149731248433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49942574240004199641664577 37456930680003149731248433)
        ·
          refine ⟨28092698010002362298436325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37456930680003149731248433 28092698010002362298436325)
          ·
            refine ⟨5267380876875442930956811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28092698010002362298436325 5267380876875442930956811)
            ·
              refine ⟨7901071315313164396435217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267380876875442930956811 7901071315313164396435217)
              ·
                refine ⟨5925803486484873297326413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7901071315313164396435217 5925803486484873297326413)
                ·
                  refine ⟨2222176307431827486497405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5925803486484873297326413 2222176307431827486497405)
                  ·
                    refine ⟨833316115286935307436527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222176307431827486497405 833316115286935307436527)
                    ·
                      rfl

theorem cell22_2434316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_2434316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434316 prefixEnd_2434316 := by exact prefixLift 2434316
  have htrace : WordTrace (prefixWord ++ tailWord_2434316) baseStart_2434316 baseEnd_2434316 := by
    simpa [prefixWord, tailWord_2434316, baseEnd_2434316] using wordTrace_append hprefix tailTrace_2434316
  have hstable : (prefixWord ++ tailWord_2434316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434316).length < 2 ^ (prefixWord ++ tailWord_2434316).sum := by decide
  have hdescent : baseEnd_2434316 < baseStart_2434316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434346 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 7]
def baseStart_2434346 : Nat := 118140960795 + 2434346 * 2 ^ 59
def prefixEnd_2434346 : Nat := 4983230072969 + 3 ^ 40 * 2434346 * 2
def baseEnd_2434346 : Nat := 277775461633341743062145

theorem tailTrace_2434346 : CollatzResearch.WordTrace tailWord_2434346 prefixEnd_2434346 277775461633341743062145 := by
  unfold tailWord_2434346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22196973209696917510526723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59191928559191780028071261 22196973209696917510526723)
  ·
    refine ⟨33295459814545376265790085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22196973209696917510526723 33295459814545376265790085)
    ·
      refine ⟨6242898715227258049835641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33295459814545376265790085 6242898715227258049835641)
      ·
        refine ⟨4682174036420443537376731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6242898715227258049835641 4682174036420443537376731)
        ·
          refine ⟨7023261054630665306065097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4682174036420443537376731 7023261054630665306065097)
          ·
            refine ⟨5267445790972998979548823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7023261054630665306065097 5267445790972998979548823)
            ·
              refine ⟨7901168686459498469323235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267445790972998979548823 7901168686459498469323235)
              ·
                refine ⟨11851753029689247703984853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7901168686459498469323235 11851753029689247703984853)
                ·
                  refine ⟨277775461633341743062145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11851753029689247703984853 277775461633341743062145)
                  ·
                    rfl

theorem cell22_2434346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_2434346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434346 prefixEnd_2434346 := by exact prefixLift 2434346
  have htrace : WordTrace (prefixWord ++ tailWord_2434346) baseStart_2434346 baseEnd_2434346 := by
    simpa [prefixWord, tailWord_2434346, baseEnd_2434346] using wordTrace_append hprefix tailTrace_2434346
  have hstable : (prefixWord ++ tailWord_2434346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434346).length < 2 ^ (prefixWord ++ tailWord_2434346).sum := by decide
  have hdescent : baseEnd_2434346 < baseStart_2434346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434408 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 6]
def baseStart_2434408 : Nat := 118140960795 + 2434408 * 2 ^ 59
def prefixEnd_2434408 : Nat := 4983230072969 + 3 ^ 40 * 2434408 * 2
def baseEnd_2434408 : Nat := 277782536255692578045415

theorem tailTrace_2434408 : CollatzResearch.WordTrace tailWord_2434408 prefixEnd_2434408 277782536255692578045415 := by
  unfold tailWord_2434408
  simp only [CollatzResearch.WordTrace]
  refine ⟨44395077082281527315431939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59193436109708703087242585 44395077082281527315431939)
  ·
    refine ⟨66592615623422290973147909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44395077082281527315431939 66592615623422290973147909)
    ·
      refine ⟨12486115429391679557465233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66592615623422290973147909 12486115429391679557465233)
      ·
        refine ⟨9364586572043759668098925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12486115429391679557465233 9364586572043759668098925)
        ·
          refine ⟨3511719964516409875537097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9364586572043759668098925 3511719964516409875537097)
          ·
            refine ⟨2633789973387307406652823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511719964516409875537097 2633789973387307406652823)
            ·
              refine ⟨3950684960080961109979235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633789973387307406652823 3950684960080961109979235)
              ·
                refine ⟨5926027440121441664968853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950684960080961109979235 5926027440121441664968853)
                ·
                  refine ⟨277782536255692578045415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5926027440121441664968853 277782536255692578045415)
                  ·
                    rfl

theorem cell22_2434408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 6].length) (baseStart_2434408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434408 prefixEnd_2434408 := by exact prefixLift 2434408
  have htrace : WordTrace (prefixWord ++ tailWord_2434408) baseStart_2434408 baseEnd_2434408 := by
    simpa [prefixWord, tailWord_2434408, baseEnd_2434408] using wordTrace_append hprefix tailTrace_2434408
  have hstable : (prefixWord ++ tailWord_2434408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434408).length < 2 ^ (prefixWord ++ tailWord_2434408).sum := by decide
  have hdescent : baseEnd_2434408 < baseStart_2434408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434466 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2434466 : Nat := 118140960795 + 2434466 * 2 ^ 59
def prefixEnd_2434466 : Nat := 4983230072969 + 3 ^ 40 * 2434466 * 2
def baseEnd_2434466 : Nat := 833367463352384916186067

theorem tailTrace_2434466 : CollatzResearch.WordTrace tailWord_2434466 prefixEnd_2434466 833367463352384916186067 := by
  unfold tailWord_2434466
  simp only [CollatzResearch.WordTrace]
  refine ⟨22198067399588232634118813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59194846398901953690983501 22198067399588232634118813)
  ·
    refine ⟨8324275274845587237794555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22198067399588232634118813 8324275274845587237794555)
    ·
      refine ⟨12486412912268380856691833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8324275274845587237794555 12486412912268380856691833)
      ·
        refine ⟨9364809684201285642518875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12486412912268380856691833 9364809684201285642518875)
        ·
          refine ⟨14047214526301928463778313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9364809684201285642518875 14047214526301928463778313)
          ·
            refine ⟨10535410894726446347833735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14047214526301928463778313 10535410894726446347833735)
            ·
              refine ⟨15803116342089669521750603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10535410894726446347833735 15803116342089669521750603)
              ·
                refine ⟨23704674513134504282625905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15803116342089669521750603 23704674513134504282625905)
                ·
                  refine ⟨17778505884850878211969429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23704674513134504282625905 17778505884850878211969429)
                  ·
                    refine ⟨833367463352384916186067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17778505884850878211969429 833367463352384916186067)
                    ·
                      rfl

theorem cell22_2434466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2434466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434466 prefixEnd_2434466 := by exact prefixLift 2434466
  have htrace : WordTrace (prefixWord ++ tailWord_2434466) baseStart_2434466 baseEnd_2434466 := by
    simpa [prefixWord, tailWord_2434466, baseEnd_2434466] using wordTrace_append hprefix tailTrace_2434466
  have hstable : (prefixWord ++ tailWord_2434466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434466).length < 2 ^ (prefixWord ++ tailWord_2434466).sum := by decide
  have hdescent : baseEnd_2434466 < baseStart_2434466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434481 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 5]
def baseStart_2434481 : Nat := 118140960795 + 2434481 * 2 ^ 59
def prefixEnd_2434481 : Nat := 4983230072969 + 3 ^ 40 * 2434481 * 2
def baseEnd_2434481 : Nat := 277790866052976625687007

theorem tailTrace_2434481 : CollatzResearch.WordTrace tailWord_2434481 prefixEnd_2434481 277790866052976625687007 := by
  unfold tailWord_2434481
  simp only [CollatzResearch.WordTrace]
  refine ⟨88792816693298588098271297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59195211128865725398847531 88792816693298588098271297)
  ·
    refine ⟨66594612519973941073703473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88792816693298588098271297 66594612519973941073703473)
    ·
      refine ⟨49945959389980455805277605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66594612519973941073703473 49945959389980455805277605)
      ·
        refine ⟨9364867385621335463489551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49945959389980455805277605 9364867385621335463489551)
        ·
          refine ⟨14047301078432003195234327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9364867385621335463489551 14047301078432003195234327)
          ·
            refine ⟨21070951617648004792851491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14047301078432003195234327 21070951617648004792851491)
            ·
              refine ⟨31606427426472007189277237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21070951617648004792851491 31606427426472007189277237)
              ·
                refine ⟨2963102571231750673994741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31606427426472007189277237 2963102571231750673994741)
                ·
                  refine ⟨277790866052976625687007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2963102571231750673994741 277790866052976625687007)
                  ·
                    rfl

theorem cell22_2434481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_2434481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434481 prefixEnd_2434481 := by exact prefixLift 2434481
  have htrace : WordTrace (prefixWord ++ tailWord_2434481) baseStart_2434481 baseEnd_2434481 := by
    simpa [prefixWord, tailWord_2434481, baseEnd_2434481] using wordTrace_append hprefix tailTrace_2434481
  have hstable : (prefixWord ++ tailWord_2434481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434481).length < 2 ^ (prefixWord ++ tailWord_2434481).sum := by decide
  have hdescent : baseEnd_2434481 < baseStart_2434481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434556 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 1, 6]
def baseStart_2434556 : Nat := 118140960795 + 2434556 * 2 ^ 59
def prefixEnd_2434556 : Nat := 4983230072969 + 3 ^ 40 * 2434556 * 2
def baseEnd_2434556 : Nat := 833398272191654681435791

theorem tailTrace_2434556 : CollatzResearch.WordTrace tailWord_2434556 prefixEnd_2434556 833398272191654681435791 := by
  unfold tailWord_2434556
  simp only [CollatzResearch.WordTrace]
  refine ⟨44397776084013437953625761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59197034778684583938167681 44397776084013437953625761)
  ·
    refine ⟨33298332063010078465219321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44397776084013437953625761 33298332063010078465219321)
    ·
      refine ⟨24973749047257558848914491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33298332063010078465219321 24973749047257558848914491)
      ·
        refine ⟨37460623570886338273371737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24973749047257558848914491 37460623570886338273371737)
        ·
          refine ⟨28095467678164753705028803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37460623570886338273371737 28095467678164753705028803)
          ·
            refine ⟨42143201517247130557543205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28095467678164753705028803 42143201517247130557543205)
            ·
              refine ⟨7901850284483836979539351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42143201517247130557543205 7901850284483836979539351)
              ·
                refine ⟨11852775426725755469309027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7901850284483836979539351 11852775426725755469309027)
                ·
                  refine ⟨17779163140088633203963541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11852775426725755469309027 17779163140088633203963541)
                  ·
                    refine ⟨833398272191654681435791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17779163140088633203963541 833398272191654681435791)
                    ·
                      rfl

theorem cell22_2434556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_2434556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434556 prefixEnd_2434556 := by exact prefixLift 2434556
  have htrace : WordTrace (prefixWord ++ tailWord_2434556) baseStart_2434556 baseEnd_2434556 := by
    simpa [prefixWord, tailWord_2434556, baseEnd_2434556] using wordTrace_append hprefix tailTrace_2434556
  have hstable : (prefixWord ++ tailWord_2434556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434556).length < 2 ^ (prefixWord ++ tailWord_2434556).sum := by decide
  have hdescent : baseEnd_2434556 < baseStart_2434556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434592 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 2, 3]
def baseStart_2434592 : Nat := 118140960795 + 2434592 * 2 ^ 59
def prefixEnd_2434592 : Nat := 4983230072969 + 3 ^ 40 * 2434592 * 2
def baseEnd_2434592 : Nat := 833410595727362587535681

theorem tailTrace_2434592 : CollatzResearch.WordTrace tailWord_2434592 prefixEnd_2434592 833410595727362587535681 := by
  unfold tailWord_2434592
  simp only [CollatzResearch.WordTrace]
  refine ⟨44398432597948227027781015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59197910130597636037041353 44398432597948227027781015)
  ·
    refine ⟨66597648896922340541671523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44398432597948227027781015 66597648896922340541671523)
    ·
      refine ⟨99896473345383510812507285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66597648896922340541671523 99896473345383510812507285)
      ·
        refine ⟨4682647188064852069336279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99896473345383510812507285 4682647188064852069336279)
        ·
          refine ⟨7023970782097278104004419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4682647188064852069336279 7023970782097278104004419)
          ·
            refine ⟨10535956173145917156006629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7023970782097278104004419 10535956173145917156006629)
            ·
              refine ⟨1975491782464859466751243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10535956173145917156006629 1975491782464859466751243)
              ·
                refine ⟨2963237673697289200126865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975491782464859466751243 2963237673697289200126865)
                ·
                  refine ⟨2222428255272966900095149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2963237673697289200126865 2222428255272966900095149)
                  ·
                    refine ⟨833410595727362587535681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222428255272966900095149 833410595727362587535681)
                    ·
                      rfl

theorem cell22_2434592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 3].length) (baseStart_2434592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434592 prefixEnd_2434592 := by exact prefixLift 2434592
  have htrace : WordTrace (prefixWord ++ tailWord_2434592) baseStart_2434592 baseEnd_2434592 := by
    simpa [prefixWord, tailWord_2434592, baseEnd_2434592] using wordTrace_append hprefix tailTrace_2434592
  have hstable : (prefixWord ++ tailWord_2434592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434592).length < 2 ^ (prefixWord ++ tailWord_2434592).sum := by decide
  have hdescent : baseEnd_2434592 < baseStart_2434592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434663 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2434663 : Nat := 118140960795 + 2434663 * 2 ^ 59
def prefixEnd_2434663 : Nat := 4983230072969 + 3 ^ 40 * 2434663 * 2
def baseEnd_2434663 : Nat := 833434900478342069010463

theorem tailTrace_2434663 : CollatzResearch.WordTrace tailWord_2434663 prefixEnd_2434663 833434900478342069010463 := by
  unfold tailWord_2434663
  simp only [CollatzResearch.WordTrace]
  refine ⟨88799454778639233181396643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59199636519092822120931095 88799454778639233181396643)
  ·
    refine ⟨133199182167958849772094965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88799454778639233181396643 133199182167958849772094965)
    ·
      refine ⟨12487423328246142166133903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133199182167958849772094965 12487423328246142166133903)
      ·
        refine ⟨18731134992369213249200855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12487423328246142166133903 18731134992369213249200855)
        ·
          refine ⟨28096702488553819873801283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18731134992369213249200855 28096702488553819873801283)
          ·
            refine ⟨42145053732830729810701925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28096702488553819873801283 42145053732830729810701925)
            ·
              refine ⟨7902197574905761839506611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42145053732830729810701925 7902197574905761839506611)
              ·
                refine ⟨11853296362358642759259917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7902197574905761839506611 11853296362358642759259917)
                ·
                  refine ⟨4444986135884491034722469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11853296362358642759259917 4444986135884491034722469)
                  ·
                    refine ⟨833434900478342069010463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4444986135884491034722469 833434900478342069010463)
                    ·
                      rfl

theorem cell22_2434663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2434663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434663 prefixEnd_2434663 := by exact prefixLift 2434663
  have htrace : WordTrace (prefixWord ++ tailWord_2434663) baseStart_2434663 baseEnd_2434663 := by
    simpa [prefixWord, tailWord_2434663, baseEnd_2434663] using wordTrace_append hprefix tailTrace_2434663
  have hstable : (prefixWord ++ tailWord_2434663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434663).length < 2 ^ (prefixWord ++ tailWord_2434663).sum := by decide
  have hdescent : baseEnd_2434663 < baseStart_2434663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434695 : List Nat := [1, 1, 4, 2, 1, 3, 2, 4, 4]
def baseStart_2434695 : Nat := 118140960795 + 2434695 * 2 ^ 59
def prefixEnd_2434695 : Nat := 4983230072969 + 3 ^ 40 * 2434695 * 2
def baseEnd_2434695 : Nat := 277815284910768217403455

theorem tailTrace_2434695 : CollatzResearch.WordTrace tailWord_2434695 prefixEnd_2434695 277815284910768217403455 := by
  unfold tailWord_2434695
  simp only [CollatzResearch.WordTrace]
  refine ⟨88800621914523302646561539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59200414609682201764374359 88800621914523302646561539)
  ·
    refine ⟨133200932871784953969842309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88800621914523302646561539 133200932871784953969842309)
    ·
      refine ⟨24975174913459678869345433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133200932871784953969842309 24975174913459678869345433)
      ·
        refine ⟨18731381185094759152009075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24975174913459678869345433 18731381185094759152009075)
        ·
          refine ⟨28097071777642138728013613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18731381185094759152009075 28097071777642138728013613)
          ·
            refine ⟨10536401916615802023005105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28097071777642138728013613 10536401916615802023005105)
            ·
              refine ⟨7902301437461851517253829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10536401916615802023005105 7902301437461851517253829)
              ·
                refine ⟨1481681519524097159485093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7902301437461851517253829 1481681519524097159485093)
                ·
                  refine ⟨277815284910768217403455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481681519524097159485093 277815284910768217403455)
                  ·
                    rfl

theorem cell22_2434695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 4].length) (baseStart_2434695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434695 prefixEnd_2434695 := by exact prefixLift 2434695
  have htrace : WordTrace (prefixWord ++ tailWord_2434695) baseStart_2434695 baseEnd_2434695 := by
    simpa [prefixWord, tailWord_2434695, baseEnd_2434695] using wordTrace_append hprefix tailTrace_2434695
  have hstable : (prefixWord ++ tailWord_2434695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434695).length < 2 ^ (prefixWord ++ tailWord_2434695).sum := by decide
  have hdescent : baseEnd_2434695 < baseStart_2434695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434742 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2434742 : Nat := 118140960795 + 2434742 * 2 ^ 59
def prefixEnd_2434742 : Nat := 4983230072969 + 3 ^ 40 * 2434742 * 2
def baseEnd_2434742 : Nat := 833461943792812196285221

theorem tailTrace_2434742 : CollatzResearch.WordTrace tailWord_2434742 prefixEnd_2434742 833461943792812196285221 := by
  unfold tailWord_2434742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550146009084564354595155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59201557430235353115681653 5550146009084564354595155)
  ·
    refine ⟨8325219013626846531892733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5550146009084564354595155 8325219013626846531892733)
    ·
      refine ⟨3121957130110067449459775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8325219013626846531892733 3121957130110067449459775)
      ·
        refine ⟨4682935695165101174189663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121957130110067449459775 4682935695165101174189663)
        ·
          refine ⟨7024403542747651761284495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4682935695165101174189663 7024403542747651761284495)
          ·
            refine ⟨10536605314121477641926743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7024403542747651761284495 10536605314121477641926743)
            ·
              refine ⟨15804907971182216462890115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10536605314121477641926743 15804907971182216462890115)
              ·
                refine ⟨23707361956773324694335173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15804907971182216462890115 23707361956773324694335173)
                ·
                  refine ⟨4445130366894998380187845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23707361956773324694335173 4445130366894998380187845)
                  ·
                    refine ⟨833461943792812196285221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4445130366894998380187845 833461943792812196285221)
                    ·
                      rfl

theorem cell22_2434742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2434742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434742 prefixEnd_2434742 := by exact prefixLift 2434742
  have htrace : WordTrace (prefixWord ++ tailWord_2434742) baseStart_2434742 baseEnd_2434742 := by
    simpa [prefixWord, tailWord_2434742, baseEnd_2434742] using wordTrace_append hprefix tailTrace_2434742
  have hstable : (prefixWord ++ tailWord_2434742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434742).length < 2 ^ (prefixWord ++ tailWord_2434742).sum := by decide
  have hdescent : baseEnd_2434742 < baseStart_2434742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434806 : List Nat := [5, 1, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_2434806 : Nat := 118140960795 + 2434806 * 2 ^ 59
def prefixEnd_2434806 : Nat := 4983230072969 + 3 ^ 40 * 2434806 * 2
def baseEnd_2434806 : Nat := 833483852300737362685025

theorem tailTrace_2434806 : CollatzResearch.WordTrace tailWord_2434806 prefixEnd_2434806 833483852300737362685025 := by
  unfold tailWord_2434806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550291901070073037740767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59203113611414112402568181 5550291901070073037740767)
  ·
    refine ⟨8325437851605109556611151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5550291901070073037740767 8325437851605109556611151)
    ·
      refine ⟨12488156777407664334916727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8325437851605109556611151 12488156777407664334916727)
      ·
        refine ⟨18732235166111496502375091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12488156777407664334916727 18732235166111496502375091)
        ·
          refine ⟨28098352749167244753562637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18732235166111496502375091 28098352749167244753562637)
          ·
            refine ⟨10536882280937716782585989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28098352749167244753562637 10536882280937716782585989)
            ·
              refine ⟨1975665427675821896734873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10536882280937716782585989 1975665427675821896734873)
              ·
                refine ⟨1481749070756866422551155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975665427675821896734873 1481749070756866422551155)
                ·
                  refine ⟨2222623606135299633826733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481749070756866422551155 2222623606135299633826733)
                  ·
                    refine ⟨833483852300737362685025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222623606135299633826733 833483852300737362685025)
                    ·
                      rfl

theorem cell22_2434806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_2434806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434806 prefixEnd_2434806 := by exact prefixLift 2434806
  have htrace : WordTrace (prefixWord ++ tailWord_2434806) baseStart_2434806 baseEnd_2434806 := by
    simpa [prefixWord, tailWord_2434806, baseEnd_2434806] using wordTrace_append hprefix tailTrace_2434806
  have hstable : (prefixWord ++ tailWord_2434806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434806).length < 2 ^ (prefixWord ++ tailWord_2434806).sum := by decide
  have hdescent : baseEnd_2434806 < baseStart_2434806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434843 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 1, 6]
def baseStart_2434843 : Nat := 118140960795 + 2434843 * 2 ^ 59
def prefixEnd_2434843 : Nat := 4983230072969 + 3 ^ 40 * 2434843 * 2
def baseEnd_2434843 : Nat := 833496518156881599509911

theorem tailTrace_2434843 : CollatzResearch.WordTrace tailWord_2434843 prefixEnd_2434843 833496518156881599509911 := by
  unfold tailWord_2434843
  simp only [CollatzResearch.WordTrace]
  refine ⟨88806019917987123922949183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59204013278658082615299455 88806019917987123922949183)
  ·
    refine ⟨133209029876980685884423775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88806019917987123922949183 133209029876980685884423775)
    ·
      refine ⟨199813544815471028826635663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133209029876980685884423775 199813544815471028826635663)
      ·
        refine ⟨299720317223206543239953495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199813544815471028826635663 299720317223206543239953495)
        ·
          refine ⟨449580475834809814859930243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299720317223206543239953495 449580475834809814859930243)
          ·
            refine ⟨674370713752214722289895365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449580475834809814859930243 674370713752214722289895365)
            ·
              refine ⟨126444508828540260429355381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 674370713752214722289895365 126444508828540260429355381)
              ·
                refine ⟨11854172702675649415252067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126444508828540260429355381 11854172702675649415252067)
                ·
                  refine ⟨17781259054013474122878101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11854172702675649415252067 17781259054013474122878101)
                  ·
                    refine ⟨833496518156881599509911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17781259054013474122878101 833496518156881599509911)
                    ·
                      rfl

theorem cell22_2434843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_2434843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434843 prefixEnd_2434843 := by exact prefixLift 2434843
  have htrace : WordTrace (prefixWord ++ tailWord_2434843) baseStart_2434843 baseEnd_2434843 := by
    simpa [prefixWord, tailWord_2434843, baseEnd_2434843] using wordTrace_append hprefix tailTrace_2434843
  have hstable : (prefixWord ++ tailWord_2434843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434843).length < 2 ^ (prefixWord ++ tailWord_2434843).sum := by decide
  have hdescent : baseEnd_2434843 < baseStart_2434843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434847 : List Nat := [1, 1, 2, 4, 2, 1, 4, 3, 4]
def baseStart_2434847 : Nat := 118140960795 + 2434847 * 2 ^ 59
def prefixEnd_2434847 : Nat := 4983230072969 + 3 ^ 40 * 2434847 * 2
def baseEnd_2434847 : Nat := 277832629146208974136633

theorem tailTrace_2434847 : CollatzResearch.WordTrace tailWord_2434847 prefixEnd_2434847 277832629146208974136633 := by
  unfold tailWord_2434847
  simp only [CollatzResearch.WordTrace]
  refine ⟨88806165809972632606094795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59204110539981755070729863 88806165809972632606094795)
  ·
    refine ⟨133209248714958948909142193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88806165809972632606094795 133209248714958948909142193)
    ·
      refine ⟨99906936536219211681856645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133209248714958948909142193 99906936536219211681856645)
      ·
        refine ⟨18732550600541102190348121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99906936536219211681856645 18732550600541102190348121)
        ·
          refine ⟨14049412950405826642761091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18732550600541102190348121 14049412950405826642761091)
          ·
            refine ⟨21074119425608739964141637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14049412950405826642761091 21074119425608739964141637)
            ·
              refine ⟨3951397392301638743276557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21074119425608739964141637 3951397392301638743276557)
              ·
                refine ⟨1481774022113114528728709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3951397392301638743276557 1481774022113114528728709)
                ·
                  refine ⟨277832629146208974136633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481774022113114528728709 277832629146208974136633)
                  ·
                    rfl

theorem cell22_2434847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 4].length) (baseStart_2434847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434847 prefixEnd_2434847 := by exact prefixLift 2434847
  have htrace : WordTrace (prefixWord ++ tailWord_2434847) baseStart_2434847 baseEnd_2434847 := by
    simpa [prefixWord, tailWord_2434847, baseEnd_2434847] using wordTrace_append hprefix tailTrace_2434847
  have hstable : (prefixWord ++ tailWord_2434847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434847).length < 2 ^ (prefixWord ++ tailWord_2434847).sum := by decide
  have hdescent : baseEnd_2434847 < baseStart_2434847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434849 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 1, 4]
def baseStart_2434849 : Nat := 118140960795 + 2434849 * 2 ^ 59
def prefixEnd_2434849 : Nat := 4983230072969 + 3 ^ 40 * 2434849 * 2
def baseEnd_2434849 : Nat := 833498572079499583859893

theorem tailTrace_2434849 : CollatzResearch.WordTrace tailWord_2434849 prefixEnd_2434849 833498572079499583859893 := by
  unfold tailWord_2434849
  simp only [CollatzResearch.WordTrace]
  refine ⟨88806238755965386947667601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59204159170643591298445067 88806238755965386947667601)
  ·
    refine ⟨66604679066974040210750701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88806238755965386947667601 66604679066974040210750701)
    ·
      refine ⟨24976754650115265079031513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66604679066974040210750701 24976754650115265079031513)
      ·
        refine ⟨18732565987586448809273635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24976754650115265079031513 18732565987586448809273635)
        ·
          refine ⟨28098848981379673213910453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18732565987586448809273635 28098848981379673213910453)
          ·
            refine ⟨2634267092004344363804105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28098848981379673213910453 2634267092004344363804105)
            ·
              refine ⟨1975700319003258272853079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634267092004344363804105 1975700319003258272853079)
              ·
                refine ⟨2963550478504887409279619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975700319003258272853079 2963550478504887409279619)
                ·
                  refine ⟨4445325717757331113919429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963550478504887409279619 4445325717757331113919429)
                  ·
                    refine ⟨833498572079499583859893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4445325717757331113919429 833498572079499583859893)
                    ·
                      rfl

theorem cell22_2434849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_2434849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434849 prefixEnd_2434849 := by exact prefixLift 2434849
  have htrace : WordTrace (prefixWord ++ tailWord_2434849) baseStart_2434849 baseEnd_2434849 := by
    simpa [prefixWord, tailWord_2434849, baseEnd_2434849] using wordTrace_append hprefix tailTrace_2434849
  have hstable : (prefixWord ++ tailWord_2434849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434849).length < 2 ^ (prefixWord ++ tailWord_2434849).sum := by decide
  have hdescent : baseEnd_2434849 < baseStart_2434849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434879 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 1, 5]
def baseStart_2434879 : Nat := 118140960795 + 2434879 * 2 ^ 59
def prefixEnd_2434879 : Nat := 4983230072969 + 3 ^ 40 * 2434879 * 2
def baseEnd_2434879 : Nat := 833508841692589505609801

theorem tailTrace_2434879 : CollatzResearch.WordTrace tailWord_2434879 prefixEnd_2434879 833508841692589505609801 := by
  unfold tailWord_2434879
  simp only [CollatzResearch.WordTrace]
  refine ⟨88807332945856702071259691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59204888630571134714173127 88807332945856702071259691)
  ·
    refine ⟨133210999418785053106889537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88807332945856702071259691 133210999418785053106889537)
    ·
      refine ⟨99908249564088789830167153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133210999418785053106889537 99908249564088789830167153)
      ·
        refine ⟨74931187173066592372625365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99908249564088789830167153 74931187173066592372625365)
        ·
          refine ⟨1756199699368748258733407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 74931187173066592372625365 1756199699368748258733407)
          ·
            refine ⟨2634299549053122388100111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756199699368748258733407 2634299549053122388100111)
            ·
              refine ⟨3951449323579683582150167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634299549053122388100111 3951449323579683582150167)
              ·
                refine ⟨5927173985369525373225251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951449323579683582150167 5927173985369525373225251)
                ·
                  refine ⟨8890760978054288059837877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927173985369525373225251 8890760978054288059837877)
                  ·
                    refine ⟨833508841692589505609801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8890760978054288059837877 833508841692589505609801)
                    ·
                      rfl

theorem cell22_2434879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_2434879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434879 prefixEnd_2434879 := by exact prefixLift 2434879
  have htrace : WordTrace (prefixWord ++ tailWord_2434879) baseStart_2434879 baseEnd_2434879 := by
    simpa [prefixWord, tailWord_2434879, baseEnd_2434879] using wordTrace_append hprefix tailTrace_2434879
  have hstable : (prefixWord ++ tailWord_2434879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434879).length < 2 ^ (prefixWord ++ tailWord_2434879).sum := by decide
  have hdescent : baseEnd_2434879 < baseStart_2434879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434920 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 7]
def baseStart_2434920 : Nat := 118140960795 + 2434920 * 2 ^ 59
def prefixEnd_2434920 : Nat := 4983230072969 + 3 ^ 40 * 2434920 * 2
def baseEnd_2434920 : Nat := 277840958943493021778225

theorem tailTrace_2434920 : CollatzResearch.WordTrace tailWord_2434920 prefixEnd_2434920 277840958943493021778225 := by
  unfold tailWord_2434920
  simp only [CollatzResearch.WordTrace]
  refine ⟨44404414169354083036751107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59205885559138777382334809 44404414169354083036751107)
  ·
    refine ⟨66606621254031124555126661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44404414169354083036751107 66606621254031124555126661)
    ·
      refine ⟨12488741485130835854086249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66606621254031124555126661 12488741485130835854086249)
      ·
        refine ⟨9366556113848126890564687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12488741485130835854086249 9366556113848126890564687)
        ·
          refine ⟨14049834170772190335847031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9366556113848126890564687 14049834170772190335847031)
          ·
            refine ⟨21074751256158285503770547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14049834170772190335847031 21074751256158285503770547)
            ·
              refine ⟨31612126884237428255655821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21074751256158285503770547 31612126884237428255655821)
              ·
                refine ⟨11854547581589035595870933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31612126884237428255655821 11854547581589035595870933)
                ·
                  refine ⟨277840958943493021778225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11854547581589035595870933 277840958943493021778225)
                  ·
                    rfl

theorem cell22_2434920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 7].length) (baseStart_2434920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434920 prefixEnd_2434920 := by exact prefixLift 2434920
  have htrace : WordTrace (prefixWord ++ tailWord_2434920) baseStart_2434920 baseEnd_2434920 := by
    simpa [prefixWord, tailWord_2434920, baseEnd_2434920] using wordTrace_append hprefix tailTrace_2434920
  have hstable : (prefixWord ++ tailWord_2434920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434920).length < 2 ^ (prefixWord ++ tailWord_2434920).sum := by decide
  have hdescent : baseEnd_2434920 < baseStart_2434920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434924 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 3, 3]
def baseStart_2434924 : Nat := 118140960795 + 2434924 * 2 ^ 59
def prefixEnd_2434924 : Nat := 4983230072969 + 3 ^ 40 * 2434924 * 2
def baseEnd_2434924 : Nat := 833524246112224388234663

theorem tailTrace_2434924 : CollatzResearch.WordTrace tailWord_2434924 prefixEnd_2434924 833524246112224388234663 := by
  unfold tailWord_2434924
  simp only [CollatzResearch.WordTrace]
  refine ⟨44404487115346837378323913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59205982820462449837765217 44404487115346837378323913)
  ·
    refine ⟨33303365336510128033742935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44404487115346837378323913 33303365336510128033742935)
    ·
      refine ⟨49955048004765192050614403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33303365336510128033742935 49955048004765192050614403)
      ·
        refine ⟨74932572007147788075921605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49955048004765192050614403 74932572007147788075921605)
        ·
          refine ⟨14049857251340210264235301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74932572007147788075921605 14049857251340210264235301)
          ·
            refine ⟨2634348234626289424544119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14049857251340210264235301 2634348234626289424544119)
            ·
              refine ⟨3951522351939434136816179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634348234626289424544119 3951522351939434136816179)
              ·
                refine ⟨5927283527909151205224269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951522351939434136816179 5927283527909151205224269)
                ·
                  refine ⟨2222731322965931701959101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5927283527909151205224269 2222731322965931701959101)
                  ·
                    refine ⟨833524246112224388234663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222731322965931701959101 833524246112224388234663)
                    ·
                      rfl

theorem cell22_2434924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_2434924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434924 prefixEnd_2434924 := by exact prefixLift 2434924
  have htrace : WordTrace (prefixWord ++ tailWord_2434924) baseStart_2434924 baseEnd_2434924 := by
    simpa [prefixWord, tailWord_2434924, baseEnd_2434924] using wordTrace_append hprefix tailTrace_2434924
  have hstable : (prefixWord ++ tailWord_2434924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434924).length < 2 ^ (prefixWord ++ tailWord_2434924).sum := by decide
  have hdescent : baseEnd_2434924 < baseStart_2434924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434975 : List Nat := [1, 1, 2, 5, 4, 1, 2, 2, 1, 3]
def baseStart_2434975 : Nat := 118140960795 + 2434975 * 2 ^ 59
def prefixEnd_2434975 : Nat := 4983230072969 + 3 ^ 40 * 2434975 * 2
def baseEnd_2434975 : Nat := 833541704454477255209507

theorem tailTrace_2434975 : CollatzResearch.WordTrace tailWord_2434975 prefixEnd_2434975 833541704454477255209507 := by
  unfold tailWord_2434975
  simp only [CollatzResearch.WordTrace]
  refine ⟨88810834353508910466754379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59207222902339273644502919 88810834353508910466754379)
  ·
    refine ⟨133216251530263365700131569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88810834353508910466754379 133216251530263365700131569)
    ·
      refine ⟨99912188647697524275098677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133216251530263365700131569 99912188647697524275098677)
      ·
        refine ⟨9366767685721642900790501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99912188647697524275098677 9366767685721642900790501)
        ·
          refine ⟨1756268941072808043898219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9366767685721642900790501 1756268941072808043898219)
          ·
            refine ⟨2634403411609212065847329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756268941072808043898219 2634403411609212065847329)
            ·
              refine ⟨1975802558706909049385497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634403411609212065847329 1975802558706909049385497)
              ·
                refine ⟨1481851919030181787039123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1975802558706909049385497 1481851919030181787039123)
                ·
                  refine ⟨2222777878545272680558685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1481851919030181787039123 2222777878545272680558685)
                  ·
                    refine ⟨833541704454477255209507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222777878545272680558685 833541704454477255209507)
                    ·
                      rfl

theorem cell22_2434975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 2, 1, 3].length) (baseStart_2434975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434975 prefixEnd_2434975 := by exact prefixLift 2434975
  have htrace : WordTrace (prefixWord ++ tailWord_2434975) baseStart_2434975 baseEnd_2434975 := by
    simpa [prefixWord, tailWord_2434975, baseEnd_2434975] using wordTrace_append hprefix tailTrace_2434975
  have hstable : (prefixWord ++ tailWord_2434975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434975).length < 2 ^ (prefixWord ++ tailWord_2434975).sum := by decide
  have hdescent : baseEnd_2434975 < baseStart_2434975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434995 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 1, 6]
def baseStart_2434995 : Nat := 118140960795 + 2434995 * 2 ^ 59
def prefixEnd_2434995 : Nat := 4983230072969 + 3 ^ 40 * 2434995 * 2
def baseEnd_2434995 : Nat := 833548550863203869709445

theorem tailTrace_2434995 : CollatzResearch.WordTrace tailWord_2434995 prefixEnd_2434995 833548550863203869709445 := by
  unfold tailWord_2434995
  simp only [CollatzResearch.WordTrace]
  refine ⟨88811563813436453882482439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59207709208957635921654959 88811563813436453882482439)
  ·
    refine ⟨133217345720154680823723659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88811563813436453882482439 133217345720154680823723659)
    ·
      refine ⟨199826018580232021235585489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133217345720154680823723659 199826018580232021235585489)
      ·
        refine ⟨149869513935174015926689117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199826018580232021235585489 149869513935174015926689117)
        ·
          refine ⟨56201067725690255972508419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149869513935174015926689117 56201067725690255972508419)
          ·
            refine ⟨84301601588535383958762629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56201067725690255972508419 84301601588535383958762629)
            ·
              refine ⟨15806550297850384492267993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84301601588535383958762629 15806550297850384492267993)
              ·
                refine ⟨11854912723387788369200995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15806550297850384492267993 11854912723387788369200995)
                ·
                  refine ⟨17782369085081682553801493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11854912723387788369200995 17782369085081682553801493)
                  ·
                    refine ⟨833548550863203869709445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17782369085081682553801493 833548550863203869709445)
                    ·
                      rfl

theorem cell22_2434995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_2434995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434995 prefixEnd_2434995 := by exact prefixLift 2434995
  have htrace : WordTrace (prefixWord ++ tailWord_2434995) baseStart_2434995 baseEnd_2434995 := by
    simpa [prefixWord, tailWord_2434995, baseEnd_2434995] using wordTrace_append hprefix tailTrace_2434995
  have hstable : (prefixWord ++ tailWord_2434995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434995).length < 2 ^ (prefixWord ++ tailWord_2434995).sum := by decide
  have hdescent : baseEnd_2434995 < baseStart_2434995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2434997 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2434997 : Nat := 118140960795 + 2434997 * 2 ^ 59
def prefixEnd_2434997 : Nat := 4983230072969 + 3 ^ 40 * 2434997 * 2
def baseEnd_2434997 : Nat := 833549235504076531159439

theorem tailTrace_2434997 : CollatzResearch.WordTrace tailWord_2434997 prefixEnd_2434997 833549235504076531159439 := by
  unfold tailWord_2434997
  simp only [CollatzResearch.WordTrace]
  refine ⟨88811636759429208224055245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59207757839619472149370163 88811636759429208224055245)
  ·
    refine ⟨33304363784785953084020717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88811636759429208224055245 33304363784785953084020717)
    ·
      refine ⟨12489136419294732406507769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33304363784785953084020717 12489136419294732406507769)
      ·
        refine ⟨9366852314471049304880827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12489136419294732406507769 9366852314471049304880827)
        ·
          refine ⟨14050278471706573957321241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9366852314471049304880827 14050278471706573957321241)
          ·
            refine ⟨10537708853779930467990931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14050278471706573957321241 10537708853779930467990931)
            ·
              refine ⟨15806563280669895701986397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10537708853779930467990931 15806563280669895701986397)
              ·
                refine ⟨5927461230251210888244899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15806563280669895701986397 5927461230251210888244899)
                ·
                  refine ⟨8891191845376816332367349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927461230251210888244899 8891191845376816332367349)
                  ·
                    refine ⟨833549235504076531159439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8891191845376816332367349 833549235504076531159439)
                    ·
                      rfl

theorem cell22_2434997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2434997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2434997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2434997 prefixEnd_2434997 := by exact prefixLift 2434997
  have htrace : WordTrace (prefixWord ++ tailWord_2434997) baseStart_2434997 baseEnd_2434997 := by
    simpa [prefixWord, tailWord_2434997, baseEnd_2434997] using wordTrace_append hprefix tailTrace_2434997
  have hstable : (prefixWord ++ tailWord_2434997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2434997).length < 2 ^ (prefixWord ++ tailWord_2434997).sum := by decide
  have hdescent : baseEnd_2434997 < baseStart_2434997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2434997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435040 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 8]
def baseStart_2435040 : Nat := 118140960795 + 2435040 * 2 ^ 59
def prefixEnd_2435040 : Nat := 4983230072969 + 3 ^ 40 * 2435040 * 2
def baseEnd_2435040 : Nat := 833563955282838752334307

theorem tailTrace_2435040 : CollatzResearch.WordTrace tailWord_2435040 prefixEnd_2435040 833563955282838752334307 := by
  unfold tailWord_2435040
  simp only [CollatzResearch.WordTrace]
  refine ⟨44406602549136713283935287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59208803398848951045247049 44406602549136713283935287)
  ·
    refine ⟨66609903823705069925902931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44406602549136713283935287 66609903823705069925902931)
    ·
      refine ⟨99914855735557604888854397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66609903823705069925902931 99914855735557604888854397)
      ·
        refine ⟨37468070900834101833320399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99914855735557604888854397 37468070900834101833320399)
        ·
          refine ⟨56202106351251152749980599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37468070900834101833320399 56202106351251152749980599)
          ·
            refine ⟨84303159526876729124970899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56202106351251152749980599 84303159526876729124970899)
            ·
              refine ⟨126454739290315093687456349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84303159526876729124970899 126454739290315093687456349)
              ·
                refine ⟨47420527233868160132796131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126454739290315093687456349 47420527233868160132796131)
                ·
                  refine ⟨71130790850802240199194197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47420527233868160132796131 71130790850802240199194197)
                  ·
                    refine ⟨833563955282838752334307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71130790850802240199194197 833563955282838752334307)
                    ·
                      rfl

theorem cell22_2435040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_2435040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435040 prefixEnd_2435040 := by exact prefixLift 2435040
  have htrace : WordTrace (prefixWord ++ tailWord_2435040) baseStart_2435040 baseEnd_2435040 := by
    simpa [prefixWord, tailWord_2435040, baseEnd_2435040] using wordTrace_append hprefix tailTrace_2435040
  have hstable : (prefixWord ++ tailWord_2435040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435040).length < 2 ^ (prefixWord ++ tailWord_2435040).sum := by decide
  have hdescent : baseEnd_2435040 < baseStart_2435040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435093 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_2435093 : Nat := 118140960795 + 2435093 * 2 ^ 59
def prefixEnd_2435093 : Nat := 4983230072969 + 3 ^ 40 * 2435093 * 2
def baseEnd_2435093 : Nat := 833582098265964280759145

theorem tailTrace_2435093 : CollatzResearch.WordTrace tailWord_2435093 prefixEnd_2435093 833582098265964280759145 := by
  unfold tailWord_2435093
  simp only [CollatzResearch.WordTrace]
  refine ⟨88815138167081416619549933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59210092111387611079699955 88815138167081416619549933)
  ·
    refine ⟨33305676812655531232331225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88815138167081416619549933 33305676812655531232331225)
    ·
      refine ⟨24979257609491648424248419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33305676812655531232331225 24979257609491648424248419)
      ·
        refine ⟨37468886414237472636372629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24979257609491648424248419 37468886414237472636372629)
        ·
          refine ⟨1756354050667381529829967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37468886414237472636372629 1756354050667381529829967)
          ·
            refine ⟨2634531076001072294744951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756354050667381529829967 2634531076001072294744951)
            ·
              refine ⟨3951796614001608442117427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634531076001072294744951 3951796614001608442117427)
              ·
                refine ⟨5927694921002412663176141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951796614001608442117427 5927694921002412663176141)
                ·
                  refine ⟨2222885595375904748691053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5927694921002412663176141 2222885595375904748691053)
                  ·
                    refine ⟨833582098265964280759145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2222885595375904748691053 833582098265964280759145)
                    ·
                      rfl

theorem cell22_2435093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_2435093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435093 prefixEnd_2435093 := by exact prefixLift 2435093
  have htrace : WordTrace (prefixWord ++ tailWord_2435093) baseStart_2435093 baseEnd_2435093 := by
    simpa [prefixWord, tailWord_2435093, baseEnd_2435093] using wordTrace_append hprefix tailTrace_2435093
  have hstable : (prefixWord ++ tailWord_2435093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435093).length < 2 ^ (prefixWord ++ tailWord_2435093).sum := by decide
  have hdescent : baseEnd_2435093 < baseStart_2435093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435136 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 1, 4]
def baseStart_2435136 : Nat := 118140960795 + 2435136 * 2 ^ 59
def prefixEnd_2435136 : Nat := 4983230072969 + 3 ^ 40 * 2435136 * 2
def baseEnd_2435136 : Nat := 833596818044726501934013

theorem tailTrace_2435136 : CollatzResearch.WordTrace tailWord_2435136 prefixEnd_2435136 833596818044726501934013 := by
  unfold tailWord_2435136
  simp only [CollatzResearch.WordTrace]
  refine ⟨44408353252962817481682631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59211137670617089975576841 44408353252962817481682631)
  ·
    refine ⟨66612529879444226222523947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44408353252962817481682631 66612529879444226222523947)
    ·
      refine ⟨99918794819166339333785921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66612529879444226222523947 99918794819166339333785921)
      ·
        refine ⟨74939096114374754500339441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99918794819166339333785921 74939096114374754500339441)
        ·
          refine ⟨56204322085781065875254581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74939096114374754500339441 56204322085781065875254581)
          ·
            refine ⟨5269155195541974925805117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56204322085781065875254581 5269155195541974925805117)
            ·
              refine ⟨1975933198328240597176919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5269155195541974925805117 1975933198328240597176919)
              ·
                refine ⟨2963899797492360895765379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975933198328240597176919 2963899797492360895765379)
                ·
                  refine ⟨4445849696238541343648069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963899797492360895765379 4445849696238541343648069)
                  ·
                    refine ⟨833596818044726501934013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4445849696238541343648069 833596818044726501934013)
                    ·
                      rfl

theorem cell22_2435136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 4].length) (baseStart_2435136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435136 prefixEnd_2435136 := by exact prefixLift 2435136
  have htrace : WordTrace (prefixWord ++ tailWord_2435136) baseStart_2435136 baseEnd_2435136 := by
    simpa [prefixWord, tailWord_2435136, baseEnd_2435136] using wordTrace_append hprefix tailTrace_2435136
  have hstable : (prefixWord ++ tailWord_2435136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435136).length < 2 ^ (prefixWord ++ tailWord_2435136).sum := by decide
  have hdescent : baseEnd_2435136 < baseStart_2435136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435149 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2435149 : Nat := 118140960795 + 2435149 * 2 ^ 59
def prefixEnd_2435149 : Nat := 4983230072969 + 3 ^ 40 * 2435149 * 2
def baseEnd_2435149 : Nat := 833601268210398801358973

theorem tailTrace_2435149 : CollatzResearch.WordTrace tailWord_2435149 prefixEnd_2435149 833601268210398801358973 := by
  unfold tailWord_2435149
  simp only [CollatzResearch.WordTrace]
  refine ⟨88817180654878538183588501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59211453769919025455725667 88817180654878538183588501)
  ·
    refine ⟨4163305343197431477355711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88817180654878538183588501 4163305343197431477355711)
    ·
      refine ⟨6244958014796147216033567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163305343197431477355711 6244958014796147216033567)
      ·
        refine ⟨9367437022194220824050351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244958014796147216033567 9367437022194220824050351)
        ·
          refine ⟨14051155533291331236075527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9367437022194220824050351 14051155533291331236075527)
          ·
            refine ⟨21076733299936996854113291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14051155533291331236075527 21076733299936996854113291)
            ·
              refine ⟨31615099949905495281169937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21076733299936996854113291 31615099949905495281169937)
              ·
                refine ⟨23711324962429121460877453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31615099949905495281169937 23711324962429121460877453)
                ·
                  refine ⟨8891746860910920547829045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23711324962429121460877453 8891746860910920547829045)
                  ·
                    refine ⟨833601268210398801358973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8891746860910920547829045 833601268210398801358973)
                    ·
                      rfl

theorem cell22_2435149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2435149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435149 prefixEnd_2435149 := by exact prefixLift 2435149
  have htrace : WordTrace (prefixWord ++ tailWord_2435149) baseStart_2435149 baseEnd_2435149 := by
    simpa [prefixWord, tailWord_2435149, baseEnd_2435149] using wordTrace_append hprefix tailTrace_2435149
  have hstable : (prefixWord ++ tailWord_2435149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435149).length < 2 ^ (prefixWord ++ tailWord_2435149).sum := by decide
  have hdescent : baseEnd_2435149 < baseStart_2435149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435230 : List Nat := [4, 3, 1, 1, 4, 1, 2, 6]
def baseStart_2435230 : Nat := 118140960795 + 2435230 * 2 ^ 59
def prefixEnd_2435230 : Nat := 4983230072969 + 3 ^ 40 * 2435230 * 2
def baseEnd_2435230 : Nat := 92625444018415732231525

theorem tailTrace_2435230 : CollatzResearch.WordTrace tailWord_2435230 prefixEnd_2435230 92625444018415732231525 := by
  unfold tailWord_2435230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102516870948136127160893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59213423311723392678191429 11102516870948136127160893)
  ·
    refine ⟨4163443826605551047685335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11102516870948136127160893 4163443826605551047685335)
    ·
      refine ⟨6245165739908326571528003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163443826605551047685335 6245165739908326571528003)
      ·
        refine ⟨9367748609862489857292005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245165739908326571528003 9367748609862489857292005)
        ·
          refine ⟨1756452864349216848242251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9367748609862489857292005 1756452864349216848242251)
          ·
            refine ⟨2634679296523825272363377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756452864349216848242251 2634679296523825272363377)
            ·
              refine ⟨1976009472392868954272533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634679296523825272363377 1976009472392868954272533)
              ·
                refine ⟨92625444018415732231525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1976009472392868954272533 92625444018415732231525)
                ·
                  rfl

theorem cell22_2435230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_2435230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435230 prefixEnd_2435230 := by exact prefixLift 2435230
  have htrace : WordTrace (prefixWord ++ tailWord_2435230) baseStart_2435230 baseEnd_2435230 := by
    simpa [prefixWord, tailWord_2435230, baseEnd_2435230] using wordTrace_append hprefix tailTrace_2435230
  have hstable : (prefixWord ++ tailWord_2435230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435230).length < 2 ^ (prefixWord ++ tailWord_2435230).sum := by decide
  have hdescent : baseEnd_2435230 < baseStart_2435230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435245 : List Nat := [1, 5, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2435245 : Nat := 118140960795 + 2435245 * 2 ^ 59
def prefixEnd_2435245 : Nat := 4983230072969 + 3 ^ 40 * 2435245 * 2
def baseEnd_2435245 : Nat := 833634130972286550958679

theorem tailTrace_2435245 : CollatzResearch.WordTrace tailWord_2435245 prefixEnd_2435245 833634130972286550958679 := by
  unfold tailWord_2435245
  simp only [CollatzResearch.WordTrace]
  refine ⟨88820682062530746579083189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59213788041687164386055459 88820682062530746579083189)
  ·
    refine ⟨8326938943362257491789049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88820682062530746579083189 8326938943362257491789049)
    ·
      refine ⟨6245204207521693118841787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8326938943362257491789049 6245204207521693118841787)
      ·
        refine ⟨9367806311282539678262681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245204207521693118841787 9367806311282539678262681)
        ·
          refine ⟨7025854733461904758697011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9367806311282539678262681 7025854733461904758697011)
          ·
            refine ⟨10538782100192857138045517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7025854733461904758697011 10538782100192857138045517)
            ·
              refine ⟨3952043287572321426767069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10538782100192857138045517 3952043287572321426767069)
              ·
                refine ⟨1482016232839620535037651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3952043287572321426767069 1482016232839620535037651)
                ·
                  refine ⟨2223024349259430802556477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482016232839620535037651 2223024349259430802556477)
                  ·
                    refine ⟨833634130972286550958679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223024349259430802556477 833634130972286550958679)
                    ·
                      rfl

theorem cell22_2435245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2435245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435245 prefixEnd_2435245 := by exact prefixLift 2435245
  have htrace : WordTrace (prefixWord ++ tailWord_2435245) baseStart_2435245 baseEnd_2435245 := by
    simpa [prefixWord, tailWord_2435245, baseEnd_2435245] using wordTrace_append hprefix tailTrace_2435245
  have hstable : (prefixWord ++ tailWord_2435245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435245).length < 2 ^ (prefixWord ++ tailWord_2435245).sum := by decide
  have hdescent : baseEnd_2435245 < baseStart_2435245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435262 : List Nat := [4, 2, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_2435262 : Nat := 118140960795 + 2435262 * 2 ^ 59
def prefixEnd_2435262 : Nat := 4983230072969 + 3 ^ 40 * 2435262 * 2
def baseEnd_2435262 : Nat := 833639950419704173283627

theorem tailTrace_2435262 : CollatzResearch.WordTrace tailWord_2435262 prefixEnd_2435262 833639950419704173283627 := by
  unfold tailWord_2435262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102662762933644810306505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59214201402312772321634693 11102662762933644810306505)
  ·
    refine ⟨8326997072200233607729879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11102662762933644810306505 8326997072200233607729879)
    ·
      refine ⟨12490495608300350411594819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8326997072200233607729879 12490495608300350411594819)
      ·
        refine ⟨18735743412450525617392229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12490495608300350411594819 18735743412450525617392229)
        ·
          refine ⟨3512951889834473553261043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18735743412450525617392229 3512951889834473553261043)
          ·
            refine ⟨5269427834751710329891565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512951889834473553261043 5269427834751710329891565)
            ·
              refine ⟨1976035438031891373709337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5269427834751710329891565 1976035438031891373709337)
              ·
                refine ⟨1482026578523918530282003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1976035438031891373709337 1482026578523918530282003)
                ·
                  refine ⟨2223039867785877795423005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482026578523918530282003 2223039867785877795423005)
                  ·
                    refine ⟨833639950419704173283627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223039867785877795423005 833639950419704173283627)
                    ·
                      rfl

theorem cell22_2435262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_2435262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435262 prefixEnd_2435262 := by exact prefixLift 2435262
  have htrace : WordTrace (prefixWord ++ tailWord_2435262) baseStart_2435262 baseEnd_2435262 := by
    simpa [prefixWord, tailWord_2435262, baseEnd_2435262] using wordTrace_append hprefix tailTrace_2435262
  have hstable : (prefixWord ++ tailWord_2435262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435262).length < 2 ^ (prefixWord ++ tailWord_2435262).sum := by decide
  have hdescent : baseEnd_2435262 < baseStart_2435262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435269 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 6]
def baseStart_2435269 : Nat := 118140960795 + 2435269 * 2 ^ 59
def prefixEnd_2435269 : Nat := 4983230072969 + 3 ^ 40 * 2435269 * 2
def baseEnd_2435269 : Nat := 277880782220919496119535

theorem tailTrace_2435269 : CollatzResearch.WordTrace tailWord_2435269 prefixEnd_2435269 277880782220919496119535 := by
  unfold tailWord_2435269
  simp only [CollatzResearch.WordTrace]
  refine ⟨88821557414443798677956861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59214371609629199118637907 88821557414443798677956861)
  ·
    refine ⟨33308084030416424504233823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88821557414443798677956861 33308084030416424504233823)
    ·
      refine ⟨49962126045624636756350735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33308084030416424504233823 49962126045624636756350735)
      ·
        refine ⟨74943189068436955134526103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49962126045624636756350735 74943189068436955134526103)
        ·
          refine ⟨112414783602655432701789155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74943189068436955134526103 112414783602655432701789155)
          ·
            refine ⟨168622175403983149052683733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112414783602655432701789155 168622175403983149052683733)
            ·
              refine ⟨3952082236030855055922275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 168622175403983149052683733 3952082236030855055922275)
              ·
                refine ⟨5928123354046282583883413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952082236030855055922275 5928123354046282583883413)
                ·
                  refine ⟨277880782220919496119535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5928123354046282583883413 277880782220919496119535)
                  ·
                    rfl

theorem cell22_2435269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_2435269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435269 prefixEnd_2435269 := by exact prefixLift 2435269
  have htrace : WordTrace (prefixWord ++ tailWord_2435269) baseStart_2435269 baseEnd_2435269 := by
    simpa [prefixWord, tailWord_2435269, baseEnd_2435269] using wordTrace_append hprefix tailTrace_2435269
  have hstable : (prefixWord ++ tailWord_2435269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435269).length < 2 ^ (prefixWord ++ tailWord_2435269).sum := by decide
  have hdescent : baseEnd_2435269 < baseStart_2435269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435288 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 1, 4]
def baseStart_2435288 : Nat := 118140960795 + 2435288 * 2 ^ 59
def prefixEnd_2435288 : Nat := 4983230072969 + 3 ^ 40 * 2435288 * 2
def baseEnd_2435288 : Nat := 833648850751048772133547

theorem tailTrace_2435288 : CollatzResearch.WordTrace tailWord_2435288 prefixEnd_2435288 833648850751048772133547 := by
  unfold tailWord_2435288
  simp only [CollatzResearch.WordTrace]
  refine ⟨44411125200687482461449259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59214833600916643281932345 44411125200687482461449259)
  ·
    refine ⟨66616687801031223692173889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44411125200687482461449259 66616687801031223692173889)
    ·
      refine ⟨49962515850773417769130417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66616687801031223692173889 49962515850773417769130417)
      ·
        refine ⟨37471886888080063326847813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49962515850773417769130417 37471886888080063326847813)
        ·
          refine ⟨7025978791515011873783965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37471886888080063326847813 7025978791515011873783965)
          ·
            refine ⟨2634742046818129452668987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7025978791515011873783965 2634742046818129452668987)
            ·
              refine ⟨3952113070227194179003481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634742046818129452668987 3952113070227194179003481)
              ·
                refine ⟨2964084802670395634252611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3952113070227194179003481 2964084802670395634252611)
                ·
                  refine ⟨4446127204005593451378917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964084802670395634252611 4446127204005593451378917)
                  ·
                    refine ⟨833648850751048772133547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4446127204005593451378917 833648850751048772133547)
                    ·
                      rfl

theorem cell22_2435288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_2435288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435288 prefixEnd_2435288 := by exact prefixLift 2435288
  have htrace : WordTrace (prefixWord ++ tailWord_2435288) baseStart_2435288 baseEnd_2435288 := by
    simpa [prefixWord, tailWord_2435288, baseEnd_2435288] using wordTrace_append hprefix tailTrace_2435288
  have hstable : (prefixWord ++ tailWord_2435288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435288).length < 2 ^ (prefixWord ++ tailWord_2435288).sum := by decide
  have hdescent : baseEnd_2435288 < baseStart_2435288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435301 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_2435301 : Nat := 118140960795 + 2435301 * 2 ^ 59
def prefixEnd_2435301 : Nat := 4983230072969 + 3 ^ 40 * 2435301 * 2
def baseEnd_2435301 : Nat := 833653300916721071558507

theorem tailTrace_2435301 : CollatzResearch.WordTrace tailWord_2435301 prefixEnd_2435301 833653300916721071558507 := by
  unfold tailWord_2435301
  simp only [CollatzResearch.WordTrace]
  refine ⟨88822724550327868143121757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59215149700218578762081171 88822724550327868143121757)
  ·
    refine ⟨33308521706372950553670659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88822724550327868143121757 33308521706372950553670659)
    ·
      refine ⟨49962782559559425830505989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33308521706372950553670659 49962782559559425830505989)
      ·
        refine ⟨9368021729917392343219873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49962782559559425830505989 9368021729917392343219873)
        ·
          refine ⟨7026016297438044257414905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9368021729917392343219873 7026016297438044257414905)
          ·
            refine ⟨5269512223078533193061179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7026016297438044257414905 5269512223078533193061179)
            ·
              refine ⟨7904268334617799789591769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269512223078533193061179 7904268334617799789591769)
              ·
                refine ⟨5928201250963349842193827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7904268334617799789591769 5928201250963349842193827)
                ·
                  refine ⟨8892301876445024763290741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5928201250963349842193827 8892301876445024763290741)
                  ·
                    refine ⟨833653300916721071558507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8892301876445024763290741 833653300916721071558507)
                    ·
                      rfl

theorem cell22_2435301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_2435301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435301 prefixEnd_2435301 := by exact prefixLift 2435301
  have htrace : WordTrace (prefixWord ++ tailWord_2435301) baseStart_2435301 baseEnd_2435301 := by
    simpa [prefixWord, tailWord_2435301, baseEnd_2435301] using wordTrace_append hprefix tailTrace_2435301
  have hstable : (prefixWord ++ tailWord_2435301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435301).length < 2 ^ (prefixWord ++ tailWord_2435301).sum := by decide
  have hdescent : baseEnd_2435301 < baseStart_2435301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435314 : List Nat := [3, 2, 1, 3, 2, 11]
def baseStart_2435314 : Nat := 118140960795 + 2435314 * 2 ^ 59
def prefixEnd_2435314 : Nat := 4983230072969 + 3 ^ 40 * 2435314 * 2
def baseEnd_2435314 : Nat := 10292071001017202110907

theorem tailTrace_2435314 : CollatzResearch.WordTrace tailWord_2435314 prefixEnd_2435314 10292071001017202110907 := by
  unfold tailWord_2435314
  simp only [CollatzResearch.WordTrace]
  refine ⟨22205799674820192840836249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59215465799520514242229997 22205799674820192840836249)
  ·
    refine ⟨16654349756115144630627187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22205799674820192840836249 16654349756115144630627187)
    ·
      refine ⟨24981524634172716945940781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654349756115144630627187 24981524634172716945940781)
      ·
        refine ⟨9368071737814768854727793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24981524634172716945940781 9368071737814768854727793)
        ·
          refine ⟨7026053803361076641045845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9368071737814768854727793 7026053803361076641045845)
          ·
            refine ⟨10292071001017202110907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7026053803361076641045845 10292071001017202110907)
            ·
              rfl

theorem cell22_2435314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 11].length) (baseStart_2435314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435314 prefixEnd_2435314 := by exact prefixLift 2435314
  have htrace : WordTrace (prefixWord ++ tailWord_2435314) baseStart_2435314 baseEnd_2435314 := by
    simpa [prefixWord, tailWord_2435314, baseEnd_2435314] using wordTrace_append hprefix tailTrace_2435314
  have hstable : (prefixWord ++ tailWord_2435314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435314).length < 2 ^ (prefixWord ++ tailWord_2435314).sum := by decide
  have hdescent : baseEnd_2435314 < baseStart_2435314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435318 : List Nat := [5, 1, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_2435318 : Nat := 118140960795 + 2435318 * 2 ^ 59
def prefixEnd_2435318 : Nat := 4983230072969 + 3 ^ 40 * 2435318 * 2
def baseEnd_2435318 : Nat := 833659120364138693883455

theorem tailTrace_2435318 : CollatzResearch.WordTrace tailWord_2435318 prefixEnd_2435318 833659120364138693883455 := by
  unfold tailWord_2435318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551459036954142502905663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59215563060844186697660405 5551459036954142502905663)
  ·
    refine ⟨8327188555431213754358495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5551459036954142502905663 8327188555431213754358495)
    ·
      refine ⟨12490782833146820631537743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8327188555431213754358495 12490782833146820631537743)
      ·
        refine ⟨18736174249720230947306615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12490782833146820631537743 18736174249720230947306615)
        ·
          refine ⟨28104261374580346420959923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18736174249720230947306615 28104261374580346420959923)
          ·
            refine ⟨42156392061870519631439885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28104261374580346420959923 42156392061870519631439885)
            ·
              refine ⟨15808647023201444861789957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42156392061870519631439885 15808647023201444861789957)
              ·
                refine ⟨2964121316850270911585617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15808647023201444861789957 2964121316850270911585617)
                ·
                  refine ⟨2223090987637703183689213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2964121316850270911585617 2223090987637703183689213)
                  ·
                    refine ⟨833659120364138693883455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223090987637703183689213 833659120364138693883455)
                    ·
                      rfl

theorem cell22_2435318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_2435318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435318 prefixEnd_2435318 := by exact prefixLift 2435318
  have htrace : WordTrace (prefixWord ++ tailWord_2435318) baseStart_2435318 baseEnd_2435318 := by
    simpa [prefixWord, tailWord_2435318, baseEnd_2435318] using wordTrace_append hprefix tailTrace_2435318
  have hstable : (prefixWord ++ tailWord_2435318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435318).length < 2 ^ (prefixWord ++ tailWord_2435318).sum := by decide
  have hdescent : baseEnd_2435318 < baseStart_2435318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435380 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2435380 : Nat := 118140960795 + 2435380 * 2 ^ 59
def prefixEnd_2435380 : Nat := 4983230072969 + 3 ^ 40 * 2435380 * 2
def baseEnd_2435380 : Nat := 833680344231191198833265

theorem tailTrace_2435380 : CollatzResearch.WordTrace tailWord_2435380 prefixEnd_2435380 833680344231191198833265 := by
  unfold tailWord_2435380
  simp only [CollatzResearch.WordTrace]
  refine ⟨44412802958520832317623797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59217070611361109756831729 44412802958520832317623797)
  ·
    refine ⟨4163700277361328029777231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44412802958520832317623797 4163700277361328029777231)
    ·
      refine ⟨6245550416041992044665847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4163700277361328029777231 6245550416041992044665847)
      ·
        refine ⟨9368325624062988066998771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245550416041992044665847 9368325624062988066998771)
        ·
          refine ⟨14052488436094482100498157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368325624062988066998771 14052488436094482100498157)
          ·
            refine ⟨5269683163535430787686809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14052488436094482100498157 5269683163535430787686809)
            ·
              refine ⟨3952262372651573090765107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5269683163535430787686809 3952262372651573090765107)
              ·
                refine ⟨5928393558977359636147661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952262372651573090765107 5928393558977359636147661)
                ·
                  refine ⟨2223147584616509863555373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5928393558977359636147661 2223147584616509863555373)
                  ·
                    refine ⟨833680344231191198833265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223147584616509863555373 833680344231191198833265)
                    ·
                      rfl

theorem cell22_2435380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2435380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435380 prefixEnd_2435380 := by exact prefixLift 2435380
  have htrace : WordTrace (prefixWord ++ tailWord_2435380) baseStart_2435380 baseEnd_2435380 := by
    simpa [prefixWord, tailWord_2435380, baseEnd_2435380] using wordTrace_append hprefix tailTrace_2435380
  have hstable : (prefixWord ++ tailWord_2435380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435380).length < 2 ^ (prefixWord ++ tailWord_2435380).sum := by decide
  have hdescent : baseEnd_2435380 < baseStart_2435380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435468 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 2, 4]
def baseStart_2435468 : Nat := 118140960795 + 2435468 * 2 ^ 59
def prefixEnd_2435468 : Nat := 4983230072969 + 3 ^ 40 * 2435468 * 2
def baseEnd_2435468 : Nat := 833710468429588302632995

theorem tailTrace_2435468 : CollatzResearch.WordTrace tailWord_2435468 prefixEnd_2435468 833710468429588302632995 := by
  unfold tailWord_2435468
  simp only [CollatzResearch.WordTrace]
  refine ⟨44414407770361427832225529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59219210360481903776300705 44414407770361427832225529)
  ·
    refine ⟨33310805827771070874169147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44414407770361427832225529 33310805827771070874169147)
    ·
      refine ⟨49966208741656606311253721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33310805827771070874169147 49966208741656606311253721)
      ·
        refine ⟨37474656556242454733440291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49966208741656606311253721 37474656556242454733440291)
        ·
          refine ⟨56211984834363682100160437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37474656556242454733440291 56211984834363682100160437)
          ·
            refine ⟨5269873578221595196890041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56211984834363682100160437 5269873578221595196890041)
            ·
              refine ⟨3952405183666196397667531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5269873578221595196890041 3952405183666196397667531)
              ·
                refine ⟨5928607775499294596501297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952405183666196397667531 5928607775499294596501297)
                ·
                  refine ⟨4446455831624470947375973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5928607775499294596501297 4446455831624470947375973)
                  ·
                    refine ⟨833710468429588302632995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4446455831624470947375973 833710468429588302632995)
                    ·
                      rfl

theorem cell22_2435468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_2435468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435468 prefixEnd_2435468 := by exact prefixLift 2435468
  have htrace : WordTrace (prefixWord ++ tailWord_2435468) baseStart_2435468 baseEnd_2435468 := by
    simpa [prefixWord, tailWord_2435468, baseEnd_2435468] using wordTrace_append hprefix tailTrace_2435468
  have hstable : (prefixWord ++ tailWord_2435468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435468).length < 2 ^ (prefixWord ++ tailWord_2435468).sum := by decide
  have hdescent : baseEnd_2435468 < baseStart_2435468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435489 : List Nat := [1, 2, 3, 5, 1, 2, 2, 2, 4]
def baseStart_2435489 : Nat := 118140960795 + 2435489 * 2 ^ 59
def prefixEnd_2435489 : Nat := 4983230072969 + 3 ^ 40 * 2435489 * 2
def baseEnd_2435489 : Nat := 277905885719583749285977

theorem tailTrace_2435489 : CollatzResearch.WordTrace tailWord_2435489 prefixEnd_2435489 277905885719583749285977 := by
  unfold tailWord_2435489
  simp only [CollatzResearch.WordTrace]
  refine ⟨88829581473646776250965521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59219720982431184167310347 88829581473646776250965521)
  ·
    refine ⟨66622186105235082188224141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88829581473646776250965521 66622186105235082188224141)
    ·
      refine ⟨24983319789463155820584053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66622186105235082188224141 24983319789463155820584053)
      ·
        refine ⟨2342186230262170858179755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24983319789463155820584053 2342186230262170858179755)
        ·
          refine ⟨3513279345393256287269633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342186230262170858179755 3513279345393256287269633)
          ·
            refine ⟨2634959509044942215452225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3513279345393256287269633 2634959509044942215452225)
            ·
              refine ⟨1976219631783706661589169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634959509044942215452225 1976219631783706661589169)
              ·
                refine ⟨1482164723837779996191877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1976219631783706661589169 1482164723837779996191877)
                ·
                  refine ⟨277905885719583749285977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482164723837779996191877 277905885719583749285977)
                  ·
                    rfl

theorem cell22_2435489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_2435489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435489 prefixEnd_2435489 := by exact prefixLift 2435489
  have htrace : WordTrace (prefixWord ++ tailWord_2435489) baseStart_2435489 baseEnd_2435489 := by
    simpa [prefixWord, tailWord_2435489, baseEnd_2435489] using wordTrace_append hprefix tailTrace_2435489
  have hstable : (prefixWord ++ tailWord_2435489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435489).length < 2 ^ (prefixWord ++ tailWord_2435489).sum := by decide
  have hdescent : baseEnd_2435489 < baseStart_2435489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435603 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 2, 4]
def baseStart_2435603 : Nat := 118140960795 + 2435603 * 2 ^ 59
def prefixEnd_2435603 : Nat := 4983230072969 + 3 ^ 40 * 2435603 * 2
def baseEnd_2435603 : Nat := 833756681688492950507581

theorem tailTrace_2435603 : CollatzResearch.WordTrace tailWord_2435603 prefixEnd_2435603 833756681688492950507581 := by
  unfold tailWord_2435603
  simp only [CollatzResearch.WordTrace]
  refine ⟨88833739395233773720615463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59222492930155849147076975 88833739395233773720615463)
  ·
    refine ⟨133250609092850660580923195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88833739395233773720615463 133250609092850660580923195)
    ·
      refine ⟨199875913639275990871384793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133250609092850660580923195 199875913639275990871384793)
      ·
        refine ⟨149906935229456993153538595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199875913639275990871384793 149906935229456993153538595)
        ·
          refine ⟨224860402844185489730307893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149906935229456993153538595 224860402844185489730307893)
          ·
            refine ⟨21080662766642389662216365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224860402844185489730307893 21080662766642389662216365)
            ·
              refine ⟨7905248537490896123331137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21080662766642389662216365 7905248537490896123331137)
              ·
                refine ⟨5928936403118172092498353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7905248537490896123331137 5928936403118172092498353)
                ·
                  refine ⟨4446702302338629069373765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5928936403118172092498353 4446702302338629069373765)
                  ·
                    refine ⟨833756681688492950507581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4446702302338629069373765 833756681688492950507581)
                    ·
                      rfl

theorem cell22_2435603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_2435603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435603 prefixEnd_2435603 := by exact prefixLift 2435603
  have htrace : WordTrace (prefixWord ++ tailWord_2435603) baseStart_2435603 baseEnd_2435603 := by
    simpa [prefixWord, tailWord_2435603, baseEnd_2435603] using wordTrace_append hprefix tailTrace_2435603
  have hstable : (prefixWord ++ tailWord_2435603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435603).length < 2 ^ (prefixWord ++ tailWord_2435603).sum := by decide
  have hdescent : baseEnd_2435603 < baseStart_2435603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435605 : List Nat := [1, 3, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2435605 : Nat := 118140960795 + 2435605 * 2 ^ 59
def prefixEnd_2435605 : Nat := 4983230072969 + 3 ^ 40 * 2435605 * 2
def baseEnd_2435605 : Nat := 833757366329365611957575

theorem tailTrace_2435605 : CollatzResearch.WordTrace tailWord_2435605 prefixEnd_2435605 833757366329365611957575 := by
  unfold tailWord_2435605
  simp only [CollatzResearch.WordTrace]
  refine ⟨88833812341226528062188269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59222541560817685374792179 88833812341226528062188269)
  ·
    refine ⟨33312679627959948023320601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88833812341226528062188269 33312679627959948023320601)
    ·
      refine ⟨24984509720969961017490451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33312679627959948023320601 24984509720969961017490451)
      ·
        refine ⟨37476764581454941526235677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24984509720969961017490451 37476764581454941526235677)
        ·
          refine ⟨14053786718045603072338379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37476764581454941526235677 14053786718045603072338379)
          ·
            refine ⟨21080680077068404608507569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14053786718045603072338379 21080680077068404608507569)
            ·
              refine ⟨15810510057801303456380677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21080680077068404608507569 15810510057801303456380677)
              ·
                refine ⟨2964470635837744398071377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15810510057801303456380677 2964470635837744398071377)
                ·
                  refine ⟨2223352976878308298553533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2964470635837744398071377 2223352976878308298553533)
                  ·
                    refine ⟨833757366329365611957575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223352976878308298553533 833757366329365611957575)
                    ·
                      rfl

theorem cell22_2435605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2435605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435605 prefixEnd_2435605 := by exact prefixLift 2435605
  have htrace : WordTrace (prefixWord ++ tailWord_2435605) baseStart_2435605 baseEnd_2435605 := by
    simpa [prefixWord, tailWord_2435605, baseEnd_2435605] using wordTrace_append hprefix tailTrace_2435605
  have hstable : (prefixWord ++ tailWord_2435605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435605).length < 2 ^ (prefixWord ++ tailWord_2435605).sum := by decide
  have hdescent : baseEnd_2435605 < baseStart_2435605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435607 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 6]
def baseStart_2435607 : Nat := 118140960795 + 2435607 * 2 ^ 59
def prefixEnd_2435607 : Nat := 4983230072969 + 3 ^ 40 * 2435607 * 2
def baseEnd_2435607 : Nat := 277919350323412757802523

theorem tailTrace_2435607 : CollatzResearch.WordTrace tailWord_2435607 prefixEnd_2435607 277919350323412757802523 := by
  unfold tailWord_2435607
  simp only [CollatzResearch.WordTrace]
  refine ⟨88833885287219282403761075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59222590191479521602507383 88833885287219282403761075)
  ·
    refine ⟨133250827930828923605641613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88833885287219282403761075 133250827930828923605641613)
    ·
      refine ⟨49969060474060846352115605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133250827930828923605641613 49969060474060846352115605)
      ·
        refine ⟨2342299709721602172755419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49969060474060846352115605 2342299709721602172755419)
        ·
          refine ⟨3513449564582403259133129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342299709721602172755419 3513449564582403259133129)
          ·
            refine ⟨2635087173436802444349847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3513449564582403259133129 2635087173436802444349847)
            ·
              refine ⟨3952630760155203666524771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635087173436802444349847 3952630760155203666524771)
              ·
                refine ⟨5928946140232805499787157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952630760155203666524771 5928946140232805499787157)
                ·
                  refine ⟨277919350323412757802523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5928946140232805499787157 277919350323412757802523)
                  ·
                    rfl

theorem cell22_2435607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 6].length) (baseStart_2435607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435607 prefixEnd_2435607 := by exact prefixLift 2435607
  have htrace : WordTrace (prefixWord ++ tailWord_2435607) baseStart_2435607 baseEnd_2435607 := by
    simpa [prefixWord, tailWord_2435607, baseEnd_2435607] using wordTrace_append hprefix tailTrace_2435607
  have hstable : (prefixWord ++ tailWord_2435607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435607).length < 2 ^ (prefixWord ++ tailWord_2435607).sum := by decide
  have hdescent : baseEnd_2435607 < baseStart_2435607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435652 : List Nat := [2, 3, 5, 1, 1, 10]
def baseStart_2435652 : Nat := 118140960795 + 2435652 * 2 ^ 59
def prefixEnd_2435652 : Nat := 4983230072969 + 3 ^ 40 * 2435652 * 2
def baseEnd_2435652 : Nat := 10293499449257693284351

theorem tailTrace_2435652 : CollatzResearch.WordTrace tailWord_2435652 prefixEnd_2435652 10293499449257693284351 := by
  unfold tailWord_2435652
  simp only [CollatzResearch.WordTrace]
  refine ⟨44417763286028127544574605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59223684381370836726099473 44417763286028127544574605)
  ·
    refine ⟨16656661232260547829215477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44417763286028127544574605 16656661232260547829215477)
    ·
      refine ⟨1561561990524426358988951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16656661232260547829215477 1561561990524426358988951)
      ·
        refine ⟨2342342985786639538483427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561561990524426358988951 2342342985786639538483427)
        ·
          refine ⟨3513514478679959307725141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2342342985786639538483427 3513514478679959307725141)
          ·
            refine ⟨10293499449257693284351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3513514478679959307725141 10293499449257693284351)
            ·
              rfl

theorem cell22_2435652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 10].length) (baseStart_2435652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435652 prefixEnd_2435652 := by exact prefixLift 2435652
  have htrace : WordTrace (prefixWord ++ tailWord_2435652) baseStart_2435652 baseEnd_2435652 := by
    simpa [prefixWord, tailWord_2435652, baseEnd_2435652] using wordTrace_append hprefix tailTrace_2435652
  have hstable : (prefixWord ++ tailWord_2435652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435652).length < 2 ^ (prefixWord ++ tailWord_2435652).sum := by decide
  have hdescent : baseEnd_2435652 < baseStart_2435652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435663 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 5]
def baseStart_2435663 : Nat := 118140960795 + 2435663 * 2 ^ 59
def prefixEnd_2435663 : Nat := 4983230072969 + 3 ^ 40 * 2435663 * 2
def baseEnd_2435663 : Nat := 277925740304890931335799

theorem tailTrace_2435663 : CollatzResearch.WordTrace tailWord_2435663 prefixEnd_2435663 277925740304890931335799 := by
  unfold tailWord_2435663
  simp only [CollatzResearch.WordTrace]
  refine ⟨88835927775016403967799643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59223951850010935978533095 88835927775016403967799643)
  ·
    refine ⟨133253891662524605951699465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88835927775016403967799643 133253891662524605951699465)
    ·
      refine ⟨99940418746893454463774599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133253891662524605951699465 99940418746893454463774599)
      ·
        refine ⟨149910628120340181695661899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99940418746893454463774599 149910628120340181695661899)
        ·
          refine ⟨224865942180510272543492849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149910628120340181695661899 224865942180510272543492849)
          ·
            refine ⟨168649456635382704407619637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224865942180510272543492849 168649456635382704407619637)
            ·
              refine ⟨15810886559567128538214341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168649456635382704407619637 15810886559567128538214341)
              ·
                refine ⟨2964541229918836600915189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15810886559567128538214341 2964541229918836600915189)
                ·
                  refine ⟨277925740304890931335799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2964541229918836600915189 277925740304890931335799)
                  ·
                    rfl

theorem cell22_2435663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 5].length) (baseStart_2435663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435663 prefixEnd_2435663 := by exact prefixLift 2435663
  have htrace : WordTrace (prefixWord ++ tailWord_2435663) baseStart_2435663 baseEnd_2435663 := by
    simpa [prefixWord, tailWord_2435663, baseEnd_2435663] using wordTrace_append hprefix tailTrace_2435663
  have hstable : (prefixWord ++ tailWord_2435663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435663).length < 2 ^ (prefixWord ++ tailWord_2435663).sum := by decide
  have hdescent : baseEnd_2435663 < baseStart_2435663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435701 : List Nat := [1, 3, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2435701 : Nat := 118140960795 + 2435701 * 2 ^ 59
def prefixEnd_2435701 : Nat := 4983230072969 + 3 ^ 40 * 2435701 * 2
def baseEnd_2435701 : Nat := 833790229091253361557281

theorem tailTrace_2435701 : CollatzResearch.WordTrace tailWord_2435701 prefixEnd_2435701 833790229091253361557281 := by
  unfold tailWord_2435701
  simp only [CollatzResearch.WordTrace]
  refine ⟨88837313748878736457682957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59224875832585824305121971 88837313748878736457682957)
  ·
    refine ⟨33313992655829526171631109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88837313748878736457682957 33313992655829526171631109)
    ·
      refine ⟨6246373622968036157180833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33313992655829526171631109 6246373622968036157180833)
      ·
        refine ⟨4684780217226027117885625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6246373622968036157180833 4684780217226027117885625)
        ·
          refine ⟨3513585162919520338414219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4684780217226027117885625 3513585162919520338414219)
          ·
            refine ⟨5270377744379280507621329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513585162919520338414219 5270377744379280507621329)
            ·
              refine ⟨3952783308284460380715997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5270377744379280507621329 3952783308284460380715997)
              ·
                refine ⟨1482293740606672642768499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3952783308284460380715997 1482293740606672642768499)
                ·
                  refine ⟨2223440610910008964152749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482293740606672642768499 2223440610910008964152749)
                  ·
                    refine ⟨833790229091253361557281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223440610910008964152749 833790229091253361557281)
                    ·
                      rfl

theorem cell22_2435701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2435701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435701 prefixEnd_2435701 := by exact prefixLift 2435701
  have htrace : WordTrace (prefixWord ++ tailWord_2435701) baseStart_2435701 baseEnd_2435701 := by
    simpa [prefixWord, tailWord_2435701, baseEnd_2435701] using wordTrace_append hprefix tailTrace_2435701
  have hstable : (prefixWord ++ tailWord_2435701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435701).length < 2 ^ (prefixWord ++ tailWord_2435701).sum := by decide
  have hdescent : baseEnd_2435701 < baseStart_2435701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435757 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2435757 : Nat := 118140960795 + 2435757 * 2 ^ 59
def prefixEnd_2435757 : Nat := 4983230072969 + 3 ^ 40 * 2435757 * 2
def baseEnd_2435757 : Nat := 833809399035687882157109

theorem tailTrace_2435757 : CollatzResearch.WordTrace tailWord_2435757 prefixEnd_2435757 833809399035687882157109 := by
  unfold tailWord_2435757
  simp only [CollatzResearch.WordTrace]
  refine ⟨88839356236675858021721525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59226237491117238681147683 88839356236675858021721525)
  ·
    refine ⟨8328689647188361689536393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88839356236675858021721525 8328689647188361689536393)
    ·
      refine ⟨6246517235391271267152295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8328689647188361689536393 6246517235391271267152295)
      ·
        refine ⟨9369775853086906900728443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6246517235391271267152295 9369775853086906900728443)
        ·
          refine ⟨14054663779630360351092665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9369775853086906900728443 14054663779630360351092665)
          ·
            refine ⟨10540997834722770263319499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14054663779630360351092665 10540997834722770263319499)
            ·
              refine ⟨15811496752084155394979249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10540997834722770263319499 15811496752084155394979249)
              ·
                refine ⟨11858622564063116546234437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15811496752084155394979249 11858622564063116546234437)
                ·
                  refine ⟨2223491730761834352418957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11858622564063116546234437 2223491730761834352418957)
                  ·
                    refine ⟨833809399035687882157109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223491730761834352418957 833809399035687882157109)
                    ·
                      rfl

theorem cell22_2435757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2435757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435757 prefixEnd_2435757 := by exact prefixLift 2435757
  have htrace : WordTrace (prefixWord ++ tailWord_2435757) baseStart_2435757 baseEnd_2435757 := by
    simpa [prefixWord, tailWord_2435757, baseEnd_2435757] using wordTrace_append hprefix tailTrace_2435757
  have hstable : (prefixWord ++ tailWord_2435757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435757).length < 2 ^ (prefixWord ++ tailWord_2435757).sum := by decide
  have hdescent : baseEnd_2435757 < baseStart_2435757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435836 : List Nat := [2, 2, 2, 1, 3, 2, 4, 2, 1, 3]
def baseStart_2435836 : Nat := 118140960795 + 2435836 * 2 ^ 59
def prefixEnd_2435836 : Nat := 4983230072969 + 3 ^ 40 * 2435836 * 2
def baseEnd_2435836 : Nat := 833836442350158009431867

theorem tailTrace_2435836 : CollatzResearch.WordTrace tailWord_2435836 prefixEnd_2435836 833836442350158009431867 := by
  unfold tailWord_2435836
  simp only [CollatzResearch.WordTrace]
  refine ⟨44421118801694827256923681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59228158402259769675898241 44421118801694827256923681)
  ·
    refine ⟨33315839101271120442692761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44421118801694827256923681 33315839101271120442692761)
    ·
      refine ⟨24986879325953340332019571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33315839101271120442692761 24986879325953340332019571)
      ·
        refine ⟨37480318988930010498029357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24986879325953340332019571 37480318988930010498029357)
        ·
          refine ⟨14055119620848753936761009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37480318988930010498029357 14055119620848753936761009)
          ·
            refine ⟨10541339715636565452570757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14055119620848753936761009 10541339715636565452570757)
            ·
              refine ⟨1976501196681856022357017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10541339715636565452570757 1976501196681856022357017)
              ·
                refine ⟨1482375897511392016767763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1976501196681856022357017 1482375897511392016767763)
                ·
                  refine ⟨2223563846267088025151645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482375897511392016767763 2223563846267088025151645)
                  ·
                    refine ⟨833836442350158009431867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223563846267088025151645 833836442350158009431867)
                    ·
                      rfl

theorem cell22_2435836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_2435836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435836 prefixEnd_2435836 := by exact prefixLift 2435836
  have htrace : WordTrace (prefixWord ++ tailWord_2435836) baseStart_2435836 baseEnd_2435836 := by
    simpa [prefixWord, tailWord_2435836, baseEnd_2435836] using wordTrace_append hprefix tailTrace_2435836
  have hstable : (prefixWord ++ tailWord_2435836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435836).length < 2 ^ (prefixWord ++ tailWord_2435836).sum := by decide
  have hdescent : baseEnd_2435836 < baseStart_2435836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435847 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2435847 : Nat := 118140960795 + 2435847 * 2 ^ 59
def prefixEnd_2435847 : Nat := 4983230072969 + 3 ^ 40 * 2435847 * 2
def baseEnd_2435847 : Nat := 833840207874957647406833

theorem tailTrace_2435847 : CollatzResearch.WordTrace tailWord_2435847 prefixEnd_2435847 833840207874957647406833 := by
  unfold tailWord_2435847
  simp only [CollatzResearch.WordTrace]
  refine ⟨88842638806349803392497795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59228425870899868928331863 88842638806349803392497795)
  ·
    refine ⟨133263958209524705088746693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88842638806349803392497795 133263958209524705088746693)
    ·
      refine ⟨24986992164285882204140005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133263958209524705088746693 24986992164285882204140005)
      ·
        refine ⟨4685061030803602913276251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24986992164285882204140005 4685061030803602913276251)
        ·
          refine ⟨7027591546205404369914377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685061030803602913276251 7027591546205404369914377)
          ·
            refine ⟨5270693659654053277435783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7027591546205404369914377 5270693659654053277435783)
            ·
              refine ⟨7906040489481079916153675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270693659654053277435783 7906040489481079916153675)
              ·
                refine ⟨11859060734221619874230513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7906040489481079916153675 11859060734221619874230513)
                ·
                  refine ⟨8894295550666214905672885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11859060734221619874230513 8894295550666214905672885)
                  ·
                    refine ⟨833840207874957647406833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8894295550666214905672885 833840207874957647406833)
                    ·
                      rfl

theorem cell22_2435847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2435847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435847 prefixEnd_2435847 := by exact prefixLift 2435847
  have htrace : WordTrace (prefixWord ++ tailWord_2435847) baseStart_2435847 baseEnd_2435847 := by
    simpa [prefixWord, tailWord_2435847, baseEnd_2435847] using wordTrace_append hprefix tailTrace_2435847
  have hstable : (prefixWord ++ tailWord_2435847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435847).length < 2 ^ (prefixWord ++ tailWord_2435847).sum := by decide
  have hdescent : baseEnd_2435847 < baseStart_2435847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2435954 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_2435954 : Nat := 118140960795 + 2435954 * 2 ^ 59
def prefixEnd_2435954 : Nat := 4983230072969 + 3 ^ 40 * 2435954 * 2
def baseEnd_2435954 : Nat := 833876836161645034981505

theorem tailTrace_2435954 : CollatzResearch.WordTrace tailWord_2435954 prefixEnd_2435954 833876836161645034981505 := by
  unfold tailWord_2435954
  simp only [CollatzResearch.WordTrace]
  refine ⟨22211635354240540166660729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59231027611308107111095277 22211635354240540166660729)
  ·
    refine ⟨16658726515680405124995547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22211635354240540166660729 16658726515680405124995547)
    ·
      refine ⟨24988089773520607687493321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16658726515680405124995547 24988089773520607687493321)
      ·
        refine ⟨18741067330140455765619991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24988089773520607687493321 18741067330140455765619991)
        ·
          refine ⟨28111600995210683648429987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18741067330140455765619991 28111600995210683648429987)
          ·
            refine ⟨42167401492816025472644981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28111600995210683648429987 42167401492816025472644981)
            ·
              refine ⟨3953193889951502388060467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42167401492816025472644981 3953193889951502388060467)
              ·
                refine ⟨5929790834927253582090701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953193889951502388060467 5929790834927253582090701)
                ·
                  refine ⟨2223671563097720093284013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5929790834927253582090701 2223671563097720093284013)
                  ·
                    refine ⟨833876836161645034981505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223671563097720093284013 833876836161645034981505)
                    ·
                      rfl

theorem cell22_2435954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_2435954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2435954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2435954 prefixEnd_2435954 := by exact prefixLift 2435954
  have htrace : WordTrace (prefixWord ++ tailWord_2435954) baseStart_2435954 baseEnd_2435954 := by
    simpa [prefixWord, tailWord_2435954, baseEnd_2435954] using wordTrace_append hprefix tailTrace_2435954
  have hstable : (prefixWord ++ tailWord_2435954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2435954).length < 2 ^ (prefixWord ++ tailWord_2435954).sum := by decide
  have hdescent : baseEnd_2435954 < baseStart_2435954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2435954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436029 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 6]
def baseStart_2436029 : Nat := 118140960795 + 2436029 * 2 ^ 59
def prefixEnd_2436029 : Nat := 4983230072969 + 3 ^ 40 * 2436029 * 2
def baseEnd_2436029 : Nat := 277967503398123279785425

theorem tailTrace_2436029 : CollatzResearch.WordTrace tailWord_2436029 prefixEnd_2436029 277967503398123279785425 := by
  unfold tailWord_2436029
  simp only [CollatzResearch.WordTrace]
  refine ⟨88849276891690448475623141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59232851261126965650415427 88849276891690448475623141)
  ·
    refine ⟨16659239417191959089179339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88849276891690448475623141 16659239417191959089179339)
    ·
      refine ⟨24988859125787938633769009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16659239417191959089179339 24988859125787938633769009)
      ·
        refine ⟨18741644344340953975326757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24988859125787938633769009 18741644344340953975326757)
        ·
          refine ⟨3514058314563928870373767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18741644344340953975326757 3514058314563928870373767)
          ·
            refine ⟨5271087471845893305560651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514058314563928870373767 5271087471845893305560651)
            ·
              refine ⟨7906631207768839958340977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271087471845893305560651 7906631207768839958340977)
              ·
                refine ⟨5929973405826629968755733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7906631207768839958340977 5929973405826629968755733)
                ·
                  refine ⟨277967503398123279785425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5929973405826629968755733 277967503398123279785425)
                  ·
                    rfl

theorem cell22_2436029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_2436029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436029 prefixEnd_2436029 := by exact prefixLift 2436029
  have htrace : WordTrace (prefixWord ++ tailWord_2436029) baseStart_2436029 baseEnd_2436029 := by
    simpa [prefixWord, tailWord_2436029, baseEnd_2436029] using wordTrace_append hprefix tailTrace_2436029
  have hstable : (prefixWord ++ tailWord_2436029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436029).length < 2 ^ (prefixWord ++ tailWord_2436029).sum := by decide
  have hdescent : baseEnd_2436029 < baseStart_2436029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436044 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 4, 3]
def baseStart_2436044 : Nat := 118140960795 + 2436044 * 2 ^ 59
def prefixEnd_2436044 : Nat := 4983230072969 + 3 ^ 40 * 2436044 * 2
def baseEnd_2436044 : Nat := 833907645000914800231229

theorem tailTrace_2436044 : CollatzResearch.WordTrace tailWord_2436044 prefixEnd_2436044 833907645000914800231229 := by
  unfold tailWord_2436044
  simp only [CollatzResearch.WordTrace]
  refine ⟨44424911993318053018709593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59233215991090737358279457 44424911993318053018709593)
  ·
    refine ⟨33318683994988539764032195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44424911993318053018709593 33318683994988539764032195)
    ·
      refine ⟨49978025992482809646048293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33318683994988539764032195 49978025992482809646048293)
      ·
        refine ⟨9370879873590526808634055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49978025992482809646048293 9370879873590526808634055)
        ·
          refine ⟨14056319810385790212951083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9370879873590526808634055 14056319810385790212951083)
          ·
            refine ⟨21084479715578685319426625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14056319810385790212951083 21084479715578685319426625)
            ·
              refine ⟨15813359786684013989569969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21084479715578685319426625 15813359786684013989569969)
              ·
                refine ⟨11860019840013010492177477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15813359786684013989569969 11860019840013010492177477)
                ·
                  refine ⟨2223753720002439467283277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11860019840013010492177477 2223753720002439467283277)
                  ·
                    refine ⟨833907645000914800231229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223753720002439467283277 833907645000914800231229)
                    ·
                      rfl

theorem cell22_2436044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_2436044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436044 prefixEnd_2436044 := by exact prefixLift 2436044
  have htrace : WordTrace (prefixWord ++ tailWord_2436044) baseStart_2436044 baseEnd_2436044 := by
    simpa [prefixWord, tailWord_2436044, baseEnd_2436044] using wordTrace_append hprefix tailTrace_2436044
  have hstable : (prefixWord ++ tailWord_2436044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436044).length < 2 ^ (prefixWord ++ tailWord_2436044).sum := by decide
  have hdescent : baseEnd_2436044 < baseStart_2436044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436046 : List Nat := [4, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_2436046 : Nat := 118140960795 + 2436046 * 2 ^ 59
def prefixEnd_2436046 : Nat := 4983230072969 + 3 ^ 40 * 2436046 * 2
def baseEnd_2436046 : Nat := 277969443213929153893741

theorem tailTrace_2436046 : CollatzResearch.WordTrace tailWord_2436046 prefixEnd_2436046 277969443213929153893741 := by
  unfold tailWord_2436046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106237116578607547373999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59233264621752573585994661 11106237116578607547373999)
  ·
    refine ⟨16659355674867911321060999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11106237116578607547373999 16659355674867911321060999)
    ·
      refine ⟨24989033512301866981591499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16659355674867911321060999 24989033512301866981591499)
      ·
        refine ⟨37483550268452800472387249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24989033512301866981591499 37483550268452800472387249)
        ·
          refine ⟨28112662701339600354290437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37483550268452800472387249 28112662701339600354290437)
          ·
            refine ⟨5271124256501175066429457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28112662701339600354290437 5271124256501175066429457)
            ·
              refine ⟨3953343192375881299822093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271124256501175066429457 3953343192375881299822093)
              ·
                refine ⟨1482503697140955487433285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3953343192375881299822093 1482503697140955487433285)
                ·
                  refine ⟨277969443213929153893741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482503697140955487433285 277969443213929153893741)
                  ·
                    rfl

theorem cell22_2436046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_2436046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436046 prefixEnd_2436046 := by exact prefixLift 2436046
  have htrace : WordTrace (prefixWord ++ tailWord_2436046) baseStart_2436046 baseEnd_2436046 := by
    simpa [prefixWord, tailWord_2436046, baseEnd_2436046] using wordTrace_append hprefix tailTrace_2436046
  have hstable : (prefixWord ++ tailWord_2436046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436046).length < 2 ^ (prefixWord ++ tailWord_2436046).sum := by decide
  have hdescent : baseEnd_2436046 < baseStart_2436046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436057 : List Nat := [1, 2, 1, 2, 5, 2, 9]
def baseStart_2436057 : Nat := 118140960795 + 2436057 * 2 ^ 59
def prefixEnd_2436057 : Nat := 4983230072969 + 3 ^ 40 * 2436057 * 2
def baseEnd_2436057 : Nat := 30885633154318040728007

theorem tailTrace_2436057 : CollatzResearch.WordTrace tailWord_2436057 prefixEnd_2436057 30885633154318040728007 := by
  unfold tailWord_2436057
  simp only [CollatzResearch.WordTrace]
  refine ⟨88850298135589009257642425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59233532090392672838428283 88850298135589009257642425)
  ·
    refine ⟨66637723601691756943231819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88850298135589009257642425 66637723601691756943231819)
    ·
      refine ⟨99956585402537635414847729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66637723601691756943231819 99956585402537635414847729)
      ·
        refine ⟨74967439051903226561135797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99956585402537635414847729 74967439051903226561135797)
        ·
          refine ⟨7028197411115927490106481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74967439051903226561135797 7028197411115927490106481)
          ·
            refine ⟨5271148058336945617579861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7028197411115927490106481 5271148058336945617579861)
            ·
              refine ⟨30885633154318040728007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5271148058336945617579861 30885633154318040728007)
              ·
                rfl

theorem cell22_2436057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 9].length) (baseStart_2436057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436057 prefixEnd_2436057 := by exact prefixLift 2436057
  have htrace : WordTrace (prefixWord ++ tailWord_2436057) baseStart_2436057 baseEnd_2436057 := by
    simpa [prefixWord, tailWord_2436057, baseEnd_2436057] using wordTrace_append hprefix tailTrace_2436057
  have hstable : (prefixWord ++ tailWord_2436057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436057).length < 2 ^ (prefixWord ++ tailWord_2436057).sum := by decide
  have hdescent : baseEnd_2436057 < baseStart_2436057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436061 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_2436061 : Nat := 118140960795 + 2436061 * 2 ^ 59
def prefixEnd_2436061 : Nat := 4983230072969 + 3 ^ 40 * 2436061 * 2
def baseEnd_2436061 : Nat := 833913464448332422556177

theorem tailTrace_2436061 : CollatzResearch.WordTrace tailWord_2436061 prefixEnd_2436061 833913464448332422556177 := by
  unfold tailWord_2436061
  simp only [CollatzResearch.WordTrace]
  refine ⟨88850444027574517940788037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59233629351716345293858691 88850444027574517940788037)
  ·
    refine ⟨16659458255170222113897757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88850444027574517940788037 16659458255170222113897757)
    ·
      refine ⟨6247296845688833292711659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16659458255170222113897757 6247296845688833292711659)
      ·
        refine ⟨9370945268533249939067489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6247296845688833292711659 9370945268533249939067489)
        ·
          refine ⟨7028208951399937454300617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9370945268533249939067489 7028208951399937454300617)
          ·
            refine ⟨5271156713549953090725463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7028208951399937454300617 5271156713549953090725463)
            ·
              refine ⟨7906735070324929636088195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271156713549953090725463 7906735070324929636088195)
              ·
                refine ⟨11860102605487394454132293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7906735070324929636088195 11860102605487394454132293)
                ·
                  refine ⟨2223769238528886460149805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11860102605487394454132293 2223769238528886460149805)
                  ·
                    refine ⟨833913464448332422556177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223769238528886460149805 833913464448332422556177)
                    ·
                      rfl

theorem cell22_2436061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_2436061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436061 prefixEnd_2436061 := by exact prefixLift 2436061
  have htrace : WordTrace (prefixWord ++ tailWord_2436061) baseStart_2436061 baseEnd_2436061 := by
    simpa [prefixWord, tailWord_2436061, baseEnd_2436061] using wordTrace_append hprefix tailTrace_2436061
  have hstable : (prefixWord ++ tailWord_2436061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436061).length < 2 ^ (prefixWord ++ tailWord_2436061).sum := by decide
  have hdescent : baseEnd_2436061 < baseStart_2436061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436078 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_2436078 : Nat := 118140960795 + 2436078 * 2 ^ 59
def prefixEnd_2436078 : Nat := 4983230072969 + 3 ^ 40 * 2436078 * 2
def baseEnd_2436078 : Nat := 833919283895750044881125

theorem tailTrace_2436078 : CollatzResearch.WordTrace tailWord_2436078 prefixEnd_2436078 833919283895750044881125 := by
  unfold tailWord_2436078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106383008564116230519611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59234042712341953229437925 11106383008564116230519611)
  ·
    refine ⟨16659574512846174345779417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11106383008564116230519611 16659574512846174345779417)
    ·
      refine ⟨12494680884634630759334563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16659574512846174345779417 12494680884634630759334563)
      ·
        refine ⟨18742021326951946139001845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12494680884634630759334563 18742021326951946139001845)
        ·
          refine ⟨1757064499401744950531423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18742021326951946139001845 1757064499401744950531423)
          ·
            refine ⟨2635596749102617425797135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757064499401744950531423 2635596749102617425797135)
            ·
              refine ⟨3953395123653926138695703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635596749102617425797135 3953395123653926138695703)
              ·
                refine ⟨5930092685480889208043555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953395123653926138695703 5930092685480889208043555)
                ·
                  refine ⟨8895139028221333812065333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5930092685480889208043555 8895139028221333812065333)
                  ·
                    refine ⟨833919283895750044881125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8895139028221333812065333 833919283895750044881125)
                    ·
                      rfl

theorem cell22_2436078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_2436078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436078 prefixEnd_2436078 := by exact prefixLift 2436078
  have htrace : WordTrace (prefixWord ++ tailWord_2436078) baseStart_2436078 baseEnd_2436078 := by
    simpa [prefixWord, tailWord_2436078, baseEnd_2436078] using wordTrace_append hprefix tailTrace_2436078
  have hstable : (prefixWord ++ tailWord_2436078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436078).length < 2 ^ (prefixWord ++ tailWord_2436078).sum := by decide
  have hdescent : baseEnd_2436078 < baseStart_2436078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436089 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 3, 3]
def baseStart_2436089 : Nat := 118140960795 + 2436089 * 2 ^ 59
def prefixEnd_2436089 : Nat := 4983230072969 + 3 ^ 40 * 2436089 * 2
def baseEnd_2436089 : Nat := 833923049420549682856091

theorem tailTrace_2436089 : CollatzResearch.WordTrace tailWord_2436089 prefixEnd_2436089 833923049420549682856091 := by
  unfold tailWord_2436089
  simp only [CollatzResearch.WordTrace]
  refine ⟨88851465271473078722807321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59234310180982052481871547 88851465271473078722807321)
  ·
    refine ⟨66638598953604809042105491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88851465271473078722807321 66638598953604809042105491)
    ·
      refine ⟨99957898430407213563158237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66638598953604809042105491 99957898430407213563158237)
      ·
        refine ⟨37484211911402705086184339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99957898430407213563158237 37484211911402705086184339)
        ·
          refine ⟨56226317867104057629276509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37484211911402705086184339 56226317867104057629276509)
          ·
            refine ⟨21084869200164021610978691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56226317867104057629276509 21084869200164021610978691)
            ·
              refine ⟨31627303800246032416468037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21084869200164021610978691 31627303800246032416468037)
              ·
                refine ⟨5930119462546131078087757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31627303800246032416468037 5930119462546131078087757)
                ·
                  refine ⟨2223794798454799154282909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5930119462546131078087757 2223794798454799154282909)
                  ·
                    refine ⟨833923049420549682856091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223794798454799154282909 833923049420549682856091)
                    ·
                      rfl

theorem cell22_2436089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_2436089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436089 prefixEnd_2436089 := by exact prefixLift 2436089
  have htrace : WordTrace (prefixWord ++ tailWord_2436089) baseStart_2436089 baseEnd_2436089 := by
    simpa [prefixWord, tailWord_2436089, baseEnd_2436089] using wordTrace_append hprefix tailTrace_2436089
  have hstable : (prefixWord ++ tailWord_2436089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436089).length < 2 ^ (prefixWord ++ tailWord_2436089).sum := by decide
  have hdescent : baseEnd_2436089 < baseStart_2436089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436119 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 7]
def baseStart_2436119 : Nat := 118140960795 + 2436119 * 2 ^ 59
def prefixEnd_2436119 : Nat := 4983230072969 + 3 ^ 40 * 2436119 * 2
def baseEnd_2436119 : Nat := 277977773011213201535333

theorem tailTrace_2436119 : CollatzResearch.WordTrace tailWord_2436119 prefixEnd_2436119 277977773011213201535333 := by
  unfold tailWord_2436119
  simp only [CollatzResearch.WordTrace]
  refine ⟨88852559461364393846399411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59235039640909595897599607 88852559461364393846399411)
  ·
    refine ⟨133278839192046590769599117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88852559461364393846399411 133278839192046590769599117)
    ·
      refine ⟨49979564697017471538599669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133278839192046590769599117 49979564697017471538599669)
      ·
        refine ⟨4685584190345387956743719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49979564697017471538599669 4685584190345387956743719)
        ·
          refine ⟨7028376285518081935115579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685584190345387956743719 7028376285518081935115579)
          ·
            refine ⟨10542564428277122902673369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7028376285518081935115579 10542564428277122902673369)
            ·
              refine ⟨7906923321207842177005027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10542564428277122902673369 7906923321207842177005027)
              ·
                refine ⟨11860384981811763265507541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7906923321207842177005027 11860384981811763265507541)
                ·
                  refine ⟨277977773011213201535333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11860384981811763265507541 277977773011213201535333)
                  ·
                    rfl

theorem cell22_2436119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 7].length) (baseStart_2436119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436119 prefixEnd_2436119 := by exact prefixLift 2436119
  have htrace : WordTrace (prefixWord ++ tailWord_2436119) baseStart_2436119 baseEnd_2436119 := by
    simpa [prefixWord, tailWord_2436119, baseEnd_2436119] using wordTrace_append hprefix tailTrace_2436119
  have hstable : (prefixWord ++ tailWord_2436119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436119).length < 2 ^ (prefixWord ++ tailWord_2436119).sum := by decide
  have hdescent : baseEnd_2436119 < baseStart_2436119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436147 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 8]
def baseStart_2436147 : Nat := 118140960795 + 2436147 * 2 ^ 59
def prefixEnd_2436147 : Nat := 4983230072969 + 3 ^ 40 * 2436147 * 2
def baseEnd_2436147 : Nat := 277980968001952288301971

theorem tailTrace_2436147 : CollatzResearch.WordTrace tailWord_2436147 prefixEnd_2436147 277980968001952288301971 := by
  unfold tailWord_2436147
  simp only [CollatzResearch.WordTrace]
  refine ⟨88853580705262954628418695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59235720470175303085612463 88853580705262954628418695)
  ·
    refine ⟨133280371057894431942628043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88853580705262954628418695 133280371057894431942628043)
    ·
      refine ⟨199920556586841647913942065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133280371057894431942628043 199920556586841647913942065)
      ·
        refine ⟨149940417440131235935456549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199920556586841647913942065 149940417440131235935456549)
        ·
          refine ⟨28113828270024606737898103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149940417440131235935456549 28113828270024606737898103)
          ·
            refine ⟨42170742405036910106847155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28113828270024606737898103 42170742405036910106847155)
            ·
              refine ⟨63256113607555365160270733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42170742405036910106847155 63256113607555365160270733)
              ·
                refine ⟨23721042602833261935101525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63256113607555365160270733 23721042602833261935101525)
                ·
                  refine ⟨277980968001952288301971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23721042602833261935101525 277980968001952288301971)
                  ·
                    rfl

theorem cell22_2436147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_2436147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436147 prefixEnd_2436147 := by exact prefixLift 2436147
  have htrace : WordTrace (prefixWord ++ tailWord_2436147) baseStart_2436147 baseEnd_2436147 := by
    simpa [prefixWord, tailWord_2436147, baseEnd_2436147] using wordTrace_append hprefix tailTrace_2436147
  have hstable : (prefixWord ++ tailWord_2436147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436147).length < 2 ^ (prefixWord ++ tailWord_2436147).sum := by decide
  have hdescent : baseEnd_2436147 < baseStart_2436147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436181 : List Nat := [1, 3, 2, 2, 1, 2, 3, 4, 4]
def baseStart_2436181 : Nat := 118140960795 + 2436181 * 2 ^ 59
def prefixEnd_2436181 : Nat := 4983230072969 + 3 ^ 40 * 2436181 * 2
def baseEnd_2436181 : Nat := 277984847633564036518603

theorem tailTrace_2436181 : CollatzResearch.WordTrace tailWord_2436181 prefixEnd_2436181 277984847633564036518603 := by
  unfold tailWord_2436181
  simp only [CollatzResearch.WordTrace]
  refine ⟨88854820787139778435156397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59236547191426518956770931 88854820787139778435156397)
  ·
    refine ⟨33320557795177416913183649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88854820787139778435156397 33320557795177416913183649)
    ·
      refine ⟨24990418346383062684887737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33320557795177416913183649 24990418346383062684887737)
      ·
        refine ⟨18742813759787297013665803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24990418346383062684887737 18742813759787297013665803)
        ·
          refine ⟨28114220639680945520498705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18742813759787297013665803 28114220639680945520498705)
          ·
            refine ⟨21085665479760709140374029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28114220639680945520498705 21085665479760709140374029)
            ·
              refine ⟨7907124554910265927640261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21085665479760709140374029 7907124554910265927640261)
              ·
                refine ⟨1482585854045674861432549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7907124554910265927640261 1482585854045674861432549)
                ·
                  refine ⟨277984847633564036518603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482585854045674861432549 277984847633564036518603)
                  ·
                    rfl

theorem cell22_2436181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_2436181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436181 prefixEnd_2436181 := by exact prefixLift 2436181
  have htrace : WordTrace (prefixWord ++ tailWord_2436181) baseStart_2436181 baseEnd_2436181 := by
    simpa [prefixWord, tailWord_2436181, baseEnd_2436181] using wordTrace_append hprefix tailTrace_2436181
  have hstable : (prefixWord ++ tailWord_2436181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436181).length < 2 ^ (prefixWord ++ tailWord_2436181).sum := by decide
  have hdescent : baseEnd_2436181 < baseStart_2436181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436292 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2436292 : Nat := 118140960795 + 2436292 * 2 ^ 59
def prefixEnd_2436292 : Nat := 4983230072969 + 3 ^ 40 * 2436292 * 2
def baseEnd_2436292 : Nat := 833992540469124820030469

theorem tailTrace_2436292 : CollatzResearch.WordTrace tailWord_2436292 prefixEnd_2436292 833992540469124820030469 := by
  unfold tailWord_2436292
  simp only [CollatzResearch.WordTrace]
  refine ⟨44429434644868822196223565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59239246193158429594964753 44429434644868822196223565)
  ·
    refine ⟨16661037991825808323583837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44429434644868822196223565 16661037991825808323583837)
    ·
      refine ⟨6247889246934678121343939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16661037991825808323583837 6247889246934678121343939)
      ·
        refine ⟨9371833870402017182015909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6247889246934678121343939 9371833870402017182015909)
        ·
          refine ⟨1757218850700378221627983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9371833870402017182015909 1757218850700378221627983)
          ·
            refine ⟨2635828276050567332441975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757218850700378221627983 2635828276050567332441975)
            ·
              refine ⟨3953742414075850998662963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635828276050567332441975 3953742414075850998662963)
              ·
                refine ⟨5930613621113776497994445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953742414075850998662963 5930613621113776497994445)
                ·
                  refine ⟨2223980107917666186747917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5930613621113776497994445 2223980107917666186747917)
                  ·
                    refine ⟨833992540469124820030469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2223980107917666186747917 833992540469124820030469)
                    ·
                      rfl

theorem cell22_2436292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2436292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436292 prefixEnd_2436292 := by exact prefixLift 2436292
  have htrace : WordTrace (prefixWord ++ tailWord_2436292) baseStart_2436292 baseEnd_2436292 := by
    simpa [prefixWord, tailWord_2436292, baseEnd_2436292] using wordTrace_append hprefix tailTrace_2436292
  have hstable : (prefixWord ++ tailWord_2436292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436292).length < 2 ^ (prefixWord ++ tailWord_2436292).sum := by decide
  have hdescent : baseEnd_2436292 < baseStart_2436292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436299 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 6]
def baseStart_2436299 : Nat := 118140960795 + 2436299 * 2 ^ 59
def prefixEnd_2436299 : Nat := 4983230072969 + 3 ^ 40 * 2436299 * 2
def baseEnd_2436299 : Nat := 277998312237393045035149

theorem tailTrace_2436299 : CollatzResearch.WordTrace tailWord_2436299 prefixEnd_2436299 277998312237393045035149 := by
  unfold tailWord_2436299
  simp only [CollatzResearch.WordTrace]
  refine ⟨88859124600712284587951951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59239416400474856391967967 88859124600712284587951951)
  ·
    refine ⟨133288686901068426881927927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88859124600712284587951951 133288686901068426881927927)
    ·
      refine ⟨199933030351602640322891891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133288686901068426881927927 199933030351602640322891891)
      ·
        refine ⟨299899545527403960484337837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199933030351602640322891891 299899545527403960484337837)
        ·
          refine ⟨112462329572776485181626689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299899545527403960484337837 112462329572776485181626689)
          ·
            refine ⟨84346747179582363886220017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112462329572776485181626689 84346747179582363886220017)
            ·
              refine ⟨63260060384686772914665013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84346747179582363886220017 63260060384686772914665013)
              ·
                refine ⟨5930630661064384960749845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63260060384686772914665013 5930630661064384960749845)
                ·
                  refine ⟨277998312237393045035149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5930630661064384960749845 277998312237393045035149)
                  ·
                    rfl

theorem cell22_2436299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 6].length) (baseStart_2436299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436299 prefixEnd_2436299 := by exact prefixLift 2436299
  have htrace : WordTrace (prefixWord ++ tailWord_2436299) baseStart_2436299 baseEnd_2436299 := by
    simpa [prefixWord, tailWord_2436299, baseEnd_2436299] using wordTrace_append hprefix tailTrace_2436299
  have hstable : (prefixWord ++ tailWord_2436299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436299).length < 2 ^ (prefixWord ++ tailWord_2436299).sum := by decide
  have hdescent : baseEnd_2436299 < baseStart_2436299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436331 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 1, 5]
def baseStart_2436331 : Nat := 118140960795 + 2436331 * 2 ^ 59
def prefixEnd_2436331 : Nat := 4983230072969 + 3 ^ 40 * 2436331 * 2
def baseEnd_2436331 : Nat := 834005890966141718305349

theorem tailTrace_2436331 : CollatzResearch.WordTrace tailWord_2436331 prefixEnd_2436331 834005890966141718305349 := by
  unfold tailWord_2436331
  simp only [CollatzResearch.WordTrace]
  refine ⟨88860291736596354053116847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59240194491064236035411231 88860291736596354053116847)
  ·
    refine ⟨133290437604894531079675271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88860291736596354053116847 133290437604894531079675271)
    ·
      refine ⟨199935656407341796619512907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133290437604894531079675271 199935656407341796619512907)
      ·
        refine ⟨299903484611012694929269361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199935656407341796619512907 299903484611012694929269361)
        ·
          refine ⟨224927613458259521196952021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299903484611012694929269361 224927613458259521196952021)
          ·
            refine ⟨5271740940427957528053563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 224927613458259521196952021 5271740940427957528053563)
            ·
              refine ⟨7907611410641936292080345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271740940427957528053563 7907611410641936292080345)
              ·
                refine ⟨5930708557981452219060259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7907611410641936292080345 5930708557981452219060259)
                ·
                  refine ⟨8896062836972178328590389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5930708557981452219060259 8896062836972178328590389)
                  ·
                    refine ⟨834005890966141718305349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8896062836972178328590389 834005890966141718305349)
                    ·
                      rfl

theorem cell22_2436331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_2436331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436331 prefixEnd_2436331 := by exact prefixLift 2436331
  have htrace : WordTrace (prefixWord ++ tailWord_2436331) baseStart_2436331 baseEnd_2436331 := by
    simpa [prefixWord, tailWord_2436331, baseEnd_2436331] using wordTrace_append hprefix tailTrace_2436331
  have hstable : (prefixWord ++ tailWord_2436331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436331).length < 2 ^ (prefixWord ++ tailWord_2436331).sum := by decide
  have hdescent : baseEnd_2436331 < baseStart_2436331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436335 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 1, 4]
def baseStart_2436335 : Nat := 118140960795 + 2436335 * 2 ^ 59
def prefixEnd_2436335 : Nat := 4983230072969 + 3 ^ 40 * 2436335 * 2
def baseEnd_2436335 : Nat := 834007260247887041205337

theorem tailTrace_2436335 : CollatzResearch.WordTrace tailWord_2436335 prefixEnd_2436335 834007260247887041205337 := by
  unfold tailWord_2436335
  simp only [CollatzResearch.WordTrace]
  refine ⟨88860437628581862736262459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59240291752387908490841639 88860437628581862736262459)
  ·
    refine ⟨133290656442872794104393689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88860437628581862736262459 133290656442872794104393689)
    ·
      refine ⟨99967992332154595578295267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133290656442872794104393689 99967992332154595578295267)
      ·
        refine ⟨149951988498231893367442901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99967992332154595578295267 149951988498231893367442901)
        ·
          refine ⟨3514499730427310000799443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 149951988498231893367442901 3514499730427310000799443)
          ·
            refine ⟨5271749595640965001199165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514499730427310000799443 5271749595640965001199165)
            ·
              refine ⟨1976906098365361875449687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5271749595640965001199165 1976906098365361875449687)
              ·
                refine ⟨2965359147548042813174531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1976906098365361875449687 2965359147548042813174531)
                ·
                  refine ⟨4448038721322064219761797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965359147548042813174531 4448038721322064219761797)
                  ·
                    refine ⟨834007260247887041205337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448038721322064219761797 834007260247887041205337)
                    ·
                      rfl

theorem cell22_2436335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_2436335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436335 prefixEnd_2436335 := by exact prefixLift 2436335
  have htrace : WordTrace (prefixWord ++ tailWord_2436335) baseStart_2436335 baseEnd_2436335 := by
    simpa [prefixWord, tailWord_2436335, baseEnd_2436335] using wordTrace_append hprefix tailTrace_2436335
  have hstable : (prefixWord ++ tailWord_2436335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436335).length < 2 ^ (prefixWord ++ tailWord_2436335).sum := by decide
  have hdescent : baseEnd_2436335 < baseStart_2436335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436346 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_2436346 : Nat := 118140960795 + 2436346 * 2 ^ 59
def prefixEnd_2436346 : Nat := 4983230072969 + 3 ^ 40 * 2436346 * 2
def baseEnd_2436346 : Nat := 834011025772686679180303

theorem tailTrace_2436346 : CollatzResearch.WordTrace tailWord_2436346 prefixEnd_2436346 834011025772686679180303 := by
  unfold tailWord_2436346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22215209707885502903728223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59240559221028007743275261 22215209707885502903728223)
  ·
    refine ⟨33322814561828254355592335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22215209707885502903728223 33322814561828254355592335)
    ·
      refine ⟨49984221842742381533388503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33322814561828254355592335 49984221842742381533388503)
      ·
        refine ⟨74976332764113572300082755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49984221842742381533388503 74976332764113572300082755)
        ·
          refine ⟨112464499146170358450124133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74976332764113572300082755 112464499146170358450124133)
          ·
            refine ⟨21087093589906942209398275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112464499146170358450124133 21087093589906942209398275)
            ·
              refine ⟨31630640384860413314097413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21087093589906942209398275 31630640384860413314097413)
              ·
                refine ⟨5930745072161327496393265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31630640384860413314097413 5930745072161327496393265)
                ·
                  refine ⟨4448058804120995622294949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5930745072161327496393265 4448058804120995622294949)
                  ·
                    refine ⟨834011025772686679180303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448058804120995622294949 834011025772686679180303)
                    ·
                      rfl

theorem cell22_2436346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_2436346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436346 prefixEnd_2436346 := by exact prefixLift 2436346
  have htrace : WordTrace (prefixWord ++ tailWord_2436346) baseStart_2436346 baseEnd_2436346 := by
    simpa [prefixWord, tailWord_2436346, baseEnd_2436346] using wordTrace_append hprefix tailTrace_2436346
  have hstable : (prefixWord ++ tailWord_2436346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436346).length < 2 ^ (prefixWord ++ tailWord_2436346).sum := by decide
  have hdescent : baseEnd_2436346 < baseStart_2436346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436350 : List Nat := [4, 2, 2, 1, 1, 3, 1, 4, 4]
def baseStart_2436350 : Nat := 118140960795 + 2436350 * 2 ^ 59
def prefixEnd_2436350 : Nat := 4983230072969 + 3 ^ 40 * 2436350 * 2
def baseEnd_2436350 : Nat := 278004131684810667360097

theorem tailTrace_2436350 : CollatzResearch.WordTrace tailWord_2436350 prefixEnd_2436350 278004131684810667360097 := by
  unfold tailWord_2436350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11107623090440940037257313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59240656482351680198705669 11107623090440940037257313)
  ·
    refine ⟨8330717317830705027942985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11107623090440940037257313 8330717317830705027942985)
    ·
      refine ⟨6248037988373028770957239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8330717317830705027942985 6248037988373028770957239)
      ·
        refine ⟨9372056982559543156435859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248037988373028770957239 9372056982559543156435859)
        ·
          refine ⟨14058085473839314734653789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9372056982559543156435859 14058085473839314734653789)
          ·
            refine ⟨5271782052689743025495171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14058085473839314734653789 5271782052689743025495171)
            ·
              refine ⟨7907673079034614538242757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271782052689743025495171 7907673079034614538242757)
              ·
                refine ⟨1482688702318990225920517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7907673079034614538242757 1482688702318990225920517)
                ·
                  refine ⟨278004131684810667360097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482688702318990225920517 278004131684810667360097)
                  ·
                    rfl

theorem cell22_2436350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_2436350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436350 prefixEnd_2436350 := by exact prefixLift 2436350
  have htrace : WordTrace (prefixWord ++ tailWord_2436350) baseStart_2436350 baseEnd_2436350 := by
    simpa [prefixWord, tailWord_2436350, baseEnd_2436350] using wordTrace_append hprefix tailTrace_2436350
  have hstable : (prefixWord ++ tailWord_2436350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436350).length < 2 ^ (prefixWord ++ tailWord_2436350).sum := by decide
  have hdescent : baseEnd_2436350 < baseStart_2436350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436378 : List Nat := [3, 1, 1, 3, 3, 2, 3, 6]
def baseStart_2436378 : Nat := 118140960795 + 2436378 * 2 ^ 59
def prefixEnd_2436378 : Nat := 4983230072969 + 3 ^ 40 * 2436378 * 2
def baseEnd_2436378 : Nat := 92669108891849918042245

theorem tailTrace_2436378 : CollatzResearch.WordTrace tailWord_2436378 prefixEnd_2436378 92669108891849918042245 := by
  unfold tailWord_2436378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22215501491856520270019447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59241337311617387386718525 22215501491856520270019447)
  ·
    refine ⟨33323252237784780405029171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22215501491856520270019447 33323252237784780405029171)
    ·
      refine ⟨49984878356677170607543757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33323252237784780405029171 49984878356677170607543757)
      ·
        refine ⟨18744329383753938977828909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49984878356677170607543757 18744329383753938977828909)
        ·
          refine ⟨7029123518907727116685841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18744329383753938977828909 7029123518907727116685841)
          ·
            refine ⟨5271842639180795337514381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7029123518907727116685841 5271842639180795337514381)
            ·
              refine ⟨1976940989692798251567893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5271842639180795337514381 1976940989692798251567893)
              ·
                refine ⟨92669108891849918042245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1976940989692798251567893 92669108891849918042245)
                ·
                  rfl

theorem cell22_2436378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_2436378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436378 prefixEnd_2436378 := by exact prefixLift 2436378
  have htrace : WordTrace (prefixWord ++ tailWord_2436378) baseStart_2436378 baseEnd_2436378 := by
    simpa [prefixWord, tailWord_2436378, baseEnd_2436378] using wordTrace_append hprefix tailTrace_2436378
  have hstable : (prefixWord ++ tailWord_2436378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436378).length < 2 ^ (prefixWord ++ tailWord_2436378).sum := by decide
  have hdescent : baseEnd_2436378 < baseStart_2436378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436410 : List Nat := [3, 1, 1, 1, 4, 1, 1, 6, 1, 3]
def baseStart_2436410 : Nat := 118140960795 + 2436410 * 2 ^ 59
def prefixEnd_2436410 : Nat := 4983230072969 + 3 ^ 40 * 2436410 * 2
def baseEnd_2436410 : Nat := 834032934280611845580107

theorem tailTrace_2436410 : CollatzResearch.WordTrace tailWord_2436410 prefixEnd_2436410 834032934280611845580107 := by
  unfold tailWord_2436410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22215793275827537636310671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59242115402206767030161789 22215793275827537636310671)
  ·
    refine ⟨33323689913741306454466007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22215793275827537636310671 33323689913741306454466007)
    ·
      refine ⟨49985534870611959681699011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33323689913741306454466007 49985534870611959681699011)
      ·
        refine ⟨74978302305917939522548517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49985534870611959681699011 74978302305917939522548517)
        ·
          refine ⟨14058431682359613660477847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74978302305917939522548517 14058431682359613660477847)
          ·
            refine ⟨21087647523539420490716771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14058431682359613660477847 21087647523539420490716771)
            ·
              refine ⟨31631471285309130736075157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21087647523539420490716771 31631471285309130736075157)
              ·
                refine ⟨1482725216498865503253523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31631471285309130736075157 1482725216498865503253523)
                ·
                  refine ⟨2224087824748298254880285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1482725216498865503253523 2224087824748298254880285)
                  ·
                    refine ⟨834032934280611845580107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2224087824748298254880285 834032934280611845580107)
                    ·
                      rfl

theorem cell22_2436410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_2436410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436410 prefixEnd_2436410 := by exact prefixLift 2436410
  have htrace : WordTrace (prefixWord ++ tailWord_2436410) baseStart_2436410 baseEnd_2436410 := by
    simpa [prefixWord, tailWord_2436410, baseEnd_2436410] using wordTrace_append hprefix tailTrace_2436410
  have hstable : (prefixWord ++ tailWord_2436410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436410).length < 2 ^ (prefixWord ++ tailWord_2436410).sum := by decide
  have hdescent : baseEnd_2436410 < baseStart_2436410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436429 : List Nat := [1, 6, 1, 3, 2, 1, 2, 6]
def baseStart_2436429 : Nat := 118140960795 + 2436429 * 2 ^ 59
def prefixEnd_2436429 : Nat := 4983230072969 + 3 ^ 40 * 2436429 * 2
def baseEnd_2436429 : Nat := 92671048707655792150561

theorem tailTrace_2436429 : CollatzResearch.WordTrace tailWord_2436429 prefixEnd_2436429 92671048707655792150561 := by
  unfold tailWord_2436429
  simp only [CollatzResearch.WordTrace]
  refine ⟨88863866090241316790184341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59242577393494211193456227 88863866090241316790184341)
  ·
    refine ⟨4165493722980061724539891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88863866090241316790184341 4165493722980061724539891)
    ·
      refine ⟨6248240584470092586809837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4165493722980061724539891 6248240584470092586809837)
      ·
        refine ⟨2343090219176284720053689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6248240584470092586809837 2343090219176284720053689)
        ·
          refine ⟨1757317664382213540040267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2343090219176284720053689 1757317664382213540040267)
          ·
            refine ⟨2635976496573320310060401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757317664382213540040267 2635976496573320310060401)
            ·
              refine ⟨1976982372429990232545301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2635976496573320310060401 1976982372429990232545301)
              ·
                refine ⟨92671048707655792150561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1976982372429990232545301 92671048707655792150561)
                ·
                  rfl

theorem cell22_2436429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 6].length) (baseStart_2436429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436429 prefixEnd_2436429 := by exact prefixLift 2436429
  have htrace : WordTrace (prefixWord ++ tailWord_2436429) baseStart_2436429 baseEnd_2436429 := by
    simpa [prefixWord, tailWord_2436429, baseEnd_2436429] using wordTrace_append hprefix tailTrace_2436429
  have hstable : (prefixWord ++ tailWord_2436429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436429).length < 2 ^ (prefixWord ++ tailWord_2436429).sum := by decide
  have hdescent : baseEnd_2436429 < baseStart_2436429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436453 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_2436453 : Nat := 118140960795 + 2436453 * 2 ^ 59
def prefixEnd_2436453 : Nat := 4983230072969 + 3 ^ 40 * 2436453 * 2
def baseEnd_2436453 : Nat := 834047654059374066754975

theorem tailTrace_2436453 : CollatzResearch.WordTrace tailWord_2436453 prefixEnd_2436453 834047654059374066754975 := by
  unfold tailWord_2436453
  simp only [CollatzResearch.WordTrace]
  refine ⟨88864741442154368889058013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59243160961436245926038675 88864741442154368889058013)
  ·
    refine ⟨33324278040807888333396755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88864741442154368889058013 33324278040807888333396755)
    ·
      refine ⟨49986417061211832500095133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33324278040807888333396755 49986417061211832500095133)
      ·
        refine ⟨18744906397954437187535675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49986417061211832500095133 18744906397954437187535675)
        ·
          refine ⟨28117359596931655781303513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18744906397954437187535675 28117359596931655781303513)
          ·
            refine ⟨21088019697698741835977635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28117359596931655781303513 21088019697698741835977635)
            ·
              refine ⟨31632029546548112753966453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21088019697698741835977635 31632029546548112753966453)
              ·
                refine ⟨2965502769988885570684355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31632029546548112753966453 2965502769988885570684355)
                ·
                  refine ⟨4448254154983328356026533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965502769988885570684355 4448254154983328356026533)
                  ·
                    refine ⟨834047654059374066754975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448254154983328356026533 834047654059374066754975)
                    ·
                      rfl

theorem cell22_2436453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_2436453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436453 prefixEnd_2436453 := by exact prefixLift 2436453
  have htrace : WordTrace (prefixWord ++ tailWord_2436453) baseStart_2436453 baseEnd_2436453 := by
    simpa [prefixWord, tailWord_2436453, baseEnd_2436453] using wordTrace_append hprefix tailTrace_2436453
  have hstable : (prefixWord ++ tailWord_2436453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436453).length < 2 ^ (prefixWord ++ tailWord_2436453).sum := by decide
  have hdescent : baseEnd_2436453 < baseStart_2436453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436500 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2436500 : Nat := 118140960795 + 2436500 * 2 ^ 59
def prefixEnd_2436500 : Nat := 4983230072969 + 3 ^ 40 * 2436500 * 2
def baseEnd_2436500 : Nat := 834063743119881610829831

theorem tailTrace_2436500 : CollatzResearch.WordTrace tailWord_2436500 prefixEnd_2436500 834063743119881610829831 := by
  unfold tailWord_2436500
  simp only [CollatzResearch.WordTrace]
  refine ⟨44433227836492047958009477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59244303781989397277345969 44433227836492047958009477)
  ·
    refine ⟨8331230219342258992126777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44433227836492047958009477 8331230219342258992126777)
    ·
      refine ⟨6248422664506694244095083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8331230219342258992126777 6248422664506694244095083)
      ·
        refine ⟨9372633996760041366142625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248422664506694244095083 9372633996760041366142625)
        ·
          refine ⟨7029475497570031024606969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9372633996760041366142625 7029475497570031024606969)
          ·
            refine ⟨5272106623177523268455227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7029475497570031024606969 5272106623177523268455227)
            ·
              refine ⟨7908159934766284902682841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5272106623177523268455227 7908159934766284902682841)
              ·
                refine ⟨5931119951074713677012131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908159934766284902682841 5931119951074713677012131)
                ·
                  refine ⟨8896679926612070515518197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931119951074713677012131 8896679926612070515518197)
                  ·
                    refine ⟨834063743119881610829831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8896679926612070515518197 834063743119881610829831)
                    ·
                      rfl

theorem cell22_2436500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2436500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436500 prefixEnd_2436500 := by exact prefixLift 2436500
  have htrace : WordTrace (prefixWord ++ tailWord_2436500) baseStart_2436500 baseEnd_2436500 := by
    simpa [prefixWord, tailWord_2436500, baseEnd_2436500] using wordTrace_append hprefix tailTrace_2436500
  have hstable : (prefixWord ++ tailWord_2436500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436500).length < 2 ^ (prefixWord ++ tailWord_2436500).sum := by decide
  have hdescent : baseEnd_2436500 < baseStart_2436500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436588 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_2436588 : Nat := 118140960795 + 2436588 * 2 ^ 59
def prefixEnd_2436588 : Nat := 4983230072969 + 3 ^ 40 * 2436588 * 2
def baseEnd_2436588 : Nat := 834093867318278714629561

theorem tailTrace_2436588 : CollatzResearch.WordTrace tailWord_2436588 prefixEnd_2436588 834093867318278714629561 := by
  unfold tailWord_2436588
  simp only [CollatzResearch.WordTrace]
  refine ⟨44434832648332643472611209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59246443531110191296814945 44434832648332643472611209)
  ·
    refine ⟨33326124486249482604458407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44434832648332643472611209 33326124486249482604458407)
    ·
      refine ⟨49989186729374223906687611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33326124486249482604458407 49989186729374223906687611)
      ·
        refine ⟨74983780094061335860031417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49989186729374223906687611 74983780094061335860031417)
        ·
          refine ⟨56237835070546001895023563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74983780094061335860031417 56237835070546001895023563)
          ·
            refine ⟨84356752605819002842535345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56237835070546001895023563 84356752605819002842535345)
            ·
              refine ⟨63267564454364252131901509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84356752605819002842535345 63267564454364252131901509)
              ·
                refine ⟨11862668335193297274731533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63267564454364252131901509 11862668335193297274731533)
                ·
                  refine ⟨4448500625697486478024325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11862668335193297274731533 4448500625697486478024325)
                  ·
                    refine ⟨834093867318278714629561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448500625697486478024325 834093867318278714629561)
                    ·
                      rfl

theorem cell22_2436588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_2436588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436588 prefixEnd_2436588 := by exact prefixLift 2436588
  have htrace : WordTrace (prefixWord ++ tailWord_2436588) baseStart_2436588 baseEnd_2436588 := by
    simpa [prefixWord, tailWord_2436588, baseEnd_2436588] using wordTrace_append hprefix tailTrace_2436588
  have hstable : (prefixWord ++ tailWord_2436588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436588).length < 2 ^ (prefixWord ++ tailWord_2436588).sum := by decide
  have hdescent : baseEnd_2436588 < baseStart_2436588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436605 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_2436605 : Nat := 118140960795 + 2436605 * 2 ^ 59
def prefixEnd_2436605 : Nat := 4983230072969 + 3 ^ 40 * 2436605 * 2
def baseEnd_2436605 : Nat := 834099686765696336954509

theorem tailTrace_2436605 : CollatzResearch.WordTrace tailWord_2436605 prefixEnd_2436605 834099686765696336954509 := by
  unfold tailWord_2436605
  simp only [CollatzResearch.WordTrace]
  refine ⟨88870285337603698848591269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59246856891735799232394179 88870285337603698848591269)
  ·
    refine ⟨16663178500800693534110863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88870285337603698848591269 16663178500800693534110863)
    ·
      refine ⟨24994767751201040301166295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16663178500800693534110863 24994767751201040301166295)
      ·
        refine ⟨37492151626801560451749443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24994767751201040301166295 37492151626801560451749443)
        ·
          refine ⟨56238227440202340677624165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37492151626801560451749443 56238227440202340677624165)
          ·
            refine ⟨10544667645037938877054531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56238227440202340677624165 10544667645037938877054531)
            ·
              refine ⟨15817001467556908315581797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10544667645037938877054531 15817001467556908315581797)
              ·
                refine ⟨2965687775166920309171587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15817001467556908315581797 2965687775166920309171587)
                ·
                  refine ⟨4448531662750380463757381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965687775166920309171587 4448531662750380463757381)
                  ·
                    refine ⟨834099686765696336954509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448531662750380463757381 834099686765696336954509)
                    ·
                      rfl

theorem cell22_2436605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_2436605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436605 prefixEnd_2436605 := by exact prefixLift 2436605
  have htrace : WordTrace (prefixWord ++ tailWord_2436605) baseStart_2436605 baseEnd_2436605 := by
    simpa [prefixWord, tailWord_2436605, baseEnd_2436605] using wordTrace_append hprefix tailTrace_2436605
  have hstable : (prefixWord ++ tailWord_2436605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436605).length < 2 ^ (prefixWord ++ tailWord_2436605).sum := by decide
  have hdescent : baseEnd_2436605 < baseStart_2436605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436650 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2436650 : Nat := 118140960795 + 2436650 * 2 ^ 59
def prefixEnd_2436650 : Nat := 4983230072969 + 3 ^ 40 * 2436650 * 2
def baseEnd_2436650 : Nat := 834115091185331219579371

theorem tailTrace_2436650 : CollatzResearch.WordTrace tailWord_2436650 prefixEnd_2436650 834115091185331219579371 := by
  unfold tailWord_2436650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22217981655610167883494851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59247951081627114355986269 22217981655610167883494851)
  ·
    refine ⟨33326972483415251825242277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22217981655610167883494851 33326972483415251825242277)
    ·
      refine ⟨6248807340640359717232927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33326972483415251825242277 6248807340640359717232927)
      ·
        refine ⟨9373211010960539575849391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248807340640359717232927 9373211010960539575849391)
        ·
          refine ⟨14059816516440809363774087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9373211010960539575849391 14059816516440809363774087)
          ·
            refine ⟨21089724774661214045661131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14059816516440809363774087 21089724774661214045661131)
            ·
              refine ⟨31634587161991821068491697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21089724774661214045661131 31634587161991821068491697)
              ·
                refine ⟨23725940371493865801368773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31634587161991821068491697 23725940371493865801368773)
                ·
                  refine ⟨4448613819655099837756645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23725940371493865801368773 4448613819655099837756645)
                  ·
                    refine ⟨834115091185331219579371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448613819655099837756645 834115091185331219579371)
                    ·
                      rfl

theorem cell22_2436650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2436650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436650 prefixEnd_2436650 := by exact prefixLift 2436650
  have htrace : WordTrace (prefixWord ++ tailWord_2436650) baseStart_2436650 baseEnd_2436650 := by
    simpa [prefixWord, tailWord_2436650, baseEnd_2436650] using wordTrace_append hprefix tailTrace_2436650
  have hstable : (prefixWord ++ tailWord_2436650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436650).length < 2 ^ (prefixWord ++ tailWord_2436650).sum := by decide
  have hdescent : baseEnd_2436650 < baseStart_2436650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436804 : List Nat := [2, 3, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2436804 : Nat := 118140960795 + 2436804 * 2 ^ 59
def prefixEnd_2436804 : Nat := 4983230072969 + 3 ^ 40 * 2436804 * 2
def baseEnd_2436804 : Nat := 834167808532526151228899

theorem tailTrace_2436804 : CollatzResearch.WordTrace tailWord_2436804 prefixEnd_2436804 834167808532526151228899 := by
  unfold tailWord_2436804
  simp only [CollatzResearch.WordTrace]
  refine ⟨44438771731941377917542733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59251695642588503890056977 44438771731941377917542733)
  ·
    refine ⟨16664539399478016719078525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44438771731941377917542733 16664539399478016719078525)
    ·
      refine ⟨6249202274804256269654447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16664539399478016719078525 6249202274804256269654447)
      ·
        refine ⟨9373803412206384404481671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6249202274804256269654447 9373803412206384404481671)
        ·
          refine ⟨14060705118309576606722507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9373803412206384404481671 14060705118309576606722507)
          ·
            refine ⟨21091057677464364910083761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14060705118309576606722507 21091057677464364910083761)
            ·
              refine ⟨15818293258098273682562821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21091057677464364910083761 15818293258098273682562821)
              ·
                refine ⟨2965929985893426315480529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15818293258098273682562821 2965929985893426315480529)
                ·
                  refine ⟨2224447489420069736610397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2965929985893426315480529 2224447489420069736610397)
                  ·
                    refine ⟨834167808532526151228899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2224447489420069736610397 834167808532526151228899)
                    ·
                      rfl

theorem cell22_2436804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2436804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436804 prefixEnd_2436804 := by exact prefixLift 2436804
  have htrace : WordTrace (prefixWord ++ tailWord_2436804) baseStart_2436804 baseEnd_2436804 := by
    simpa [prefixWord, tailWord_2436804, baseEnd_2436804] using wordTrace_append hprefix tailTrace_2436804
  have hstable : (prefixWord ++ tailWord_2436804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436804).length < 2 ^ (prefixWord ++ tailWord_2436804).sum := by decide
  have hdescent : baseEnd_2436804 < baseStart_2436804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436806 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2436806 : Nat := 118140960795 + 2436806 * 2 ^ 59
def prefixEnd_2436806 : Nat := 4983230072969 + 3 ^ 40 * 2436806 * 2
def baseEnd_2436806 : Nat := 278056164391132937559631

theorem tailTrace_2436806 : CollatzResearch.WordTrace tailWord_2436806 prefixEnd_2436806 278056164391132937559631 := by
  unfold tailWord_2436806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777425512808609693020571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59251744273250340117772181 2777425512808609693020571)
  ·
    refine ⟨4166138269212914539530857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777425512808609693020571 4166138269212914539530857)
    ·
      refine ⟨3124603701909685904648143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4166138269212914539530857 3124603701909685904648143)
      ·
        refine ⟨4686905552864528856972215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124603701909685904648143 4686905552864528856972215)
        ·
          refine ⟨7030358329296793285458323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4686905552864528856972215 7030358329296793285458323)
          ·
            refine ⟨10545537493945189928187485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030358329296793285458323 10545537493945189928187485)
            ·
              refine ⟨3954576560229446223070307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10545537493945189928187485 3954576560229446223070307)
              ·
                refine ⟨5931864840344169334605461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954576560229446223070307 5931864840344169334605461)
                ·
                  refine ⟨278056164391132937559631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5931864840344169334605461 278056164391132937559631)
                  ·
                    rfl

theorem cell22_2436806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2436806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436806 prefixEnd_2436806 := by exact prefixLift 2436806
  have htrace : WordTrace (prefixWord ++ tailWord_2436806) baseStart_2436806 baseEnd_2436806 := by
    simpa [prefixWord, tailWord_2436806, baseEnd_2436806] using wordTrace_append hprefix tailTrace_2436806
  have hstable : (prefixWord ++ tailWord_2436806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436806).length < 2 ^ (prefixWord ++ tailWord_2436806).sum := by decide
  have hdescent : baseEnd_2436806 < baseStart_2436806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436832 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 3, 3]
def baseStart_2436832 : Nat := 118140960795 + 2436832 * 2 ^ 59
def prefixEnd_2436832 : Nat := 4983230072969 + 3 ^ 40 * 2436832 * 2
def baseEnd_2436832 : Nat := 834177393504743411528813

theorem tailTrace_2436832 : CollatzResearch.WordTrace tailWord_2436832 prefixEnd_2436832 834177393504743411528813 := by
  unfold tailWord_2436832
  simp only [CollatzResearch.WordTrace]
  refine ⟨44439282353890658308552375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59252376471854211078069833 44439282353890658308552375)
  ·
    refine ⟨66658923530835987462828563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44439282353890658308552375 66658923530835987462828563)
    ·
      refine ⟨99988385296253981194242845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66658923530835987462828563 99988385296253981194242845)
      ·
        refine ⟨37495644486095242947841067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99988385296253981194242845 37495644486095242947841067)
        ·
          refine ⟨56243466729142864421761601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37495644486095242947841067 56243466729142864421761601)
          ·
            refine ⟨42182600046857148316321201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56243466729142864421761601 42182600046857148316321201)
            ·
              refine ⟨31636950035142861237240901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42182600046857148316321201 31636950035142861237240901)
              ·
                refine ⟨5931928131589286481982669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31636950035142861237240901 5931928131589286481982669)
                ·
                  refine ⟨2224473049345982430743501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5931928131589286481982669 2224473049345982430743501)
                  ·
                    refine ⟨834177393504743411528813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2224473049345982430743501 834177393504743411528813)
                    ·
                      rfl

theorem cell22_2436832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 3].length) (baseStart_2436832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436832 prefixEnd_2436832 := by exact prefixLift 2436832
  have htrace : WordTrace (prefixWord ++ tailWord_2436832) baseStart_2436832 baseEnd_2436832 := by
    simpa [prefixWord, tailWord_2436832, baseEnd_2436832] using wordTrace_append hprefix tailTrace_2436832
  have hstable : (prefixWord ++ tailWord_2436832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436832).length < 2 ^ (prefixWord ++ tailWord_2436832).sum := by decide
  have hdescent : baseEnd_2436832 < baseStart_2436832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436892 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_2436892 : Nat := 118140960795 + 2436892 * 2 ^ 59
def prefixEnd_2436892 : Nat := 4983230072969 + 3 ^ 40 * 2436892 * 2
def baseEnd_2436892 : Nat := 834197932730923255028629

theorem tailTrace_2436892 : CollatzResearch.WordTrace tailWord_2436892 prefixEnd_2436892 834197932730923255028629 := by
  unfold tailWord_2436892
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440376543781973432144465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59253835391709297909525953 44440376543781973432144465)
  ·
    refine ⟨33330282407836480074108349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44440376543781973432144465 33330282407836480074108349)
    ·
      refine ⟨12498855902938680027790631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33330282407836480074108349 12498855902938680027790631)
      ·
        refine ⟨18748283854408020041685947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12498855902938680027790631 18748283854408020041685947)
        ·
          refine ⟨28122425781612030062528921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18748283854408020041685947 28122425781612030062528921)
          ·
            refine ⟨21091819336209022546896691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28122425781612030062528921 21091819336209022546896691)
            ·
              refine ⟨31637729004313533820345037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21091819336209022546896691 31637729004313533820345037)
              ·
                refine ⟨11864148376617575182629389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31637729004313533820345037 11864148376617575182629389)
                ·
                  refine ⟨4449055641231590693486021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11864148376617575182629389 4449055641231590693486021)
                  ·
                    refine ⟨834197932730923255028629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449055641231590693486021 834197932730923255028629)
                    ·
                      rfl

theorem cell22_2436892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_2436892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436892 prefixEnd_2436892 := by exact prefixLift 2436892
  have htrace : WordTrace (prefixWord ++ tailWord_2436892) baseStart_2436892 baseEnd_2436892 := by
    simpa [prefixWord, tailWord_2436892, baseEnd_2436892] using wordTrace_append hprefix tailTrace_2436892
  have hstable : (prefixWord ++ tailWord_2436892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436892).length < 2 ^ (prefixWord ++ tailWord_2436892).sum := by decide
  have hdescent : baseEnd_2436892 < baseStart_2436892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436924 : List Nat := [2, 2, 2, 2, 1, 1, 4, 4, 4]
def baseStart_2436924 : Nat := 118140960795 + 2436924 * 2 ^ 59
def prefixEnd_2436924 : Nat := 4983230072969 + 3 ^ 40 * 2436924 * 2
def baseEnd_2436924 : Nat := 278069628994961946076177

theorem tailTrace_2436924 : CollatzResearch.WordTrace tailWord_2436924 prefixEnd_2436924 278069628994961946076177 := by
  unfold tailWord_2436924
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440960111724008164726913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59254613482298677552969217 44440960111724008164726913)
  ·
    refine ⟨33330720083793006123545185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44440960111724008164726913 33330720083793006123545185)
    ·
      refine ⟨24998040062844754592658889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33330720083793006123545185 24998040062844754592658889)
      ·
        refine ⟨18748530047133565944494167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24998040062844754592658889 18748530047133565944494167)
        ·
          refine ⟨28122795070700348916741251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18748530047133565944494167 28122795070700348916741251)
          ·
            refine ⟨42184192606050523375111877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28122795070700348916741251 42184192606050523375111877)
            ·
              refine ⟨7909536113634473132833477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42184192606050523375111877 7909536113634473132833477)
              ·
                refine ⟨1483038021306463712406277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7909536113634473132833477 1483038021306463712406277)
                ·
                  refine ⟨278069628994961946076177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483038021306463712406277 278069628994961946076177)
                  ·
                    rfl

theorem cell22_2436924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_2436924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436924 prefixEnd_2436924 := by exact prefixLift 2436924
  have htrace : WordTrace (prefixWord ++ tailWord_2436924) baseStart_2436924 baseEnd_2436924 := by
    simpa [prefixWord, tailWord_2436924, baseEnd_2436924] using wordTrace_append hprefix tailTrace_2436924
  have hstable : (prefixWord ++ tailWord_2436924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436924).length < 2 ^ (prefixWord ++ tailWord_2436924).sum := by decide
  have hdescent : baseEnd_2436924 < baseStart_2436924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2436990 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_2436990 : Nat := 118140960795 + 2436990 * 2 ^ 59
def prefixEnd_2436990 : Nat := 4983230072969 + 3 ^ 40 * 2436990 * 2
def baseEnd_2436990 : Nat := 834231480133683666078329

theorem tailTrace_2436990 : CollatzResearch.WordTrace tailWord_2436990 prefixEnd_2436990 834231480133683666078329 := by
  unfold tailWord_2436990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11110540930151113700169553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59256218294139273067570949 11110540930151113700169553)
  ·
    refine ⟨8332905697613335275127165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11110540930151113700169553 8332905697613335275127165)
    ·
      refine ⟨3124839636605000728172687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8332905697613335275127165 3124839636605000728172687)
      ·
        refine ⟨4687259454907501092259031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124839636605000728172687 4687259454907501092259031)
        ·
          refine ⟨7030889182361251638388547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687259454907501092259031 7030889182361251638388547)
          ·
            refine ⟨10546333773541877457582821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030889182361251638388547 10546333773541877457582821)
            ·
              refine ⟨1977437582539102023296779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10546333773541877457582821 1977437582539102023296779)
              ·
                refine ⟨2966156373808653034945169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977437582539102023296779 2966156373808653034945169)
                ·
                  refine ⟨2224617280356489776208877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966156373808653034945169 2224617280356489776208877)
                  ·
                    refine ⟨834231480133683666078329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2224617280356489776208877 834231480133683666078329)
                    ·
                      rfl

theorem cell22_2436990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_2436990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2436990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2436990 prefixEnd_2436990 := by exact prefixLift 2436990
  have htrace : WordTrace (prefixWord ++ tailWord_2436990) baseStart_2436990 baseEnd_2436990 := by
    simpa [prefixWord, tailWord_2436990, baseEnd_2436990] using wordTrace_append hprefix tailTrace_2436990
  have hstable : (prefixWord ++ tailWord_2436990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2436990).length < 2 ^ (prefixWord ++ tailWord_2436990).sum := by decide
  have hdescent : baseEnd_2436990 < baseStart_2436990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2436990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437031 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 5]
def baseStart_2437031 : Nat := 118140960795 + 2437031 * 2 ^ 59
def prefixEnd_2437031 : Nat := 4983230072969 + 3 ^ 40 * 2437031 * 2
def baseEnd_2437031 : Nat := 278081838423857741934401

theorem tailTrace_2437031 : CollatzResearch.WordTrace tailWord_2437031 prefixEnd_2437031 278081838423857741934401 := by
  unfold tailWord_2437031
  simp only [CollatzResearch.WordTrace]
  refine ⟨88885822834060373603598947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59257215222706915735732631 88885822834060373603598947)
  ·
    refine ⟨133328734251090560405398421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88885822834060373603598947 133328734251090560405398421)
    ·
      refine ⟨6249784418019870019003051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133328734251090560405398421 6249784418019870019003051)
      ·
        refine ⟨9374676627029805028504577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6249784418019870019003051 9374676627029805028504577)
        ·
          refine ⟨7031007470272353771378433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9374676627029805028504577 7031007470272353771378433)
          ·
            refine ⟨5273255602704265328533825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7031007470272353771378433 5273255602704265328533825)
            ·
              refine ⟨3954941702028198996400369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5273255602704265328533825 3954941702028198996400369)
              ·
                refine ⟨2966206276521149247300277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3954941702028198996400369 2966206276521149247300277)
                ·
                  refine ⟨278081838423857741934401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2966206276521149247300277 278081838423857741934401)
                  ·
                    rfl

theorem cell22_2437031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 5].length) (baseStart_2437031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437031 prefixEnd_2437031 := by exact prefixLift 2437031
  have htrace : WordTrace (prefixWord ++ tailWord_2437031) baseStart_2437031 baseEnd_2437031 := by
    simpa [prefixWord, tailWord_2437031, baseEnd_2437031] using wordTrace_append hprefix tailTrace_2437031
  have hstable : (prefixWord ++ tailWord_2437031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437031).length < 2 ^ (prefixWord ++ tailWord_2437031).sum := by decide
  have hdescent : baseEnd_2437031 < baseStart_2437031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437042 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_2437042 : Nat := 118140960795 + 2437042 * 2 ^ 59
def prefixEnd_2437042 : Nat := 4983230072969 + 3 ^ 40 * 2437042 * 2
def baseEnd_2437042 : Nat := 278083093598790954592723

theorem tailTrace_2437042 : CollatzResearch.WordTrace tailWord_2437042 prefixEnd_2437042 278083093598790954592723 := by
  unfold tailWord_2437042
  simp only [CollatzResearch.WordTrace]
  refine ⟨22221556009255130620562345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59257482691347014988166253 22221556009255130620562345)
  ·
    refine ⟨16666167006941347965421759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22221556009255130620562345 16666167006941347965421759)
    ·
      refine ⟨24999250510412021948132639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16666167006941347965421759 24999250510412021948132639)
      ·
        refine ⟨37498875765618032922198959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24999250510412021948132639 37498875765618032922198959)
        ·
          refine ⟨56248313648427049383298439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37498875765618032922198959 56248313648427049383298439)
          ·
            refine ⟨84372470472640574074947659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56248313648427049383298439 84372470472640574074947659)
            ·
              refine ⟨126558705708960861112421489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84372470472640574074947659 126558705708960861112421489)
              ·
                refine ⟨94919029281720645834316117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126558705708960861112421489 94919029281720645834316117)
                ·
                  refine ⟨278083093598790954592723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 94919029281720645834316117 278083093598790954592723)
                  ·
                    rfl

theorem cell22_2437042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_2437042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437042 prefixEnd_2437042 := by exact prefixLift 2437042
  have htrace : WordTrace (prefixWord ++ tailWord_2437042) baseStart_2437042 baseEnd_2437042 := by
    simpa [prefixWord, tailWord_2437042, baseEnd_2437042] using wordTrace_append hprefix tailTrace_2437042
  have hstable : (prefixWord ++ tailWord_2437042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437042).length < 2 ^ (prefixWord ++ tailWord_2437042).sum := by decide
  have hdescent : baseEnd_2437042 < baseStart_2437042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437089 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2437089 : Nat := 118140960795 + 2437089 * 2 ^ 59
def prefixEnd_2437089 : Nat := 4983230072969 + 3 ^ 40 * 2437089 * 2
def baseEnd_2437089 : Nat := 834265369856880407853025

theorem tailTrace_2437089 : CollatzResearch.WordTrace tailWord_2437089 prefixEnd_2437089 834265369856880407853025 := by
  unfold tailWord_2437089
  simp only [CollatzResearch.WordTrace]
  refine ⟨88887938267850249509210321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59258625511900166339473547 88887938267850249509210321)
  ·
    refine ⟨66665953700887687131907741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88887938267850249509210321 66665953700887687131907741)
    ·
      refine ⟨24999732637832882674465403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66665953700887687131907741 24999732637832882674465403)
      ·
        refine ⟨37499598956749324011698105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24999732637832882674465403 37499598956749324011698105)
        ·
          refine ⟨28124699217561993008773579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37499598956749324011698105 28124699217561993008773579)
          ·
            refine ⟨42187048826342989513160369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28124699217561993008773579 42187048826342989513160369)
            ·
              refine ⟨31640286619757242134870277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42187048826342989513160369 31640286619757242134870277)
              ·
                refine ⟨5932553741204482900288177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31640286619757242134870277 5932553741204482900288177)
                ·
                  refine ⟨4449415305903362175216133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5932553741204482900288177 4449415305903362175216133)
                  ·
                    refine ⟨834265369856880407853025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449415305903362175216133 834265369856880407853025)
                    ·
                      rfl

theorem cell22_2437089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2437089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437089 prefixEnd_2437089 := by exact prefixLift 2437089
  have htrace : WordTrace (prefixWord ++ tailWord_2437089) baseStart_2437089 baseEnd_2437089 := by
    simpa [prefixWord, tailWord_2437089, baseEnd_2437089] using wordTrace_append hprefix tailTrace_2437089
  have hstable : (prefixWord ++ tailWord_2437089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437089).length < 2 ^ (prefixWord ++ tailWord_2437089).sum := by decide
  have hdescent : baseEnd_2437089 < baseStart_2437089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437091 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 4, 3]
def baseStart_2437091 : Nat := 118140960795 + 2437091 * 2 ^ 59
def prefixEnd_2437091 : Nat := 4983230072969 + 3 ^ 40 * 2437091 * 2
def baseEnd_2437091 : Nat := 834266054497753069303019

theorem tailTrace_2437091 : CollatzResearch.WordTrace tailWord_2437091 prefixEnd_2437091 834266054497753069303019 := by
  unfold tailWord_2437091
  simp only [CollatzResearch.WordTrace]
  refine ⟨88888011213843003850783127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59258674142562002567188751 88888011213843003850783127)
  ·
    refine ⟨133332016820764505776174691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88888011213843003850783127 133332016820764505776174691)
    ·
      refine ⟨199998025231146758664262037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133332016820764505776174691 199998025231146758664262037)
      ·
        refine ⟨9374907432710004312387283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 199998025231146758664262037 9374907432710004312387283)
        ·
          refine ⟨14062361149065006468580925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9374907432710004312387283 14062361149065006468580925)
          ·
            refine ⟨5273385430899377425717847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14062361149065006468580925 5273385430899377425717847)
            ·
              refine ⟨7910078146349066138576771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273385430899377425717847 7910078146349066138576771)
              ·
                refine ⟨11865117219523599207865157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910078146349066138576771 11865117219523599207865157)
                ·
                  refine ⟨2224709478660674851474717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11865117219523599207865157 2224709478660674851474717)
                  ·
                    refine ⟨834266054497753069303019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2224709478660674851474717 834266054497753069303019)
                    ·
                      rfl

theorem cell22_2437091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 3].length) (baseStart_2437091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437091 prefixEnd_2437091 := by exact prefixLift 2437091
  have htrace : WordTrace (prefixWord ++ tailWord_2437091) baseStart_2437091 baseEnd_2437091 := by
    simpa [prefixWord, tailWord_2437091, baseEnd_2437091] using wordTrace_append hprefix tailTrace_2437091
  have hstable : (prefixWord ++ tailWord_2437091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437091).length < 2 ^ (prefixWord ++ tailWord_2437091).sum := by decide
  have hdescent : baseEnd_2437091 < baseStart_2437091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437140 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2437140 : Nat := 118140960795 + 2437140 * 2 ^ 59
def prefixEnd_2437140 : Nat := 4983230072969 + 3 ^ 40 * 2437140 * 2
def baseEnd_2437140 : Nat := 834282828199133274827869

theorem tailTrace_2437140 : CollatzResearch.WordTrace tailWord_2437140 prefixEnd_2437140 834282828199133274827869 := by
  unfold tailWord_2437140
  simp only [CollatzResearch.WordTrace]
  refine ⟨44444899195332742609658437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59259865593776990146211249 44444899195332742609658437)
  ·
    refine ⟨8333418599124889239310957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44444899195332742609658437 8333418599124889239310957)
    ·
      refine ⟨3125031974671833464741609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8333418599124889239310957 3125031974671833464741609)
      ·
        refine ⟨2343773981003875098556207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3125031974671833464741609 2343773981003875098556207)
        ·
          refine ⟨3515660971505812647834311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343773981003875098556207 3515660971505812647834311)
          ·
            refine ⟨5273491457258718971751467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3515660971505812647834311 5273491457258718971751467)
            ·
              refine ⟨7910237185888078457627201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273491457258718971751467 7910237185888078457627201)
              ·
                refine ⟨5932677889416058843220401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7910237185888078457627201 5932677889416058843220401)
                ·
                  refine ⟨4449508417062044132415301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5932677889416058843220401 4449508417062044132415301)
                  ·
                    refine ⟨834282828199133274827869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449508417062044132415301 834282828199133274827869)
                    ·
                      rfl

theorem cell22_2437140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2437140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437140 prefixEnd_2437140 := by exact prefixLift 2437140
  have htrace : WordTrace (prefixWord ++ tailWord_2437140) baseStart_2437140 baseEnd_2437140 := by
    simpa [prefixWord, tailWord_2437140, baseEnd_2437140] using wordTrace_append hprefix tailTrace_2437140
  have hstable : (prefixWord ++ tailWord_2437140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437140).length < 2 ^ (prefixWord ++ tailWord_2437140).sum := by decide
  have hdescent : baseEnd_2437140 < baseStart_2437140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437159 : List Nat := [1, 1, 7, 1, 3, 1, 2, 1, 2, 3]
def baseStart_2437159 : Nat := 118140960795 + 2437159 * 2 ^ 59
def prefixEnd_2437159 : Nat := 4983230072969 + 3 ^ 40 * 2437159 * 2
def baseEnd_2437159 : Nat := 834289332287423558602811

theorem tailTrace_2437159 : CollatzResearch.WordTrace tailWord_2437159 prefixEnd_2437159 834289332287423558602811 := by
  unfold tailWord_2437159
  simp only [CollatzResearch.WordTrace]
  refine ⟨88890491377596651464258531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59260327585064434309505687 88890491377596651464258531)
  ·
    refine ⟨133335737066394977196387797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88890491377596651464258531 133335737066394977196387797)
    ·
      refine ⟨3125056337493632278040339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 133335737066394977196387797 3125056337493632278040339)
      ·
        refine ⟨4687584506240448417060509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125056337493632278040339 4687584506240448417060509)
        ·
          refine ⟨1757844189840168156397691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4687584506240448417060509 1757844189840168156397691)
          ·
            refine ⟨2636766284760252234596537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1757844189840168156397691 2636766284760252234596537)
            ·
              refine ⟨1977574713570189175947403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2636766284760252234596537 1977574713570189175947403)
              ·
                refine ⟨2966362070355283763921105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977574713570189175947403 2966362070355283763921105)
                ·
                  refine ⟨2224771552766462822940829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2966362070355283763921105 2224771552766462822940829)
                  ·
                    refine ⟨834289332287423558602811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2224771552766462822940829 834289332287423558602811)
                    ·
                      rfl

theorem cell22_2437159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_2437159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437159 prefixEnd_2437159 := by exact prefixLift 2437159
  have htrace : WordTrace (prefixWord ++ tailWord_2437159) baseStart_2437159 baseEnd_2437159 := by
    simpa [prefixWord, tailWord_2437159, baseEnd_2437159] using wordTrace_append hprefix tailTrace_2437159
  have hstable : (prefixWord ++ tailWord_2437159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437159).length < 2 ^ (prefixWord ++ tailWord_2437159).sum := by decide
  have hdescent : baseEnd_2437159 < baseStart_2437159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437179 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 3, 4]
def baseStart_2437179 : Nat := 118140960795 + 2437179 * 2 ^ 59
def prefixEnd_2437179 : Nat := 4983230072969 + 3 ^ 40 * 2437179 * 2
def baseEnd_2437179 : Nat := 834296178696150173102749

theorem tailTrace_2437179 : CollatzResearch.WordTrace tailWord_2437179 prefixEnd_2437179 834296178696150173102749 := by
  unfold tailWord_2437179
  simp only [CollatzResearch.WordTrace]
  refine ⟨88891220837524194879986591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59260813891682796586657727 88891220837524194879986591)
  ·
    refine ⟨133336831256286292319979887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88891220837524194879986591 133336831256286292319979887)
    ·
      refine ⟨200005246884429438479969831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133336831256286292319979887 200005246884429438479969831)
      ·
        refine ⟨300007870326644157719954747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200005246884429438479969831 300007870326644157719954747)
        ·
          refine ⟨450011805489966236579932121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300007870326644157719954747 450011805489966236579932121)
          ·
            refine ⟨337508854117474677434949091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450011805489966236579932121 337508854117474677434949091)
            ·
              refine ⟨506263281176212016152423637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337508854117474677434949091 506263281176212016152423637)
              ·
                refine ⟨11865545652567469128572429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 506263281176212016152423637 11865545652567469128572429)
                ·
                  refine ⟨4449579619712800923214661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11865545652567469128572429 4449579619712800923214661)
                  ·
                    refine ⟨834296178696150173102749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449579619712800923214661 834296178696150173102749)
                    ·
                      rfl

theorem cell22_2437179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_2437179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437179 prefixEnd_2437179 := by exact prefixLift 2437179
  have htrace : WordTrace (prefixWord ++ tailWord_2437179) baseStart_2437179 baseEnd_2437179 := by
    simpa [prefixWord, tailWord_2437179, baseEnd_2437179] using wordTrace_append hprefix tailTrace_2437179
  have hstable : (prefixWord ++ tailWord_2437179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437179).length < 2 ^ (prefixWord ++ tailWord_2437179).sum := by decide
  have hdescent : baseEnd_2437179 < baseStart_2437179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437196 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_2437196 : Nat := 118140960795 + 2437196 * 2 ^ 59
def prefixEnd_2437196 : Nat := 4983230072969 + 3 ^ 40 * 2437196 * 2
def baseEnd_2437196 : Nat := 834301998143567795427697

theorem tailTrace_2437196 : CollatzResearch.WordTrace tailWord_2437196 prefixEnd_2437196 834301998143567795427697 := by
  unfold tailWord_2437196
  simp only [CollatzResearch.WordTrace]
  refine ⟨44445920439231303391677721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59261227252308404522236961 44445920439231303391677721)
  ·
    refine ⟨33334440329423477543758291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44445920439231303391677721 33334440329423477543758291)
    ·
      refine ⟨50001660494135216315637437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33334440329423477543758291 50001660494135216315637437)
      ·
        refine ⟨18750622685300706118364039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50001660494135216315637437 18750622685300706118364039)
        ·
          refine ⟨28125934027951059177546059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18750622685300706118364039 28125934027951059177546059)
          ·
            refine ⟨42188901041926588766319089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28125934027951059177546059 42188901041926588766319089)
            ·
              refine ⟨31641675781444941574739317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42188901041926588766319089 31641675781444941574739317)
              ·
                refine ⟨2966407104510463272631811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31641675781444941574739317 2966407104510463272631811)
                ·
                  refine ⟨4449610656765694908947717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966407104510463272631811 4449610656765694908947717)
                  ·
                    refine ⟨834301998143567795427697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449610656765694908947717 834301998143567795427697)
                    ·
                      rfl

theorem cell22_2437196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_2437196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437196 prefixEnd_2437196 := by exact prefixLift 2437196
  have htrace : WordTrace (prefixWord ++ tailWord_2437196) baseStart_2437196 baseEnd_2437196 := by
    simpa [prefixWord, tailWord_2437196, baseEnd_2437196] using wordTrace_append hprefix tailTrace_2437196
  have hstable : (prefixWord ++ tailWord_2437196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437196).length < 2 ^ (prefixWord ++ tailWord_2437196).sum := by decide
  have hdescent : baseEnd_2437196 < baseStart_2437196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437209 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_2437209 : Nat := 118140960795 + 2437209 * 2 ^ 59
def prefixEnd_2437209 : Nat := 4983230072969 + 3 ^ 40 * 2437209 * 2
def baseEnd_2437209 : Nat := 834306448309240094852657

theorem tailTrace_2437209 : CollatzResearch.WordTrace tailWord_2437209 prefixEnd_2437209 834306448309240094852657 := by
  unfold tailWord_2437209
  simp only [CollatzResearch.WordTrace]
  refine ⟨88892315027415510003578681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59261543351610340002385787 88892315027415510003578681)
  ·
    refine ⟨66669236270561632502684011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88892315027415510003578681 66669236270561632502684011)
    ·
      refine ⟨100003854405842448754026017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66669236270561632502684011 100003854405842448754026017)
      ·
        refine ⟨75002890804381836565519513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100003854405842448754026017 75002890804381836565519513)
        ·
          refine ⟨56252168103286377424139635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75002890804381836565519513 56252168103286377424139635)
          ·
            refine ⟨84378252154929566136209453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56252168103286377424139635 84378252154929566136209453)
            ·
              refine ⟨31641844558098587301078545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84378252154929566136209453 31641844558098587301078545)
              ·
                refine ⟨23731383418573940475808909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31641844558098587301078545 23731383418573940475808909)
                ·
                  refine ⟨8899268781965227678428341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23731383418573940475808909 8899268781965227678428341)
                  ·
                    refine ⟨834306448309240094852657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8899268781965227678428341 834306448309240094852657)
                    ·
                      rfl

theorem cell22_2437209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_2437209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437209 prefixEnd_2437209 := by exact prefixLift 2437209
  have htrace : WordTrace (prefixWord ++ tailWord_2437209) baseStart_2437209 baseEnd_2437209 := by
    simpa [prefixWord, tailWord_2437209, baseEnd_2437209] using wordTrace_append hprefix tailTrace_2437209
  have hstable : (prefixWord ++ tailWord_2437209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437209).length < 2 ^ (prefixWord ++ tailWord_2437209).sum := by decide
  have hdescent : baseEnd_2437209 < baseStart_2437209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437213 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2437213 : Nat := 118140960795 + 2437213 * 2 ^ 59
def prefixEnd_2437213 : Nat := 4983230072969 + 3 ^ 40 * 2437213 * 2
def baseEnd_2437213 : Nat := 834307817590985417752645

theorem tailTrace_2437213 : CollatzResearch.WordTrace tailWord_2437213 prefixEnd_2437213 834307817590985417752645 := by
  unfold tailWord_2437213
  simp only [CollatzResearch.WordTrace]
  refine ⟨88892460919401018686724293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59261640612934012457816195 88892460919401018686724293)
  ·
    refine ⟨16667336422387691003760805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88892460919401018686724293 16667336422387691003760805)
    ·
      refine ⟨3125125579197692063205151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16667336422387691003760805 3125125579197692063205151)
      ·
        refine ⟨4687688368796538094807727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125125579197692063205151 4687688368796538094807727)
        ·
          refine ⟨7031532553194807142211591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687688368796538094807727 7031532553194807142211591)
          ·
            refine ⟨10547298829792210713317387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7031532553194807142211591 10547298829792210713317387)
            ·
              refine ⟨15820948244688316069976081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10547298829792210713317387 15820948244688316069976081)
              ·
                refine ⟨11865711183516237052482061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15820948244688316069976081 11865711183516237052482061)
                ·
                  refine ⟨4449641693818588894680773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11865711183516237052482061 4449641693818588894680773)
                  ·
                    refine ⟨834307817590985417752645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449641693818588894680773 834307817590985417752645)
                    ·
                      rfl

theorem cell22_2437213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2437213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437213 prefixEnd_2437213 := by exact prefixLift 2437213
  have htrace : WordTrace (prefixWord ++ tailWord_2437213) baseStart_2437213 baseEnd_2437213 := by
    simpa [prefixWord, tailWord_2437213, baseEnd_2437213] using wordTrace_append hprefix tailTrace_2437213
  have hstable : (prefixWord ++ tailWord_2437213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437213).length < 2 ^ (prefixWord ++ tailWord_2437213).sum := by decide
  have hdescent : baseEnd_2437213 < baseStart_2437213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437241 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_2437241 : Nat := 118140960795 + 2437241 * 2 ^ 59
def prefixEnd_2437241 : Nat := 4983230072969 + 3 ^ 40 * 2437241 * 2
def baseEnd_2437241 : Nat := 834317402563202678052559

theorem tailTrace_2437241 : CollatzResearch.WordTrace tailWord_2437241 prefixEnd_2437241 834317402563202678052559 := by
  unfold tailWord_2437241
  simp only [CollatzResearch.WordTrace]
  refine ⟨88893482163299579468743577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59262321442199719645829051 88893482163299579468743577)
  ·
    refine ⟨66670111622474684601557683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88893482163299579468743577 66670111622474684601557683)
    ·
      refine ⟨100005167433712026902336525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66670111622474684601557683 100005167433712026902336525)
      ·
        refine ⟨37501937787642010088376197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100005167433712026902336525 37501937787642010088376197)
        ·
          refine ⟨7031613335182876891570537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37501937787642010088376197 7031613335182876891570537)
          ·
            refine ⟨5273710001387157668677903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7031613335182876891570537 5273710001387157668677903)
            ·
              refine ⟨7910565002080736503016855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273710001387157668677903 7910565002080736503016855)
              ·
                refine ⟨11865847503121104754525283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910565002080736503016855 11865847503121104754525283)
                ·
                  refine ⟨17798771254681657131787925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11865847503121104754525283 17798771254681657131787925)
                  ·
                    refine ⟨834317402563202678052559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17798771254681657131787925 834317402563202678052559)
                    ·
                      rfl

theorem cell22_2437241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_2437241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437241 prefixEnd_2437241 := by exact prefixLift 2437241
  have htrace : WordTrace (prefixWord ++ tailWord_2437241) baseStart_2437241 baseEnd_2437241 := by
    simpa [prefixWord, tailWord_2437241, baseEnd_2437241] using wordTrace_append hprefix tailTrace_2437241
  have hstable : (prefixWord ++ tailWord_2437241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437241).length < 2 ^ (prefixWord ++ tailWord_2437241).sum := by decide
  have hdescent : baseEnd_2437241 < baseStart_2437241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437256 : List Nat := [2, 1, 3, 4, 1, 2, 9]
def baseStart_2437256 : Nat := 118140960795 + 2437256 * 2 ^ 59
def prefixEnd_2437256 : Nat := 4983230072969 + 3 ^ 40 * 2437256 * 2
def baseEnd_2437256 : Nat := 30900834717398060701019

theorem tailTrace_2437256 : CollatzResearch.WordTrace tailWord_2437256 prefixEnd_2437256 30900834717398060701019 := by
  unfold tailWord_2437256
  simp only [CollatzResearch.WordTrace]
  refine ⟨44447014629122618515269811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59262686172163491353693081 44447014629122618515269811)
  ·
    refine ⟨66670521943683927772904717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44447014629122618515269811 66670521943683927772904717)
    ·
      refine ⟨25001445728881472914839269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66670521943683927772904717 25001445728881472914839269)
      ·
        refine ⟨4687771074165276171532363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25001445728881472914839269 4687771074165276171532363)
        ·
          refine ⟨7031656611247914257298545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687771074165276171532363 7031656611247914257298545)
          ·
            refine ⟨5273742458435935692973909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7031656611247914257298545 5273742458435935692973909)
            ·
              refine ⟨30900834717398060701019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5273742458435935692973909 30900834717398060701019)
              ·
                rfl

theorem cell22_2437256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 9].length) (baseStart_2437256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437256 prefixEnd_2437256 := by exact prefixLift 2437256
  have htrace : WordTrace (prefixWord ++ tailWord_2437256) baseStart_2437256 baseEnd_2437256 := by
    simpa [prefixWord, tailWord_2437256, baseEnd_2437256] using wordTrace_append hprefix tailTrace_2437256
  have hstable : (prefixWord ++ tailWord_2437256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437256).length < 2 ^ (prefixWord ++ tailWord_2437256).sum := by decide
  have hdescent : baseEnd_2437256 < baseStart_2437256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437322 : List Nat := [3, 1, 2, 1, 3, 1, 5, 2, 1, 3]
def baseStart_2437322 : Nat := 118140960795 + 2437322 * 2 ^ 59
def prefixEnd_2437322 : Nat := 4983230072969 + 3 ^ 40 * 2437322 * 2
def baseEnd_2437322 : Nat := 834345130518545466777311

theorem tailTrace_2437322 : CollatzResearch.WordTrace tailWord_2437322 prefixEnd_2437322 834345130518545466777311 := by
  unfold tailWord_2437322
  simp only [CollatzResearch.WordTrace]
  refine ⟨22224109119001532575610555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59264290984004086868294813 22224109119001532575610555)
  ·
    refine ⟨33336163678502298863415833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22224109119001532575610555 33336163678502298863415833)
    ·
      refine ⟨25002122758876724147561875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33336163678502298863415833 25002122758876724147561875)
      ·
        refine ⟨37503184138315086221342813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25002122758876724147561875 37503184138315086221342813)
        ·
          refine ⟨14063694051868157333003555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37503184138315086221342813 14063694051868157333003555)
          ·
            refine ⟨21095541077802235999505333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14063694051868157333003555 21095541077802235999505333)
            ·
              refine ⟨1977706976043959624953625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21095541077802235999505333 1977706976043959624953625)
              ·
                refine ⟨1483280232032969718715219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1977706976043959624953625 1483280232032969718715219)
                ·
                  refine ⟨2224920348049454578072829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483280232032969718715219 2224920348049454578072829)
                  ·
                    refine ⟨834345130518545466777311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2224920348049454578072829 834345130518545466777311)
                    ·
                      rfl

theorem cell22_2437322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_2437322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437322 prefixEnd_2437322 := by exact prefixLift 2437322
  have htrace : WordTrace (prefixWord ++ tailWord_2437322) baseStart_2437322 baseEnd_2437322 := by
    simpa [prefixWord, tailWord_2437322, baseEnd_2437322] using wordTrace_append hprefix tailTrace_2437322
  have hstable : (prefixWord ++ tailWord_2437322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437322).length < 2 ^ (prefixWord ++ tailWord_2437322).sum := by decide
  have hdescent : baseEnd_2437322 < baseStart_2437322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437361 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_2437361 : Nat := 118140960795 + 2437361 * 2 ^ 59
def prefixEnd_2437361 : Nat := 4983230072969 + 3 ^ 40 * 2437361 * 2
def baseEnd_2437361 : Nat := 834358481015562365052191

theorem tailTrace_2437361 : CollatzResearch.WordTrace tailWord_2437361 prefixEnd_2437361 834358481015562365052191 := by
  unfold tailWord_2437361
  simp only [CollatzResearch.WordTrace]
  refine ⟨88897858922864839963111937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59265239281909893308741291 88897858922864839963111937)
  ·
    refine ⟨66673394192148629972333953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88897858922864839963111937 66673394192148629972333953)
    ·
      refine ⟨50005045644111472479250465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66673394192148629972333953 50005045644111472479250465)
      ·
        refine ⟨37503784233083604359437849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50005045644111472479250465 37503784233083604359437849)
        ·
          refine ⟨28127838174812703269578387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37503784233083604359437849 28127838174812703269578387)
          ·
            refine ⟨42191757262219054904367581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28127838174812703269578387 42191757262219054904367581)
            ·
              refine ⟨15821908973332145589137843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42191757262219054904367581 15821908973332145589137843)
              ·
                refine ⟨23732863459998218383706765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15821908973332145589137843 23732863459998218383706765)
                ·
                  refine ⟨8899823797499331893890037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23732863459998218383706765 8899823797499331893890037)
                  ·
                    refine ⟨834358481015562365052191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8899823797499331893890037 834358481015562365052191)
                    ·
                      rfl

theorem cell22_2437361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_2437361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437361 prefixEnd_2437361 := by exact prefixLift 2437361
  have htrace : WordTrace (prefixWord ++ tailWord_2437361) baseStart_2437361 baseEnd_2437361 := by
    simpa [prefixWord, tailWord_2437361, baseEnd_2437361] using wordTrace_append hprefix tailTrace_2437361
  have hstable : (prefixWord ++ tailWord_2437361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437361).length < 2 ^ (prefixWord ++ tailWord_2437361).sum := by decide
  have hdescent : baseEnd_2437361 < baseStart_2437361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437363 : List Nat := [1, 1, 1, 2, 2, 4, 2, 5, 4]
def baseStart_2437363 : Nat := 118140960795 + 2437363 * 2 ^ 59
def prefixEnd_2437363 : Nat := 4983230072969 + 3 ^ 40 * 2437363 * 2
def baseEnd_2437363 : Nat := 278119721885478342167395

theorem tailTrace_2437363 : CollatzResearch.WordTrace tailWord_2437363 prefixEnd_2437363 278119721885478342167395 := by
  unfold tailWord_2437363
  simp only [CollatzResearch.WordTrace]
  refine ⟨88897931868857594304684743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59265287912571729536456495 88897931868857594304684743)
  ·
    refine ⟨133346897803286391457027115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88897931868857594304684743 133346897803286391457027115)
    ·
      refine ⟨200020346704929587185540673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133346897803286391457027115 200020346704929587185540673)
      ·
        refine ⟨150015260028697190389155505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200020346704929587185540673 150015260028697190389155505)
        ·
          refine ⟨112511445021522892791866629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150015260028697190389155505 112511445021522892791866629)
          ·
            refine ⟨21095895941535542398474993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112511445021522892791866629 21095895941535542398474993)
            ·
              refine ⟨15821921956151656798856245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21095895941535542398474993 15821921956151656798856245)
              ·
                refine ⟨1483305183389217824892773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15821921956151656798856245 1483305183389217824892773)
                ·
                  refine ⟨278119721885478342167395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483305183389217824892773 278119721885478342167395)
                  ·
                    rfl

theorem cell22_2437363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 4].length) (baseStart_2437363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437363 prefixEnd_2437363 := by exact prefixLift 2437363
  have htrace : WordTrace (prefixWord ++ tailWord_2437363) baseStart_2437363 baseEnd_2437363 := by
    simpa [prefixWord, tailWord_2437363, baseEnd_2437363] using wordTrace_append hprefix tailTrace_2437363
  have hstable : (prefixWord ++ tailWord_2437363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437363).length < 2 ^ (prefixWord ++ tailWord_2437363).sum := by decide
  have hdescent : baseEnd_2437363 < baseStart_2437363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437410 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_2437410 : Nat := 118140960795 + 2437410 * 2 ^ 59
def prefixEnd_2437410 : Nat := 4983230072969 + 3 ^ 40 * 2437410 * 2
def baseEnd_2437410 : Nat := 834375254716942570577041

theorem tailTrace_2437410 : CollatzResearch.WordTrace tailWord_2437410 prefixEnd_2437410 834375254716942570577041 := by
  unfold tailWord_2437410
  simp only [CollatzResearch.WordTrace]
  refine ⟨22224911524921830332911421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59266430733124880887763789 22224911524921830332911421)
  ·
    refine ⟨8334341821845686374841783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22224911524921830332911421 8334341821845686374841783)
    ·
      refine ⟨12501512732768529562262675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8334341821845686374841783 12501512732768529562262675)
      ·
        refine ⟨18752269099152794343394013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12501512732768529562262675 18752269099152794343394013)
        ·
          refine ⟨7032100912182297878772755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18752269099152794343394013 7032100912182297878772755)
          ·
            refine ⟨10548151368273446818159133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7032100912182297878772755 10548151368273446818159133)
            ·
              refine ⟨3955556763102542556809675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10548151368273446818159133 3955556763102542556809675)
              ·
                refine ⟨5933335144653813835214513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3955556763102542556809675 5933335144653813835214513)
                ·
                  refine ⟨4450001358490360376410885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5933335144653813835214513 4450001358490360376410885)
                  ·
                    refine ⟨834375254716942570577041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450001358490360376410885 834375254716942570577041)
                    ·
                      rfl

theorem cell22_2437410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_2437410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437410 prefixEnd_2437410 := by exact prefixLift 2437410
  have htrace : WordTrace (prefixWord ++ tailWord_2437410) baseStart_2437410 baseEnd_2437410 := by
    simpa [prefixWord, tailWord_2437410, baseEnd_2437410] using wordTrace_append hprefix tailTrace_2437410
  have hstable : (prefixWord ++ tailWord_2437410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437410).length < 2 ^ (prefixWord ++ tailWord_2437410).sum := by decide
  have hdescent : baseEnd_2437410 < baseStart_2437410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437451 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 1, 7]
def baseStart_2437451 : Nat := 118140960795 + 2437451 * 2 ^ 59
def prefixEnd_2437451 : Nat := 4983230072969 + 3 ^ 40 * 2437451 * 2
def baseEnd_2437451 : Nat := 834389289854832130301915

theorem tailTrace_2437451 : CollatzResearch.WordTrace tailWord_2437451 prefixEnd_2437451 834389289854832130301915 := by
  unfold tailWord_2437451
  simp only [CollatzResearch.WordTrace]
  refine ⟨88901141492538785333888207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59267427661692523555925471 88901141492538785333888207)
  ·
    refine ⟨133351712238808178000832311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88901141492538785333888207 133351712238808178000832311)
    ·
      refine ⟨200027568358212267001248467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133351712238808178000832311 200027568358212267001248467)
      ·
        refine ⟨300041352537318400501872701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200027568358212267001248467 300041352537318400501872701)
        ·
          refine ⟨112515507201494400188202263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300041352537318400501872701 112515507201494400188202263)
          ·
            refine ⟨168773260802241600282303395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112515507201494400188202263 168773260802241600282303395)
            ·
              refine ⟨253159891203362400423455093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168773260802241600282303395 253159891203362400423455093)
              ·
                refine ⟨23733739800315225039698915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253159891203362400423455093 23733739800315225039698915)
                ·
                  refine ⟨35600609700472837559548373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23733739800315225039698915 35600609700472837559548373)
                  ·
                    refine ⟨834389289854832130301915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35600609700472837559548373 834389289854832130301915)
                    ·
                      rfl

theorem cell22_2437451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_2437451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437451 prefixEnd_2437451 := by exact prefixLift 2437451
  have htrace : WordTrace (prefixWord ++ tailWord_2437451) baseStart_2437451 baseEnd_2437451 := by
    simpa [prefixWord, tailWord_2437451, baseEnd_2437451] using wordTrace_append hprefix tailTrace_2437451
  have hstable : (prefixWord ++ tailWord_2437451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437451).length < 2 ^ (prefixWord ++ tailWord_2437451).sum := by decide
  have hdescent : baseEnd_2437451 < baseStart_2437451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437474 : List Nat := [3, 3, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2437474 : Nat := 118140960795 + 2437474 * 2 ^ 59
def prefixEnd_2437474 : Nat := 4983230072969 + 3 ^ 40 * 2437474 * 2
def baseEnd_2437474 : Nat := 834397163224867736976845

theorem tailTrace_2437474 : CollatzResearch.WordTrace tailWord_2437474 prefixEnd_2437474 834397163224867736976845 := by
  unfold tailWord_2437474
  simp only [CollatzResearch.WordTrace]
  refine ⟨22225495092863865065493869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59267986914303640174650317 22225495092863865065493869)
  ·
    refine ⟨8334560659823949399560201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22225495092863865065493869 8334560659823949399560201)
    ·
      refine ⟨6250920494867962049670151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8334560659823949399560201 6250920494867962049670151)
      ·
        refine ⟨9376380742301943074505227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6250920494867962049670151 9376380742301943074505227)
        ·
          refine ⟨14064571113452914611757841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376380742301943074505227 14064571113452914611757841)
          ·
            refine ⟨10548428335089685958818381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14064571113452914611757841 10548428335089685958818381)
            ·
              refine ⟨3955660625658632234556893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10548428335089685958818381 3955660625658632234556893)
              ·
                refine ⟨1483372734621987087958835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3955660625658632234556893 1483372734621987087958835)
                ·
                  refine ⟨2225059101932980631938253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483372734621987087958835 2225059101932980631938253)
                  ·
                    refine ⟨834397163224867736976845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225059101932980631938253 834397163224867736976845)
                    ·
                      rfl

theorem cell22_2437474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2437474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437474 prefixEnd_2437474 := by exact prefixLift 2437474
  have htrace : WordTrace (prefixWord ++ tailWord_2437474) baseStart_2437474 baseEnd_2437474 := by
    simpa [prefixWord, tailWord_2437474, baseEnd_2437474] using wordTrace_append hprefix tailTrace_2437474
  have hstable : (prefixWord ++ tailWord_2437474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437474).length < 2 ^ (prefixWord ++ tailWord_2437474).sum := by decide
  have hdescent : baseEnd_2437474 < baseStart_2437474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437530 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_2437530 : Nat := 118140960795 + 2437530 * 2 ^ 59
def prefixEnd_2437530 : Nat := 4983230072969 + 3 ^ 40 * 2437530 * 2
def baseEnd_2437530 : Nat := 834416333169302257576673

theorem tailTrace_2437530 : CollatzResearch.WordTrace tailWord_2437530 prefixEnd_2437530 834416333169302257576673 := by
  unfold tailWord_2437530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22226005714813145456503511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59269348572835054550676029 22226005714813145456503511)
  ·
    refine ⟨33339008572219718184755267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22226005714813145456503511 33339008572219718184755267)
    ·
      refine ⟨50008512858329577277132901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33339008572219718184755267 50008512858329577277132901)
      ·
        refine ⟨9376596160936795739462419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50008512858329577277132901 9376596160936795739462419)
        ·
          refine ⟨14064894241405193609193629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376596160936795739462419 14064894241405193609193629)
          ·
            refine ⟨5274335340526947603447611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14064894241405193609193629 5274335340526947603447611)
            ·
              refine ⟨7911503010790421405171417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274335340526947603447611 7911503010790421405171417)
              ·
                refine ⟨5933627258092816053878563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7911503010790421405171417 5933627258092816053878563)
                ·
                  refine ⟨8900440887139224080817845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5933627258092816053878563 8900440887139224080817845)
                  ·
                    refine ⟨834416333169302257576673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8900440887139224080817845 834416333169302257576673)
                    ·
                      rfl

theorem cell22_2437530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_2437530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437530 prefixEnd_2437530 := by exact prefixLift 2437530
  have htrace : WordTrace (prefixWord ++ tailWord_2437530) baseStart_2437530 baseEnd_2437530 := by
    simpa [prefixWord, tailWord_2437530, baseEnd_2437530] using wordTrace_append hprefix tailTrace_2437530
  have hstable : (prefixWord ++ tailWord_2437530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437530).length < 2 ^ (prefixWord ++ tailWord_2437530).sum := by decide
  have hdescent : baseEnd_2437530 < baseStart_2437530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437543 : List Nat := [1, 1, 6, 1, 1, 12]
def baseStart_2437543 : Nat := 118140960795 + 2437543 * 2 ^ 59
def prefixEnd_2437543 : Nat := 4983230072969 + 3 ^ 40 * 2437543 * 2
def baseEnd_2437543 : Nat := 10301491152283636506193

theorem tailTrace_2437543 : CollatzResearch.WordTrace tailWord_2437543 prefixEnd_2437543 10301491152283636506193 := by
  unfold tailWord_2437543
  simp only [CollatzResearch.WordTrace]
  refine ⟨88904497008205485046237283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59269664672136990030824855 88904497008205485046237283)
  ·
    refine ⟨133356745512308227569355925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88904497008205485046237283 133356745512308227569355925)
    ·
      refine ⟨6251097445889448167313559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133356745512308227569355925 6251097445889448167313559)
      ·
        refine ⟨9376646168834172250970339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6251097445889448167313559 9376646168834172250970339)
        ·
          refine ⟨14064969253251258376455509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376646168834172250970339 14064969253251258376455509)
          ·
            refine ⟨10301491152283636506193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14064969253251258376455509 10301491152283636506193)
            ·
              rfl

theorem cell22_2437543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 12].length) (baseStart_2437543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437543 prefixEnd_2437543 := by exact prefixLift 2437543
  have htrace : WordTrace (prefixWord ++ tailWord_2437543) baseStart_2437543 baseEnd_2437543 := by
    simpa [prefixWord, tailWord_2437543, baseEnd_2437543] using wordTrace_append hprefix tailTrace_2437543
  have hstable : (prefixWord ++ tailWord_2437543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437543).length < 2 ^ (prefixWord ++ tailWord_2437543).sum := by decide
  have hdescent : baseEnd_2437543 < baseStart_2437543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437549 : List Nat := [1, 5, 2, 2, 2, 1, 1, 4, 4]
def baseStart_2437549 : Nat := 118140960795 + 2437549 * 2 ^ 59
def prefixEnd_2437549 : Nat := 4983230072969 + 3 ^ 40 * 2437549 * 2
def baseEnd_2437549 : Nat := 278140945752530847117205

theorem tailTrace_2437549 : CollatzResearch.WordTrace tailWord_2437549 prefixEnd_2437549 278140945752530847117205 := by
  unfold tailWord_2437549
  simp only [CollatzResearch.WordTrace]
  refine ⟨88904715846183748070955701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59269810564122498713970467 88904715846183748070955701)
  ·
    refine ⟨8334817110579726381652097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88904715846183748070955701 8334817110579726381652097)
    ·
      refine ⟨6251112832934794786239073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8334817110579726381652097 6251112832934794786239073)
      ·
        refine ⟨4688334624701096089679305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6251112832934794786239073 4688334624701096089679305)
        ·
          refine ⟨3516250968525822067259479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4688334624701096089679305 3516250968525822067259479)
          ·
            refine ⟨5274376452788733100889219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516250968525822067259479 5274376452788733100889219)
            ·
              refine ⟨7911564679183099651333829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274376452788733100889219 7911564679183099651333829)
              ·
                refine ⟨1483418377346831184625093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7911564679183099651333829 1483418377346831184625093)
                ·
                  refine ⟨278140945752530847117205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483418377346831184625093 278140945752530847117205)
                  ·
                    rfl

theorem cell22_2437549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_2437549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437549 prefixEnd_2437549 := by exact prefixLift 2437549
  have htrace : WordTrace (prefixWord ++ tailWord_2437549) baseStart_2437549 baseEnd_2437549 := by
    simpa [prefixWord, tailWord_2437549, baseEnd_2437549] using wordTrace_append hprefix tailTrace_2437549
  have hstable : (prefixWord ++ tailWord_2437549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437549).length < 2 ^ (prefixWord ++ tailWord_2437549).sum := by decide
  have hdescent : baseEnd_2437549 < baseStart_2437549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437575 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 5, 3]
def baseStart_2437575 : Nat := 118140960795 + 2437575 * 2 ^ 59
def prefixEnd_2437575 : Nat := 4983230072969 + 3 ^ 40 * 2437575 * 2
def baseEnd_2437575 : Nat := 834431737588937140201535

theorem tailTrace_2437575 : CollatzResearch.WordTrace tailWord_2437575 prefixEnd_2437575 834431737588937140201535 := by
  unfold tailWord_2437575
  simp only [CollatzResearch.WordTrace]
  refine ⟨88905664144089554511402179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59270442762726369674268119 88905664144089554511402179)
  ·
    refine ⟨133358496216134331767103269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88905664144089554511402179 133358496216134331767103269)
    ·
      refine ⟨25004718040525187206331863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133358496216134331767103269 25004718040525187206331863)
      ·
        refine ⟨37507077060787780809497795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25004718040525187206331863 37507077060787780809497795)
        ·
          refine ⟨56260615591181671214246693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37507077060787780809497795 56260615591181671214246693)
          ·
            refine ⟨10548865423346563352671255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56260615591181671214246693 10548865423346563352671255)
            ·
              refine ⟨15823298135019845029006883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10548865423346563352671255 15823298135019845029006883)
              ·
                refine ⟨23734947202529767543510325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15823298135019845029006883 23734947202529767543510325)
                ·
                  refine ⟨2225151300237165707204093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23734947202529767543510325 2225151300237165707204093)
                  ·
                    refine ⟨834431737588937140201535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225151300237165707204093 834431737588937140201535)
                    ·
                      rfl

theorem cell22_2437575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_2437575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437575 prefixEnd_2437575 := by exact prefixLift 2437575
  have htrace : WordTrace (prefixWord ++ tailWord_2437575) baseStart_2437575 baseEnd_2437575 := by
    simpa [prefixWord, tailWord_2437575, baseEnd_2437575] using wordTrace_append hprefix tailTrace_2437575
  have hstable : (prefixWord ++ tailWord_2437575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437575).length < 2 ^ (prefixWord ++ tailWord_2437575).sum := by decide
  have hdescent : baseEnd_2437575 < baseStart_2437575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437667 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 6]
def baseStart_2437667 : Nat := 118140960795 + 2437667 * 2 ^ 59
def prefixEnd_2437667 : Nat := 4983230072969 + 3 ^ 40 * 2437667 * 2
def baseEnd_2437667 : Nat := 278154410356359855633751

theorem tailTrace_2437667 : CollatzResearch.WordTrace tailWord_2437667 prefixEnd_2437667 278154410356359855633751 := by
  unfold tailWord_2437667
  simp only [CollatzResearch.WordTrace]
  refine ⟨88909019659756254223751255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59272679773170836149167503 88909019659756254223751255)
  ·
    refine ⟨133363529489634381335626883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88909019659756254223751255 133363529489634381335626883)
    ·
      refine ⟨200045294234451572003440325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133363529489634381335626883 200045294234451572003440325)
      ·
        refine ⟨37508492668959669750645061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200045294234451572003440325 37508492668959669750645061)
        ·
          refine ⟨7032842375429938078245949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37508492668959669750645061 7032842375429938078245949)
          ·
            refine ⟨2637315890786226779342231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7032842375429938078245949 2637315890786226779342231)
            ·
              refine ⟨3955973836179340169013347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637315890786226779342231 3955973836179340169013347)
              ·
                refine ⟨5933960754269010253520021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3955973836179340169013347 5933960754269010253520021)
                ·
                  refine ⟨278154410356359855633751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5933960754269010253520021 278154410356359855633751)
                  ·
                    rfl

theorem cell22_2437667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 6].length) (baseStart_2437667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437667 prefixEnd_2437667 := by exact prefixLift 2437667
  have htrace : WordTrace (prefixWord ++ tailWord_2437667) baseStart_2437667 baseEnd_2437667 := by
    simpa [prefixWord, tailWord_2437667, baseEnd_2437667] using wordTrace_append hprefix tailTrace_2437667
  have hstable : (prefixWord ++ tailWord_2437667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437667).length < 2 ^ (prefixWord ++ tailWord_2437667).sum := by decide
  have hdescent : baseEnd_2437667 < baseStart_2437667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437686 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_2437686 : Nat := 118140960795 + 2437686 * 2 ^ 59
def prefixEnd_2437686 : Nat := 4983230072969 + 3 ^ 40 * 2437686 * 2
def baseEnd_2437686 : Nat := 834469735157369850676195

theorem tailTrace_2437686 : CollatzResearch.WordTrace tailWord_2437686 prefixEnd_2437686 834469735157369850676195 := by
  unfold tailWord_2437686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556857040417963779293307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59273141764458280312461941 5556857040417963779293307)
  ·
    refine ⟨8335285560626945668939961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5556857040417963779293307 8335285560626945668939961)
    ·
      refine ⟨6251464170470209251704971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8335285560626945668939961 6251464170470209251704971)
      ·
        refine ⟨9377196255705313877557457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6251464170470209251704971 9377196255705313877557457)
        ·
          refine ⟨7032897191778985408168093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9377196255705313877557457 7032897191778985408168093)
          ·
            refine ⟨2637336446917119528063035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7032897191778985408168093 2637336446917119528063035)
            ·
              refine ⟨3956004670375679292094553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637336446917119528063035 3956004670375679292094553)
              ·
                refine ⟨2967003502781759469070915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3956004670375679292094553 2967003502781759469070915)
                ·
                  refine ⟨4450505254172639203606373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967003502781759469070915 4450505254172639203606373)
                  ·
                    refine ⟨834469735157369850676195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450505254172639203606373 834469735157369850676195)
                    ·
                      rfl

theorem cell22_2437686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_2437686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437686 prefixEnd_2437686 := by exact prefixLift 2437686
  have htrace : WordTrace (prefixWord ++ tailWord_2437686) baseStart_2437686 baseEnd_2437686 := by
    simpa [prefixWord, tailWord_2437686, baseEnd_2437686] using wordTrace_append hprefix tailTrace_2437686
  have hstable : (prefixWord ++ tailWord_2437686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437686).length < 2 ^ (prefixWord ++ tailWord_2437686).sum := by decide
  have hdescent : baseEnd_2437686 < baseStart_2437686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437697 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_2437697 : Nat := 118140960795 + 2437697 * 2 ^ 59
def prefixEnd_2437697 : Nat := 4983230072969 + 3 ^ 40 * 2437697 * 2
def baseEnd_2437697 : Nat := 834473500682169488651161

theorem tailTrace_2437697 : CollatzResearch.WordTrace tailWord_2437697 prefixEnd_2437697 834473500682169488651161 := by
  unfold tailWord_2437697
  simp only [CollatzResearch.WordTrace]
  refine ⟨88910113849647569347343345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59273409233098379564895563 88910113849647569347343345)
  ·
    refine ⟨66682585387235677010507509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88910113849647569347343345 66682585387235677010507509)
    ·
      refine ⟨6251492380053344719735079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66682585387235677010507509 6251492380053344719735079)
      ·
        refine ⟨9377238570080017079602619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6251492380053344719735079 9377238570080017079602619)
        ·
          refine ⟨14065857855120025619403929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9377238570080017079602619 14065857855120025619403929)
          ·
            refine ⟨10549393391340019214552947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14065857855120025619403929 10549393391340019214552947)
            ·
              refine ⟨15824090087010028821829421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10549393391340019214552947 15824090087010028821829421)
              ·
                refine ⟨5934033782628760808186033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15824090087010028821829421 5934033782628760808186033)
                ·
                  refine ⟨4450525336971570606139525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5934033782628760808186033 4450525336971570606139525)
                  ·
                    refine ⟨834473500682169488651161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450525336971570606139525 834473500682169488651161)
                    ·
                      rfl

theorem cell22_2437697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_2437697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437697 prefixEnd_2437697 := by exact prefixLift 2437697
  have htrace : WordTrace (prefixWord ++ tailWord_2437697) baseStart_2437697 baseEnd_2437697 := by
    simpa [prefixWord, tailWord_2437697, baseEnd_2437697] using wordTrace_append hprefix tailTrace_2437697
  have hstable : (prefixWord ++ tailWord_2437697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437697).length < 2 ^ (prefixWord ++ tailWord_2437697).sum := by decide
  have hdescent : baseEnd_2437697 < baseStart_2437697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437744 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 3, 3]
def baseStart_2437744 : Nat := 118140960795 + 2437744 * 2 ^ 59
def prefixEnd_2437744 : Nat := 4983230072969 + 3 ^ 40 * 2437744 * 2
def baseEnd_2437744 : Nat := 834489589742677032726017

theorem tailTrace_2437744 : CollatzResearch.WordTrace tailWord_2437744 prefixEnd_2437744 834489589742677032726017 := by
  unfold tailWord_2437744
  simp only [CollatzResearch.WordTrace]
  refine ⟨44455914040238648187152143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59274552053651530916202857 44455914040238648187152143)
  ·
    refine ⟨66683871060357972280728215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44455914040238648187152143 66683871060357972280728215)
    ·
      refine ⟨100025806590536958421092323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66683871060357972280728215 100025806590536958421092323)
      ·
        refine ⟨150038709885805437631638485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100025806590536958421092323 150038709885805437631638485)
        ·
          refine ⟨3516532262948564944491527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 150038709885805437631638485 3516532262948564944491527)
          ·
            refine ⟨5274798394422847416737291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516532262948564944491527 5274798394422847416737291)
            ·
              refine ⟨7912197591634271125105937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274798394422847416737291 7912197591634271125105937)
              ·
                refine ⟨5934148193725703343829453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7912197591634271125105937 5934148193725703343829453)
                ·
                  refine ⟨2225305572647138753936045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5934148193725703343829453 2225305572647138753936045)
                  ·
                    refine ⟨834489589742677032726017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225305572647138753936045 834489589742677032726017)
                    ·
                      rfl

theorem cell22_2437744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 3].length) (baseStart_2437744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437744 prefixEnd_2437744 := by exact prefixLift 2437744
  have htrace : WordTrace (prefixWord ++ tailWord_2437744) baseStart_2437744 baseEnd_2437744 := by
    simpa [prefixWord, tailWord_2437744, baseEnd_2437744] using wordTrace_append hprefix tailTrace_2437744
  have hstable : (prefixWord ++ tailWord_2437744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437744).length < 2 ^ (prefixWord ++ tailWord_2437744).sum := by decide
  have hdescent : baseEnd_2437744 < baseStart_2437744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437761 : List Nat := [1, 2, 4, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2437761 : Nat := 118140960795 + 2437761 * 2 ^ 59
def prefixEnd_2437761 : Nat := 4983230072969 + 3 ^ 40 * 2437761 * 2
def baseEnd_2437761 : Nat := 834495409190094655050965

theorem tailTrace_2437761 : CollatzResearch.WordTrace tailWord_2437761 prefixEnd_2437761 834495409190094655050965 := by
  unfold tailWord_2437761
  simp only [CollatzResearch.WordTrace]
  refine ⟨88912448121415708277673137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59274965414277138851782091 88912448121415708277673137)
  ·
    refine ⟨66684336091061781208254853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88912448121415708277673137 66684336091061781208254853)
    ·
      refine ⟨12503313017074083976547785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66684336091061781208254853 12503313017074083976547785)
      ·
        refine ⟨9377484762805562982410839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12503313017074083976547785 9377484762805562982410839)
        ·
          refine ⟨14066227144208344473616259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9377484762805562982410839 14066227144208344473616259)
          ·
            refine ⟨21099340716312516710424389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14066227144208344473616259 21099340716312516710424389)
            ·
              refine ⟨3956126384308596883204573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21099340716312516710424389 3956126384308596883204573)
              ·
                refine ⟨1483547394115723831201715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3956126384308596883204573 1483547394115723831201715)
                ·
                  refine ⟨2225321091173585746802573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483547394115723831201715 2225321091173585746802573)
                  ·
                    refine ⟨834495409190094655050965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225321091173585746802573 834495409190094655050965)
                    ·
                      rfl

theorem cell22_2437761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2437761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437761 prefixEnd_2437761 := by exact prefixLift 2437761
  have htrace : WordTrace (prefixWord ++ tailWord_2437761) baseStart_2437761 baseEnd_2437761 := by
    simpa [prefixWord, tailWord_2437761, baseEnd_2437761] using wordTrace_append hprefix tailTrace_2437761
  have hstable : (prefixWord ++ tailWord_2437761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437761).length < 2 ^ (prefixWord ++ tailWord_2437761).sum := by decide
  have hdescent : baseEnd_2437761 < baseStart_2437761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437832 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_2437832 : Nat := 118140960795 + 2437832 * 2 ^ 59
def prefixEnd_2437832 : Nat := 4983230072969 + 3 ^ 40 * 2437832 * 2
def baseEnd_2437832 : Nat := 834519713941074136525747

theorem tailTrace_2437832 : CollatzResearch.WordTrace tailWord_2437832 prefixEnd_2437832 834519713941074136525747 := by
  unfold tailWord_2437832
  simp only [CollatzResearch.WordTrace]
  refine ⟨44457518852079243701753875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59276691802772324935671833 44457518852079243701753875)
  ·
    refine ⟨66686278278118865552630813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44457518852079243701753875 66686278278118865552630813)
    ·
      refine ⟨25007354354294574582236555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66686278278118865552630813 25007354354294574582236555)
      ·
        refine ⟨37511031531441861873354833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25007354354294574582236555 37511031531441861873354833)
        ·
          refine ⟨28133273648581396405016125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37511031531441861873354833 28133273648581396405016125)
          ·
            refine ⟨10549977618218023651881047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28133273648581396405016125 10549977618218023651881047)
            ·
              refine ⟨15824966427327035477821571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10549977618218023651881047 15824966427327035477821571)
              ·
                refine ⟨23737449640990553216732357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15824966427327035477821571 23737449640990553216732357)
                ·
                  refine ⟨4450771807685728728137317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23737449640990553216732357 4450771807685728728137317)
                  ·
                    refine ⟨834519713941074136525747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450771807685728728137317 834519713941074136525747)
                    ·
                      rfl

theorem cell22_2437832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_2437832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437832 prefixEnd_2437832 := by exact prefixLift 2437832
  have htrace : WordTrace (prefixWord ++ tailWord_2437832) baseStart_2437832 baseEnd_2437832 := by
    simpa [prefixWord, tailWord_2437832, baseEnd_2437832] using wordTrace_append hprefix tailTrace_2437832
  have hstable : (prefixWord ++ tailWord_2437832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437832).length < 2 ^ (prefixWord ++ tailWord_2437832).sum := by decide
  have hdescent : baseEnd_2437832 < baseStart_2437832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437834 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_2437834 : Nat := 118140960795 + 2437834 * 2 ^ 59
def prefixEnd_2437834 : Nat := 4983230072969 + 3 ^ 40 * 2437834 * 2
def baseEnd_2437834 : Nat := 834520398581946797975741

theorem tailTrace_2437834 : CollatzResearch.WordTrace tailWord_2437834 prefixEnd_2437834 834520398581946797975741 := by
  unfold tailWord_2437834
  simp only [CollatzResearch.WordTrace]
  refine ⟨22228777662537810436270139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59276740433434161163387037 22228777662537810436270139)
  ·
    refine ⟨33343166493806715654405209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22228777662537810436270139 33343166493806715654405209)
    ·
      refine ⟨25007374870355036740803907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33343166493806715654405209 25007374870355036740803907)
      ·
        refine ⟨37511062305532555111205861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25007374870355036740803907 37511062305532555111205861)
        ·
          refine ⟨7033324182287354083351099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37511062305532555111205861 7033324182287354083351099)
          ·
            refine ⟨10549986273431031125026649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7033324182287354083351099 10549986273431031125026649)
            ·
              refine ⟨7912489705073273343769987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10549986273431031125026649 7912489705073273343769987)
              ·
                refine ⟨11868734557609910015654981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7912489705073273343769987 11868734557609910015654981)
                ·
                  refine ⟨2225387729551858127935309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11868734557609910015654981 2225387729551858127935309)
                  ·
                    refine ⟨834520398581946797975741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225387729551858127935309 834520398581946797975741)
                    ·
                      rfl

theorem cell22_2437834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_2437834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437834 prefixEnd_2437834 := by exact prefixLift 2437834
  have htrace : WordTrace (prefixWord ++ tailWord_2437834) baseStart_2437834 baseEnd_2437834 := by
    simpa [prefixWord, tailWord_2437834, baseEnd_2437834] using wordTrace_append hprefix tailTrace_2437834
  have hstable : (prefixWord ++ tailWord_2437834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437834).length < 2 ^ (prefixWord ++ tailWord_2437834).sum := by decide
  have hdescent : baseEnd_2437834 < baseStart_2437834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437847 : List Nat := [1, 1, 3, 2, 1, 5, 2, 7]
def baseStart_2437847 : Nat := 118140960795 + 2437847 * 2 ^ 59
def prefixEnd_2437847 : Nat := 4983230072969 + 3 ^ 40 * 2437847 * 2
def baseEnd_2437847 : Nat := 92724983194179899711189

theorem tailTrace_2437847 : CollatzResearch.WordTrace tailWord_2437847 prefixEnd_2437847 92724983194179899711189 := by
  unfold tailWord_2437847
  simp only [CollatzResearch.WordTrace]
  refine ⟨88915584799104144965303795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59277056532736096643535863 88915584799104144965303795)
  ·
    refine ⟨133373377198656217447955693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88915584799104144965303795 133373377198656217447955693)
    ·
      refine ⟨50015016449496081542983385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133373377198656217447955693 50015016449496081542983385)
      ·
        refine ⟨37511262337122061157237539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50015016449496081542983385 37511262337122061157237539)
        ·
          refine ⟨56266893505683091735856309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37511262337122061157237539 56266893505683091735856309)
          ·
            refine ⟨5275021266157789850236529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56266893505683091735856309 5275021266157789850236529)
            ·
              refine ⟨3956265949618342387677397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5275021266157789850236529 3956265949618342387677397)
              ·
                refine ⟨92724983194179899711189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3956265949618342387677397 92724983194179899711189)
                ·
                  rfl

theorem cell22_2437847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 7].length) (baseStart_2437847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437847 prefixEnd_2437847 := by exact prefixLift 2437847
  have htrace : WordTrace (prefixWord ++ tailWord_2437847) baseStart_2437847 baseEnd_2437847 := by
    simpa [prefixWord, tailWord_2437847, baseEnd_2437847] using wordTrace_append hprefix tailTrace_2437847
  have hstable : (prefixWord ++ tailWord_2437847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437847).length < 2 ^ (prefixWord ++ tailWord_2437847).sum := by decide
  have hdescent : baseEnd_2437847 < baseStart_2437847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437907 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 2, 5]
def baseStart_2437907 : Nat := 118140960795 + 2437907 * 2 ^ 59
def prefixEnd_2437907 : Nat := 4983230072969 + 3 ^ 40 * 2437907 * 2
def baseEnd_2437907 : Nat := 834545387973798940900517

theorem tailTrace_2437907 : CollatzResearch.WordTrace tailWord_2437907 prefixEnd_2437907 834545387973798940900517 := by
  unfold tailWord_2437907
  simp only [CollatzResearch.WordTrace]
  refine ⟨88917773178886775212487975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59278515452591183474991983 88917773178886775212487975)
  ·
    refine ⟨133376659768330162818731963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88917773178886775212487975 133376659768330162818731963)
    ·
      refine ⟨200064989652495244228097945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133376659768330162818731963 200064989652495244228097945)
      ·
        refine ⟨150048742239371433171073459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200064989652495244228097945 150048742239371433171073459)
        ·
          refine ⟨225073113359057149756610189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150048742239371433171073459 225073113359057149756610189)
          ·
            refine ⟨84402417509646431158728821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225073113359057149756610189 84402417509646431158728821)
            ·
              refine ⟨7912726641529352921130827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84402417509646431158728821 7912726641529352921130827)
              ·
                refine ⟨11869089962294029381696241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7912726641529352921130827 11869089962294029381696241)
                ·
                  refine ⟨8901817471720522036272181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11869089962294029381696241 8901817471720522036272181)
                  ·
                    refine ⟨834545387973798940900517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8901817471720522036272181 834545387973798940900517)
                    ·
                      rfl

theorem cell22_2437907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_2437907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437907 prefixEnd_2437907 := by exact prefixLift 2437907
  have htrace : WordTrace (prefixWord ++ tailWord_2437907) baseStart_2437907 baseEnd_2437907 := by
    simpa [prefixWord, tailWord_2437907, baseEnd_2437907] using wordTrace_append hprefix tailTrace_2437907
  have hstable : (prefixWord ++ tailWord_2437907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437907).length < 2 ^ (prefixWord ++ tailWord_2437907).sum := by decide
  have hdescent : baseEnd_2437907 < baseStart_2437907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437937 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 8]
def baseStart_2437937 : Nat := 118140960795 + 2437937 * 2 ^ 59
def prefixEnd_2437937 : Nat := 4983230072969 + 3 ^ 40 * 2437937 * 2
def baseEnd_2437937 : Nat := 278185219195629620883475

theorem tailTrace_2437937 : CollatzResearch.WordTrace tailWord_2437937 prefixEnd_2437937 278185219195629620883475 := by
  unfold tailWord_2437937
  simp only [CollatzResearch.WordTrace]
  refine ⟨88918867368778090336080065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59279244912518726890720043 88918867368778090336080065)
  ·
    refine ⟨66689150526583567752060049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88918867368778090336080065 66689150526583567752060049)
    ·
      refine ⟨50016862894937675814045037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66689150526583567752060049 50016862894937675814045037)
      ·
        refine ⟨18756323585601628430266889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50016862894937675814045037 18756323585601628430266889)
        ·
          refine ⟨14067242689201221322700167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18756323585601628430266889 14067242689201221322700167)
          ·
            refine ⟨21100864033801831984050251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14067242689201221322700167 21100864033801831984050251)
            ·
              refine ⟨31651296050702747976075377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21100864033801831984050251 31651296050702747976075377)
              ·
                refine ⟨23738472038027060982056533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31651296050702747976075377 23738472038027060982056533)
                ·
                  refine ⟨278185219195629620883475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23738472038027060982056533 278185219195629620883475)
                  ·
                    rfl

theorem cell22_2437937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_2437937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437937 prefixEnd_2437937 := by exact prefixLift 2437937
  have htrace : WordTrace (prefixWord ++ tailWord_2437937) baseStart_2437937 baseEnd_2437937 := by
    simpa [prefixWord, tailWord_2437937, baseEnd_2437937] using wordTrace_append hprefix tailTrace_2437937
  have hstable : (prefixWord ++ tailWord_2437937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437937).length < 2 ^ (prefixWord ++ tailWord_2437937).sum := by decide
  have hdescent : baseEnd_2437937 < baseStart_2437937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437952 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_2437952 : Nat := 118140960795 + 2437952 * 2 ^ 59
def prefixEnd_2437952 : Nat := 4983230072969 + 3 ^ 40 * 2437952 * 2
def baseEnd_2437952 : Nat := 834560792393433823525379

theorem tailTrace_2437952 : CollatzResearch.WordTrace tailWord_2437952 prefixEnd_2437952 834560792393433823525379 := by
  unfold tailWord_2437952
  simp only [CollatzResearch.WordTrace]
  refine ⟨44459707231861873948938055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59279609642482498598584073 44459707231861873948938055)
  ·
    refine ⟨66689560847792810923407083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44459707231861873948938055 66689560847792810923407083)
    ·
      refine ⟨100034341271689216385110625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66689560847792810923407083 100034341271689216385110625)
      ·
        refine ⟨75025755953766912288832969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100034341271689216385110625 75025755953766912288832969)
        ·
          refine ⟨56269316965325184216624727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75025755953766912288832969 56269316965325184216624727)
          ·
            refine ⟨84403975447987776324937091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56269316965325184216624727 84403975447987776324937091)
            ·
              refine ⟨126605963171981664487405637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84403975447987776324937091 126605963171981664487405637)
              ·
                refine ⟨23738618094746562091388557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126605963171981664487405637 23738618094746562091388557)
                ·
                  refine ⟨8901981785529960784270709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23738618094746562091388557 8901981785529960784270709)
                  ·
                    refine ⟨834560792393433823525379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8901981785529960784270709 834560792393433823525379)
                    ·
                      rfl

theorem cell22_2437952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_2437952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437952 prefixEnd_2437952 := by exact prefixLift 2437952
  have htrace : WordTrace (prefixWord ++ tailWord_2437952) baseStart_2437952 baseEnd_2437952 := by
    simpa [prefixWord, tailWord_2437952, baseEnd_2437952] using wordTrace_append hprefix tailTrace_2437952
  have hstable : (prefixWord ++ tailWord_2437952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437952).length < 2 ^ (prefixWord ++ tailWord_2437952).sum := by decide
  have hdescent : baseEnd_2437952 < baseStart_2437952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437984 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_2437984 : Nat := 118140960795 + 2437984 * 2 ^ 59
def prefixEnd_2437984 : Nat := 4983230072969 + 3 ^ 40 * 2437984 * 2
def baseEnd_2437984 : Nat := 834571746647396406725281

theorem tailTrace_2437984 : CollatzResearch.WordTrace tailWord_2437984 prefixEnd_2437984 834571746647396406725281 := by
  unfold tailWord_2437984
  simp only [CollatzResearch.WordTrace]
  refine ⟨44460290799803908681520503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59280387733071878242027337 44460290799803908681520503)
  ·
    refine ⟨66690436199705863022280755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44460290799803908681520503 66690436199705863022280755)
    ·
      refine ⟨100035654299558794533421133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66690436199705863022280755 100035654299558794533421133)
      ·
        refine ⟨37513370362334547950032925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100035654299558794533421133 37513370362334547950032925)
        ·
          refine ⟨14067513885875455481262347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37513370362334547950032925 14067513885875455481262347)
          ·
            refine ⟨21101270828813183221893521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14067513885875455481262347 21101270828813183221893521)
            ·
              refine ⟨15825953121609887416420141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21101270828813183221893521 15825953121609887416420141)
              ·
                refine ⟨5934732420603707781157553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15825953121609887416420141 5934732420603707781157553)
                ·
                  refine ⟨4451049315452780835868165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5934732420603707781157553 4451049315452780835868165)
                  ·
                    refine ⟨834571746647396406725281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4451049315452780835868165 834571746647396406725281)
                    ·
                      rfl

theorem cell22_2437984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_2437984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437984 prefixEnd_2437984 := by exact prefixLift 2437984
  have htrace : WordTrace (prefixWord ++ tailWord_2437984) baseStart_2437984 baseEnd_2437984 := by
    simpa [prefixWord, tailWord_2437984, baseEnd_2437984] using wordTrace_append hprefix tailTrace_2437984
  have hstable : (prefixWord ++ tailWord_2437984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437984).length < 2 ^ (prefixWord ++ tailWord_2437984).sum := by decide
  have hdescent : baseEnd_2437984 < baseStart_2437984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2437988 : List Nat := [2, 3, 1, 1, 4, 3, 1, 3, 4]
def baseStart_2437988 : Nat := 118140960795 + 2437988 * 2 ^ 59
def prefixEnd_2437988 : Nat := 4983230072969 + 3 ^ 40 * 2437988 * 2
def baseEnd_2437988 : Nat := 278191038643047243208423

theorem tailTrace_2437988 : CollatzResearch.WordTrace tailWord_2437988 prefixEnd_2437988 278191038643047243208423 := by
  unfold tailWord_2437988
  simp only [CollatzResearch.WordTrace]
  refine ⟨44460363745796663023093309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59280484994395550697457745 44460363745796663023093309)
  ·
    refine ⟨16672636404673748633659991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44460363745796663023093309 16672636404673748633659991)
    ·
      refine ⟨25008954607010622950489987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16672636404673748633659991 25008954607010622950489987)
      ·
        refine ⟨37513431910515934425734981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25008954607010622950489987 37513431910515934425734981)
        ·
          refine ⟨7033768483221737704825309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37513431910515934425734981 7033768483221737704825309)
          ·
            refine ⟨2637663181208151639309491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7033768483221737704825309 2637663181208151639309491)
            ·
              refine ⟨3956494771812227458964237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637663181208151639309491 3956494771812227458964237)
              ·
                refine ⟨1483685539429585297111589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3956494771812227458964237 1483685539429585297111589)
                ·
                  refine ⟨278191038643047243208423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483685539429585297111589 278191038643047243208423)
                  ·
                    rfl

theorem cell22_2437988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_2437988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2437988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2437988 prefixEnd_2437988 := by exact prefixLift 2437988
  have htrace : WordTrace (prefixWord ++ tailWord_2437988) baseStart_2437988 baseEnd_2437988 := by
    simpa [prefixWord, tailWord_2437988, baseEnd_2437988] using wordTrace_append hprefix tailTrace_2437988
  have hstable : (prefixWord ++ tailWord_2437988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2437988).length < 2 ^ (prefixWord ++ tailWord_2437988).sum := by decide
  have hdescent : baseEnd_2437988 < baseStart_2437988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2437988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438065 : List Nat := [1, 2, 2, 4, 3, 1, 1, 4, 1, 3]
def baseStart_2438065 : Nat := 118140960795 + 2438065 * 2 ^ 59
def prefixEnd_2438065 : Nat := 4983230072969 + 3 ^ 40 * 2438065 * 2
def baseEnd_2438065 : Nat := 834599474602739195450033

theorem tailTrace_2438065 : CollatzResearch.WordTrace tailWord_2438065 prefixEnd_2438065 834599474602739195450033 := by
  unfold tailWord_2438065
  simp only [CollatzResearch.WordTrace]
  refine ⟨88923535912314368196739649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59282357274876245464493099 88923535912314368196739649)
  ·
    refine ⟨66692651934235776147554737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88923535912314368196739649 66692651934235776147554737)
    ·
      refine ⟨50019488950676832110666053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66692651934235776147554737 50019488950676832110666053)
      ·
        refine ⟨9378654178251906020749885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50019488950676832110666053 9378654178251906020749885)
        ·
          refine ⟨3516995316844464757781207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9378654178251906020749885 3516995316844464757781207)
          ·
            refine ⟨5275492975266697136671811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516995316844464757781207 5275492975266697136671811)
            ·
              refine ⟨7913239462900045705007717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275492975266697136671811 7913239462900045705007717)
              ·
                refine ⟨1483732399293758569688947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7913239462900045705007717 1483732399293758569688947)
                ·
                  refine ⟨2225598598940637854533421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1483732399293758569688947 2225598598940637854533421)
                  ·
                    refine ⟨834599474602739195450033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225598598940637854533421 834599474602739195450033)
                    ·
                      rfl

theorem cell22_2438065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_2438065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438065 prefixEnd_2438065 := by exact prefixLift 2438065
  have htrace : WordTrace (prefixWord ++ tailWord_2438065) baseStart_2438065 baseEnd_2438065 := by
    simpa [prefixWord, tailWord_2438065, baseEnd_2438065] using wordTrace_append hprefix tailTrace_2438065
  have hstable : (prefixWord ++ tailWord_2438065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438065).length < 2 ^ (prefixWord ++ tailWord_2438065).sum := by decide
  have hdescent : baseEnd_2438065 < baseStart_2438065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438074 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_2438074 : Nat := 118140960795 + 2438074 * 2 ^ 59
def prefixEnd_2438074 : Nat := 4983230072969 + 3 ^ 40 * 2438074 * 2
def baseEnd_2438074 : Nat := 834602555486666171975005

theorem tailTrace_2438074 : CollatzResearch.WordTrace tailWord_2438074 prefixEnd_2438074 834602555486666171975005 := by
  unfold tailWord_2438074
  simp only [CollatzResearch.WordTrace]
  refine ⟨22230966042320440683454319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59282576112854508489211517 22230966042320440683454319)
  ·
    refine ⟨33346449063480661025181479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22230966042320440683454319 33346449063480661025181479)
    ·
      refine ⟨50019673595220991537772219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33346449063480661025181479 50019673595220991537772219)
      ·
        refine ⟨75029510392831487306658329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50019673595220991537772219 75029510392831487306658329)
        ·
          refine ⟨56272132794623615479993747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75029510392831487306658329 56272132794623615479993747)
          ·
            refine ⟨84408199191935423219990621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56272132794623615479993747 84408199191935423219990621)
            ·
              refine ⟨31653074696975783707496483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84408199191935423219990621 31653074696975783707496483)
              ·
                refine ⟨47479612045463675561244725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31653074696975783707496483 47479612045463675561244725)
                ·
                  refine ⟨4451213629262219583866693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47479612045463675561244725 4451213629262219583866693)
                  ·
                    refine ⟨834602555486666171975005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4451213629262219583866693 834602555486666171975005)
                    ·
                      rfl

theorem cell22_2438074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_2438074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438074 prefixEnd_2438074 := by exact prefixLift 2438074
  have htrace : WordTrace (prefixWord ++ tailWord_2438074) baseStart_2438074 baseEnd_2438074 := by
    simpa [prefixWord, tailWord_2438074, baseEnd_2438074] using wordTrace_append hprefix tailTrace_2438074
  have hstable : (prefixWord ++ tailWord_2438074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438074).length < 2 ^ (prefixWord ++ tailWord_2438074).sum := by decide
  have hdescent : baseEnd_2438074 < baseStart_2438074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438086 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2438086 : Nat := 118140960795 + 2438086 * 2 ^ 59
def prefixEnd_2438086 : Nat := 4983230072969 + 3 ^ 40 * 2438086 * 2
def baseEnd_2438086 : Nat := 834606663331902140674969

theorem tailTrace_2438086 : CollatzResearch.WordTrace tailWord_2438086 prefixEnd_2438086 834606663331902140674969 := by
  unfold tailWord_2438086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778884432663696524476691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59282867896825525855502741 2778884432663696524476691)
  ·
    refine ⟨4168326648995544786715037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2778884432663696524476691 4168326648995544786715037)
    ·
      refine ⟨1563122493373329295018139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4168326648995544786715037 1563122493373329295018139)
      ·
        refine ⟨2344683740059993942527209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563122493373329295018139 2344683740059993942527209)
        ·
          refine ⟨1758512805044995456895407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2344683740059993942527209 1758512805044995456895407)
          ·
            refine ⟨2637769207567493185343111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758512805044995456895407 2637769207567493185343111)
            ·
              refine ⟨3956653811351239778014667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2637769207567493185343111 3956653811351239778014667)
              ·
                refine ⟨5934980717026859667022001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956653811351239778014667 5934980717026859667022001)
                ·
                  refine ⟨4451235537770144750266501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5934980717026859667022001 4451235537770144750266501)
                  ·
                    refine ⟨834606663331902140674969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4451235537770144750266501 834606663331902140674969)
                    ·
                      rfl

theorem cell22_2438086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2438086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438086 prefixEnd_2438086 := by exact prefixLift 2438086
  have htrace : WordTrace (prefixWord ++ tailWord_2438086) baseStart_2438086 baseEnd_2438086 := by
    simpa [prefixWord, tailWord_2438086, baseEnd_2438086] using wordTrace_append hprefix tailTrace_2438086
  have hstable : (prefixWord ++ tailWord_2438086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438086).length < 2 ^ (prefixWord ++ tailWord_2438086).sum := by decide
  have hdescent : baseEnd_2438086 < baseStart_2438086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438149 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_2438149 : Nat := 118140960795 + 2438149 * 2 ^ 59
def prefixEnd_2438149 : Nat := 4983230072969 + 3 ^ 40 * 2438149 * 2
def baseEnd_2438149 : Nat := 834628229519390976349775

theorem tailTrace_2438149 : CollatzResearch.WordTrace tailWord_2438149 prefixEnd_2438149 834628229519390976349775 := by
  unfold tailWord_2438149
  simp only [CollatzResearch.WordTrace]
  refine ⟨88926599644010050542797501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59284399762673367028531667 88926599644010050542797501)
  ·
    refine ⟨33347474866503768953549063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88926599644010050542797501 33347474866503768953549063)
    ·
      refine ⟨50021212299755653430323595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33347474866503768953549063 50021212299755653430323595)
      ·
        refine ⟨75031818449633480145485393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50021212299755653430323595 75031818449633480145485393)
        ·
          refine ⟨56273863837225110109114045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75031818449633480145485393 56273863837225110109114045)
          ·
            refine ⟨21102698938959416290917767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56273863837225110109114045 21102698938959416290917767)
            ·
              refine ⟨31654048408439124436376651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21102698938959416290917767 31654048408439124436376651)
              ·
                refine ⟨47481072612658686654564977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31654048408439124436376651 47481072612658686654564977)
                ·
                  refine ⟨35610804459494014990923733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47481072612658686654564977 35610804459494014990923733)
                  ·
                    refine ⟨834628229519390976349775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35610804459494014990923733 834628229519390976349775)
                    ·
                      rfl

theorem cell22_2438149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_2438149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438149 prefixEnd_2438149 := by exact prefixLift 2438149
  have htrace : WordTrace (prefixWord ++ tailWord_2438149) baseStart_2438149 baseEnd_2438149 := by
    simpa [prefixWord, tailWord_2438149, baseEnd_2438149] using wordTrace_append hprefix tailTrace_2438149
  have hstable : (prefixWord ++ tailWord_2438149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438149).length < 2 ^ (prefixWord ++ tailWord_2438149).sum := by decide
  have hdescent : baseEnd_2438149 < baseStart_2438149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438273 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_2438273 : Nat := 118140960795 + 2438273 * 2 ^ 59
def prefixEnd_2438273 : Nat := 4983230072969 + 3 ^ 40 * 2438273 * 2
def baseEnd_2438273 : Nat := 834670677253495986249395

theorem tailTrace_2438273 : CollatzResearch.WordTrace tailWord_2438273 prefixEnd_2438273 834670677253495986249395 := by
  unfold tailWord_2438273
  simp only [CollatzResearch.WordTrace]
  refine ⟨88931122295560819720311473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59287414863707213146874315 88931122295560819720311473)
  ·
    refine ⟨66698341721670614790233605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88931122295560819720311473 66698341721670614790233605)
    ·
      refine ⟨12505939072813240273168801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66698341721670614790233605 12505939072813240273168801)
      ·
        refine ⟨9379454304609930204876601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12505939072813240273168801 9379454304609930204876601)
        ·
          refine ⟨7034590728457447653657451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9379454304609930204876601 7034590728457447653657451)
          ·
            refine ⟨10551886092686171480486177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7034590728457447653657451 10551886092686171480486177)
            ·
              refine ⟨7913914569514628610364633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10551886092686171480486177 7913914569514628610364633)
              ·
                refine ⟨5935435927135971457773475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7913914569514628610364633 5935435927135971457773475)
                ·
                  refine ⟨8903153890703957186660213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5935435927135971457773475 8903153890703957186660213)
                  ·
                    refine ⟨834670677253495986249395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8903153890703957186660213 834670677253495986249395)
                    ·
                      rfl

theorem cell22_2438273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_2438273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438273 prefixEnd_2438273 := by exact prefixLift 2438273
  have htrace : WordTrace (prefixWord ++ tailWord_2438273) baseStart_2438273 baseEnd_2438273 := by
    simpa [prefixWord, tailWord_2438273, baseEnd_2438273] using wordTrace_append hprefix tailTrace_2438273
  have hstable : (prefixWord ++ tailWord_2438273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438273).length < 2 ^ (prefixWord ++ tailWord_2438273).sum := by decide
  have hdescent : baseEnd_2438273 < baseStart_2438273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438277 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_2438277 : Nat := 118140960795 + 2438277 * 2 ^ 59
def prefixEnd_2438277 : Nat := 4983230072969 + 3 ^ 40 * 2438277 * 2
def baseEnd_2438277 : Nat := 834672046535241309149383

theorem tailTrace_2438277 : CollatzResearch.WordTrace tailWord_2438277 prefixEnd_2438277 834672046535241309149383 := by
  unfold tailWord_2438277
  simp only [CollatzResearch.WordTrace]
  refine ⟨88931268187546328403457085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59287512125030885602304723 88931268187546328403457085)
  ·
    refine ⟨33349225570329873151296407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88931268187546328403457085 33349225570329873151296407)
    ·
      refine ⟨50023838355494809726944611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33349225570329873151296407 50023838355494809726944611)
      ·
        refine ⟨75035757533242214590416917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50023838355494809726944611 75035757533242214590416917)
        ·
          refine ⟨3517301134370728808925793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75035757533242214590416917 3517301134370728808925793)
          ·
            refine ⟨2637975850778046606694345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3517301134370728808925793 2637975850778046606694345)
            ·
              refine ⟨1978481888083534955020759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2637975850778046606694345 1978481888083534955020759)
              ·
                refine ⟨2967722832125302432531139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978481888083534955020759 2967722832125302432531139)
                ·
                  refine ⟨4451584248187953648796709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967722832125302432531139 4451584248187953648796709)
                  ·
                    refine ⟨834672046535241309149383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4451584248187953648796709 834672046535241309149383)
                    ·
                      rfl

theorem cell22_2438277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_2438277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438277 prefixEnd_2438277 := by exact prefixLift 2438277
  have htrace : WordTrace (prefixWord ++ tailWord_2438277) baseStart_2438277 baseEnd_2438277 := by
    simpa [prefixWord, tailWord_2438277, baseEnd_2438277] using wordTrace_append hprefix tailTrace_2438277
  have hstable : (prefixWord ++ tailWord_2438277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438277).length < 2 ^ (prefixWord ++ tailWord_2438277).sum := by decide
  have hdescent : baseEnd_2438277 < baseStart_2438277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438290 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_2438290 : Nat := 118140960795 + 2438290 * 2 ^ 59
def prefixEnd_2438290 : Nat := 4983230072969 + 3 ^ 40 * 2438290 * 2
def baseEnd_2438290 : Nat := 834676496700913608574343

theorem tailTrace_2438290 : CollatzResearch.WordTrace tailWord_2438290 prefixEnd_2438290 834676496700913608574343 := by
  unfold tailWord_2438290
  simp only [CollatzResearch.WordTrace]
  refine ⟨22232935584124807905920081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59287828224332821082453549 22232935584124807905920081)
  ·
    refine ⟨16674701688093605929440061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22232935584124807905920081 16674701688093605929440061)
    ·
      refine ⟨6253013133035102223540023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16674701688093605929440061 6253013133035102223540023)
      ·
        refine ⟨9379519699552653335310035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6253013133035102223540023 9379519699552653335310035)
        ·
          refine ⟨14069279549328980002965053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9379519699552653335310035 14069279549328980002965053)
          ·
            refine ⟨5275979830998367501111895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14069279549328980002965053 5275979830998367501111895)
            ·
              refine ⟨7913969746497551251667843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275979830998367501111895 7913969746497551251667843)
              ·
                refine ⟨11870954619746326877501765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7913969746497551251667843 11870954619746326877501765)
                ·
                  refine ⟨2225803991202436289531581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11870954619746326877501765 2225803991202436289531581)
                  ·
                    refine ⟨834676496700913608574343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225803991202436289531581 834676496700913608574343)
                    ·
                      rfl

theorem cell22_2438290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_2438290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438290 prefixEnd_2438290 := by exact prefixLift 2438290
  have htrace : WordTrace (prefixWord ++ tailWord_2438290) baseStart_2438290 baseEnd_2438290 := by
    simpa [prefixWord, tailWord_2438290, baseEnd_2438290] using wordTrace_append hprefix tailTrace_2438290
  have hstable : (prefixWord ++ tailWord_2438290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438290).length < 2 ^ (prefixWord ++ tailWord_2438290).sum := by decide
  have hdescent : baseEnd_2438290 < baseStart_2438290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438326 : List Nat := [5, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2438326 : Nat := 118140960795 + 2438326 * 2 ^ 59
def prefixEnd_2438326 : Nat := 4983230072969 + 3 ^ 40 * 2438326 * 2
def baseEnd_2438326 : Nat := 278229606745540504891411

theorem tailTrace_2438326 : CollatzResearch.WordTrace tailWord_2438326 prefixEnd_2438326 278229606745540504891411 := by
  unfold tailWord_2438326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5558315960273050610749427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59288703576245873181327221 5558315960273050610749427)
  ·
    refine ⟨8337473940409575916124141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5558315960273050610749427 8337473940409575916124141)
    ·
      refine ⟨3126552727653590968546553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8337473940409575916124141 3126552727653590968546553)
      ·
        refine ⟨2344914545740193226409915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3126552727653590968546553 2344914545740193226409915)
        ·
          refine ⟨3517371818610289839614873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344914545740193226409915 3517371818610289839614873)
          ·
            refine ⟨2638028863957717379711155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3517371818610289839614873 2638028863957717379711155)
            ·
              refine ⟨3957043295936576069566733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638028863957717379711155 3957043295936576069566733)
              ·
                refine ⟨1483891235976216026087525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3957043295936576069566733 1483891235976216026087525)
                ·
                  refine ⟨278229606745540504891411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483891235976216026087525 278229606745540504891411)
                  ·
                    rfl

theorem cell22_2438326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2438326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438326 prefixEnd_2438326 := by exact prefixLift 2438326
  have htrace : WordTrace (prefixWord ++ tailWord_2438326) baseStart_2438326 baseEnd_2438326 := by
    simpa [prefixWord, tailWord_2438326, baseEnd_2438326] using wordTrace_append hprefix tailTrace_2438326
  have hstable : (prefixWord ++ tailWord_2438326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438326).length < 2 ^ (prefixWord ++ tailWord_2438326).sum := by decide
  have hdescent : baseEnd_2438326 < baseStart_2438326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438358 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2438358 : Nat := 118140960795 + 2438358 * 2 ^ 59
def prefixEnd_2438358 : Nat := 4983230072969 + 3 ^ 40 * 2438358 * 2
def baseEnd_2438358 : Nat := 834699774490584097874135

theorem tailTrace_2438358 : CollatzResearch.WordTrace tailWord_2438358 prefixEnd_2438358 834699774490584097874135 := by
  unfold tailWord_2438358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5558388906265804952322233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59289481666835252824770485 5558388906265804952322233)
  ·
    refine ⟨4168791679699353714241675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5558388906265804952322233 4168791679699353714241675)
    ·
      refine ⟨6253187519549030571362513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4168791679699353714241675 6253187519549030571362513)
      ·
        refine ⟨4689890639661772928521885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6253187519549030571362513 4689890639661772928521885)
        ·
          refine ⟨1758708989873164848195707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4689890639661772928521885 1758708989873164848195707)
          ·
            refine ⟨2638063484809747272293561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758708989873164848195707 2638063484809747272293561)
            ·
              refine ⟨1978547613607310454220171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638063484809747272293561 1978547613607310454220171)
              ·
                refine ⟨2967821420410965681330257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978547613607310454220171 2967821420410965681330257)
                ·
                  refine ⟨2225866065308224260997693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2967821420410965681330257 2225866065308224260997693)
                  ·
                    refine ⟨834699774490584097874135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2225866065308224260997693 834699774490584097874135)
                    ·
                      rfl

theorem cell22_2438358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2438358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438358 prefixEnd_2438358 := by exact prefixLift 2438358
  have htrace : WordTrace (prefixWord ++ tailWord_2438358) baseStart_2438358 baseEnd_2438358 := by
    simpa [prefixWord, tailWord_2438358, baseEnd_2438358] using wordTrace_append hprefix tailTrace_2438358
  have hstable : (prefixWord ++ tailWord_2438358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438358).length < 2 ^ (prefixWord ++ tailWord_2438358).sum := by decide
  have hdescent : baseEnd_2438358 < baseStart_2438358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438361 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_2438361 : Nat := 118140960795 + 2438361 * 2 ^ 59
def prefixEnd_2438361 : Nat := 4983230072969 + 3 ^ 40 * 2438361 * 2
def baseEnd_2438361 : Nat := 834700801451893090049125

theorem tailTrace_2438361 : CollatzResearch.WordTrace tailWord_2438361 prefixEnd_2438361 834700801451893090049125 := by
  unfold tailWord_2438361
  simp only [CollatzResearch.WordTrace]
  refine ⟨88934331919242010749514937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59289554612828007166343291 88934331919242010749514937)
  ·
    refine ⟨66700748939431508062136203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88934331919242010749514937 66700748939431508062136203)
    ·
      refine ⟨100051123409147262093204305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66700748939431508062136203 100051123409147262093204305)
      ·
        refine ⟨75038342556860446569903229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100051123409147262093204305 75038342556860446569903229)
        ·
          refine ⟨28139378458822667463713711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75038342556860446569903229 28139378458822667463713711)
          ·
            refine ⟨42209067688234001195570567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28139378458822667463713711 42209067688234001195570567)
            ·
              refine ⟨63313601532351001793355851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42209067688234001195570567 63313601532351001793355851)
              ·
                refine ⟨94970402298526502690033777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63313601532351001793355851 94970402298526502690033777)
                ·
                  refine ⟨71227801723894877017525333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94970402298526502690033777 71227801723894877017525333)
                  ·
                    refine ⟨834700801451893090049125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71227801723894877017525333 834700801451893090049125)
                    ·
                      rfl

theorem cell22_2438361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_2438361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438361 prefixEnd_2438361 := by exact prefixLift 2438361
  have htrace : WordTrace (prefixWord ++ tailWord_2438361) baseStart_2438361 baseEnd_2438361 := by
    simpa [prefixWord, tailWord_2438361, baseEnd_2438361] using wordTrace_append hprefix tailTrace_2438361
  have hstable : (prefixWord ++ tailWord_2438361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438361).length < 2 ^ (prefixWord ++ tailWord_2438361).sum := by decide
  have hdescent : baseEnd_2438361 < baseStart_2438361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438423 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 1, 6]
def baseStart_2438423 : Nat := 118140960795 + 2438423 * 2 ^ 59
def prefixEnd_2438423 : Nat := 4983230072969 + 3 ^ 40 * 2438423 * 2
def baseEnd_2438423 : Nat := 834722025318945594998935

theorem tailTrace_2438423 : CollatzResearch.WordTrace tailWord_2438423 prefixEnd_2438423 834722025318945594998935 := by
  unfold tailWord_2438423
  simp only [CollatzResearch.WordTrace]
  refine ⟨88936593245017395338271923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59291062163344930225514615 88936593245017395338271923)
  ·
    refine ⟨133404889867526093007407885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88936593245017395338271923 133404889867526093007407885)
    ·
      refine ⟨50026833700322284877777957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133404889867526093007407885 50026833700322284877777957)
      ·
        refine ⟨9380031318810428414583367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50026833700322284877777957 9380031318810428414583367)
        ·
          refine ⟨14070046978215642621875051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9380031318810428414583367 14070046978215642621875051)
          ·
            refine ⟨21105070467323463932812577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14070046978215642621875051 21105070467323463932812577)
            ·
              refine ⟨15828802850492597949609433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21105070467323463932812577 15828802850492597949609433)
              ·
                refine ⟨11871602137869448462207075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15828802850492597949609433 11871602137869448462207075)
                ·
                  refine ⟨17807403206804172693310613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11871602137869448462207075 17807403206804172693310613)
                  ·
                    refine ⟨834722025318945594998935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17807403206804172693310613 834722025318945594998935)
                    ·
                      rfl

theorem cell22_2438423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_2438423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438423 prefixEnd_2438423 := by exact prefixLift 2438423
  have htrace : WordTrace (prefixWord ++ tailWord_2438423) baseStart_2438423 baseEnd_2438423 := by
    simpa [prefixWord, tailWord_2438423, baseEnd_2438423] using wordTrace_append hprefix tailTrace_2438423
  have hstable : (prefixWord ++ tailWord_2438423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438423).length < 2 ^ (prefixWord ++ tailWord_2438423).sum := by decide
  have hdescent : baseEnd_2438423 < baseStart_2438423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438440 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2438440 : Nat := 118140960795 + 2438440 * 2 ^ 59
def prefixEnd_2438440 : Nat := 4983230072969 + 3 ^ 40 * 2438440 * 2
def baseEnd_2438440 : Nat := 834727844766363217323883

theorem tailTrace_2438440 : CollatzResearch.WordTrace tailWord_2438440 prefixEnd_2438440 834727844766363217323883 := by
  unfold tailWord_2438440
  simp only [CollatzResearch.WordTrace]
  refine ⟨44468606642977903620820387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59291475523970538161093849 44468606642977903620820387)
  ·
    refine ⟨66702909964466855431230581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44468606642977903620820387 66702909964466855431230581)
    ·
      refine ⟨6253397809168767696677867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66702909964466855431230581 6253397809168767696677867)
      ·
        refine ⟨9380096713753151545016801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6253397809168767696677867 9380096713753151545016801)
        ·
          refine ⟨7035072535314863658762601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9380096713753151545016801 7035072535314863658762601)
          ·
            refine ⟨5276304401486147744071951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7035072535314863658762601 5276304401486147744071951)
            ·
              refine ⟨7914456602229221616107927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276304401486147744071951 7914456602229221616107927)
              ·
                refine ⟨11871684903343832424161891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7914456602229221616107927 11871684903343832424161891)
                ·
                  refine ⟨17807527355015748636242837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11871684903343832424161891 17807527355015748636242837)
                  ·
                    refine ⟨834727844766363217323883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17807527355015748636242837 834727844766363217323883)
                    ·
                      rfl

theorem cell22_2438440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2438440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438440 prefixEnd_2438440 := by exact prefixLift 2438440
  have htrace : WordTrace (prefixWord ++ tailWord_2438440) baseStart_2438440 baseEnd_2438440 := by
    simpa [prefixWord, tailWord_2438440, baseEnd_2438440] using wordTrace_append hprefix tailTrace_2438440
  have hstable : (prefixWord ++ tailWord_2438440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438440).length < 2 ^ (prefixWord ++ tailWord_2438440).sum := by decide
  have hdescent : baseEnd_2438440 < baseStart_2438440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438560 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_2438560 : Nat := 118140960795 + 2438560 * 2 ^ 59
def prefixEnd_2438560 : Nat := 4983230072969 + 3 ^ 40 * 2438560 * 2
def baseEnd_2438560 : Nat := 834768923218722904323515

theorem tailTrace_2438560 : CollatzResearch.WordTrace tailWord_2438560 prefixEnd_2438560 834768923218722904323515 := by
  unfold tailWord_2438560
  simp only [CollatzResearch.WordTrace]
  refine ⟨44470795022760533868004567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59294393363680711824006089 44470795022760533868004567)
  ·
    refine ⟨66706192534140800802006851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44470795022760533868004567 66706192534140800802006851)
    ·
      refine ⟨100059288801211201203010277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66706192534140800802006851 100059288801211201203010277)
      ·
        refine ⟨18761116650227100225564427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100059288801211201203010277 18761116650227100225564427)
        ·
          refine ⟨28141674975340650338346641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18761116650227100225564427 28141674975340650338346641)
          ·
            refine ⟨21106256231505487753759981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28141674975340650338346641 21106256231505487753759981)
            ·
              refine ⟨7914846086814557907659993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21106256231505487753759981 7914846086814557907659993)
              ·
                refine ⟨5936134565110918430744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7914846086814557907659993 5936134565110918430744995)
                ·
                  refine ⟨8904201847666377646117493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5936134565110918430744995 8904201847666377646117493)
                  ·
                    refine ⟨834768923218722904323515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8904201847666377646117493 834768923218722904323515)
                    ·
                      rfl

theorem cell22_2438560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_2438560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438560 prefixEnd_2438560 := by exact prefixLift 2438560
  have htrace : WordTrace (prefixWord ++ tailWord_2438560) baseStart_2438560 baseEnd_2438560 := by
    simpa [prefixWord, tailWord_2438560, baseEnd_2438560] using wordTrace_append hprefix tailTrace_2438560
  have hstable : (prefixWord ++ tailWord_2438560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438560).length < 2 ^ (prefixWord ++ tailWord_2438560).sum := by decide
  have hdescent : baseEnd_2438560 < baseStart_2438560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438635 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 5]
def baseStart_2438635 : Nat := 118140960795 + 2438635 * 2 ^ 59
def prefixEnd_2438635 : Nat := 4983230072969 + 3 ^ 40 * 2438635 * 2
def baseEnd_2438635 : Nat := 278264865750482569566095

theorem tailTrace_2438635 : CollatzResearch.WordTrace tailWord_2438635 prefixEnd_2438635 278264865750482569566095 := by
  unfold tailWord_2438635
  simp only [CollatzResearch.WordTrace]
  refine ⟨88944325520249355544989359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59296217013499570363326239 88944325520249355544989359)
  ·
    refine ⟨133416488280374033317484039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88944325520249355544989359 133416488280374033317484039)
    ·
      refine ⟨200124732420561049976226059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133416488280374033317484039 200124732420561049976226059)
      ·
        refine ⟨300187098630841574964339089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200124732420561049976226059 300187098630841574964339089)
        ·
          refine ⟨225140323973131181223254317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300187098630841574964339089 225140323973131181223254317)
          ·
            refine ⟨84427621489924192958720369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225140323973131181223254317 84427621489924192958720369)
            ·
              refine ⟨63320716117443144719040277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84427621489924192958720369 63320716117443144719040277)
              ·
                refine ⟨2968158568005147408705013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63320716117443144719040277 2968158568005147408705013)
                ·
                  refine ⟨278264865750482569566095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968158568005147408705013 278264865750482569566095)
                  ·
                    rfl

theorem cell22_2438635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 5].length) (baseStart_2438635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438635 prefixEnd_2438635 := by exact prefixLift 2438635
  have htrace : WordTrace (prefixWord ++ tailWord_2438635) baseStart_2438635 baseEnd_2438635 := by
    simpa [prefixWord, tailWord_2438635, baseEnd_2438635] using wordTrace_append hprefix tailTrace_2438635
  have hstable : (prefixWord ++ tailWord_2438635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438635).length < 2 ^ (prefixWord ++ tailWord_2438635).sum := by decide
  have hdescent : baseEnd_2438635 < baseStart_2438635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438639 : List Nat := [1, 1, 2, 1, 4, 1, 4, 4, 1, 3]
def baseStart_2438639 : Nat := 118140960795 + 2438639 * 2 ^ 59
def prefixEnd_2438639 : Nat := 4983230072969 + 3 ^ 40 * 2438639 * 2
def baseEnd_2438639 : Nat := 834795966533193031598273

theorem tailTrace_2438639 : CollatzResearch.WordTrace tailWord_2438639 prefixEnd_2438639 834795966533193031598273 := by
  unfold tailWord_2438639
  simp only [CollatzResearch.WordTrace]
  refine ⟨88944471412234864228134971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59296314274823242818756647 88944471412234864228134971)
  ·
    refine ⟨133416707118352296342202457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88944471412234864228134971 133416707118352296342202457)
    ·
      refine ⟨100062530338764222256651843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133416707118352296342202457 100062530338764222256651843)
      ·
        refine ⟨150093795508146333384977765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100062530338764222256651843 150093795508146333384977765)
        ·
          refine ⟨28142586657777437509683331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150093795508146333384977765 28142586657777437509683331)
          ·
            refine ⟨42213879986666156264524997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28142586657777437509683331 42213879986666156264524997)
            ·
              refine ⟨7915102497499904299598437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42213879986666156264524997 7915102497499904299598437)
              ·
                refine ⟨1484081718281232056174707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7915102497499904299598437 1484081718281232056174707)
                ·
                  refine ⟨2226122577421848084262061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484081718281232056174707 2226122577421848084262061)
                  ·
                    refine ⟨834795966533193031598273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226122577421848084262061 834795966533193031598273)
                    ·
                      rfl

theorem cell22_2438639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 3].length) (baseStart_2438639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438639 prefixEnd_2438639 := by exact prefixLift 2438639
  have htrace : WordTrace (prefixWord ++ tailWord_2438639) baseStart_2438639 baseEnd_2438639 := by
    simpa [prefixWord, tailWord_2438639, baseEnd_2438639] using wordTrace_append hprefix tailTrace_2438639
  have hstable : (prefixWord ++ tailWord_2438639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438639).length < 2 ^ (prefixWord ++ tailWord_2438639).sum := by decide
  have hdescent : baseEnd_2438639 < baseStart_2438639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438650 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_2438650 : Nat := 118140960795 + 2438650 * 2 ^ 59
def prefixEnd_2438650 : Nat := 4983230072969 + 3 ^ 40 * 2438650 * 2
def baseEnd_2438650 : Nat := 834799732057992669573239

theorem tailTrace_2438650 : CollatzResearch.WordTrace tailWord_2438650 prefixEnd_2438650 834799732057992669573239 := by
  unfold tailWord_2438650
  simp only [CollatzResearch.WordTrace]
  refine ⟨22236218153798753276696351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59296581743463342071190269 22236218153798753276696351)
  ·
    refine ⟨33354327230698129915044527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22236218153798753276696351 33354327230698129915044527)
    ·
      refine ⟨50031490846047194872566791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33354327230698129915044527 50031490846047194872566791)
      ·
        refine ⟨75047236269070792308850187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50031490846047194872566791 75047236269070792308850187)
        ·
          refine ⟨112570854403606188463275281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75047236269070792308850187 112570854403606188463275281)
          ·
            refine ⟨84428140802704641347456461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112570854403606188463275281 84428140802704641347456461)
            ·
              refine ⟨31660552801014240505296173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84428140802704641347456461 31660552801014240505296173)
              ·
                refine ⟨11872707300380340189486065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31660552801014240505296173 11872707300380340189486065)
                ·
                  refine ⟨8904530475285255142114549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11872707300380340189486065 8904530475285255142114549)
                  ·
                    refine ⟨834799732057992669573239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8904530475285255142114549 834799732057992669573239)
                    ·
                      rfl

theorem cell22_2438650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_2438650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438650 prefixEnd_2438650 := by exact prefixLift 2438650
  have htrace : WordTrace (prefixWord ++ tailWord_2438650) baseStart_2438650 baseEnd_2438650 := by
    simpa [prefixWord, tailWord_2438650, baseEnd_2438650] using wordTrace_append hprefix tailTrace_2438650
  have hstable : (prefixWord ++ tailWord_2438650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438650).length < 2 ^ (prefixWord ++ tailWord_2438650).sum := by decide
  have hdescent : baseEnd_2438650 < baseStart_2438650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438716 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_2438716 : Nat := 118140960795 + 2438716 * 2 ^ 59
def prefixEnd_2438716 : Nat := 4983230072969 + 3 ^ 40 * 2438716 * 2
def baseEnd_2438716 : Nat := 834822325206790497423037

theorem tailTrace_2438716 : CollatzResearch.WordTrace tailWord_2438716 prefixEnd_2438716 834822325206790497423037 := by
  unfold tailWord_2438716
  simp only [CollatzResearch.WordTrace]
  refine ⟨44473639916477953189344001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59298186555303937585792001 44473639916477953189344001)
  ·
    refine ⟨33355229937358464892008001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44473639916477953189344001 33355229937358464892008001)
    ·
      refine ⟨25016422453018848669006001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33355229937358464892008001 25016422453018848669006001)
      ·
        refine ⟨18762316839764136501754501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25016422453018848669006001 18762316839764136501754501)
        ·
          refine ⟨3517934407455775594078969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18762316839764136501754501 3517934407455775594078969)
          ·
            refine ⟨2638450805591831695559227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3517934407455775594078969 2638450805591831695559227)
            ·
              refine ⟨3957676208387747543338841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638450805591831695559227 3957676208387747543338841)
              ·
                refine ⟨2968257156290810657504131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3957676208387747543338841 2968257156290810657504131)
                ·
                  refine ⟨4452385734436215986256197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968257156290810657504131 4452385734436215986256197)
                  ·
                    refine ⟨834822325206790497423037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452385734436215986256197 834822325206790497423037)
                    ·
                      rfl

theorem cell22_2438716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_2438716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438716 prefixEnd_2438716 := by exact prefixLift 2438716
  have htrace : WordTrace (prefixWord ++ tailWord_2438716) baseStart_2438716 baseEnd_2438716 := by
    simpa [prefixWord, tailWord_2438716, baseEnd_2438716] using wordTrace_append hprefix tailTrace_2438716
  have hstable : (prefixWord ++ tailWord_2438716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438716).length < 2 ^ (prefixWord ++ tailWord_2438716).sum := by decide
  have hdescent : baseEnd_2438716 < baseStart_2438716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438725 : List Nat := [1, 3, 1, 1, 1, 4, 1, 10]
def baseStart_2438725 : Nat := 118140960795 + 2438725 * 2 ^ 59
def prefixEnd_2438725 : Nat := 4983230072969 + 3 ^ 40 * 2438725 * 2
def baseEnd_2438725 : Nat := 92758378454524163772001

theorem tailTrace_2438725 : CollatzResearch.WordTrace tailWord_2438725 prefixEnd_2438725 92758378454524163772001 := by
  unfold tailWord_2438725
  simp only [CollatzResearch.WordTrace]
  refine ⟨88947608089923300915765629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59298405393282200610510419 88947608089923300915765629)
  ·
    refine ⟨33355353033721237843412111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88947608089923300915765629 33355353033721237843412111)
    ·
      refine ⟨50033029550581856765118167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33355353033721237843412111 50033029550581856765118167)
      ·
        refine ⟨75049544325872785147677251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50033029550581856765118167 75049544325872785147677251)
        ·
          refine ⟨112574316488809177721515877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75049544325872785147677251 112574316488809177721515877)
          ·
            refine ⟨21107684341651720822784227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112574316488809177721515877 21107684341651720822784227)
            ·
              refine ⟨31661526512477581234176341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21107684341651720822784227 31661526512477581234176341)
              ·
                refine ⟨92758378454524163772001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31661526512477581234176341 92758378454524163772001)
                ·
                  rfl

theorem cell22_2438725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 10].length) (baseStart_2438725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438725 prefixEnd_2438725 := by exact prefixLift 2438725
  have htrace : WordTrace (prefixWord ++ tailWord_2438725) baseStart_2438725 baseEnd_2438725 := by
    simpa [prefixWord, tailWord_2438725, baseEnd_2438725] using wordTrace_append hprefix tailTrace_2438725
  have hstable : (prefixWord ++ tailWord_2438725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438725).length < 2 ^ (prefixWord ++ tailWord_2438725).sum := by decide
  have hdescent : baseEnd_2438725 < baseStart_2438725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438733 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2438733 : Nat := 118140960795 + 2438733 * 2 ^ 59
def prefixEnd_2438733 : Nat := 4983230072969 + 3 ^ 40 * 2438733 * 2
def baseEnd_2438733 : Nat := 834828144654208119747985

theorem tailTrace_2438733 : CollatzResearch.WordTrace tailWord_2438733 prefixEnd_2438733 834828144654208119747985 := by
  unfold tailWord_2438733
  simp only [CollatzResearch.WordTrace]
  refine ⟨88947899873894318282056853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59298599915929545521371235 88947899873894318282056853)
  ·
    refine ⟨4169432806588796169471415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88947899873894318282056853 4169432806588796169471415)
    ·
      refine ⟨6254149209883194254207123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4169432806588796169471415 6254149209883194254207123)
      ·
        refine ⟨9381223814824791381310685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254149209883194254207123 9381223814824791381310685)
        ·
          refine ⟨3517958930559296767991507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9381223814824791381310685 3517958930559296767991507)
          ·
            refine ⟨5276938395838945151987261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3517958930559296767991507 5276938395838945151987261)
            ·
              refine ⟨1978851898439604431995223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5276938395838945151987261 1978851898439604431995223)
              ·
                refine ⟨2968277847659406647992835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978851898439604431995223 2968277847659406647992835)
                ·
                  refine ⟨4452416771489109971989253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968277847659406647992835 4452416771489109971989253)
                  ·
                    refine ⟨834828144654208119747985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452416771489109971989253 834828144654208119747985)
                    ·
                      rfl

theorem cell22_2438733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2438733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438733 prefixEnd_2438733 := by exact prefixLift 2438733
  have htrace : WordTrace (prefixWord ++ tailWord_2438733) baseStart_2438733 baseEnd_2438733 := by
    simpa [prefixWord, tailWord_2438733, baseEnd_2438733] using wordTrace_append hprefix tailTrace_2438733
  have hstable : (prefixWord ++ tailWord_2438733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438733).length < 2 ^ (prefixWord ++ tailWord_2438733).sum := by decide
  have hdescent : baseEnd_2438733 < baseStart_2438733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438748 : List Nat := [2, 2, 4, 1, 2, 3, 2, 2, 4]
def baseStart_2438748 : Nat := 118140960795 + 2438748 * 2 ^ 59
def prefixEnd_2438748 : Nat := 4983230072969 + 3 ^ 40 * 2438748 * 2
def baseEnd_2438748 : Nat := 278277759820251026874313

theorem tailTrace_2438748 : CollatzResearch.WordTrace tailWord_2438748 prefixEnd_2438748 278277759820251026874313 := by
  unfold tailWord_2438748
  simp only [CollatzResearch.WordTrace]
  refine ⟨44474223484419987921926449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59298964645893317229235265 44474223484419987921926449)
  ·
    refine ⟨33355667613314990941444837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44474223484419987921926449 33355667613314990941444837)
    ·
      refine ⟨6254187677496560801520907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33355667613314990941444837 6254187677496560801520907)
      ·
        refine ⟨9381281516244841202281361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254187677496560801520907 9381281516244841202281361)
        ·
          refine ⟨7035961137183630901711021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9381281516244841202281361 7035961137183630901711021)
          ·
            refine ⟨2638485426443861588141633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7035961137183630901711021 2638485426443861588141633)
            ·
              refine ⟨1978864069832896191106225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638485426443861588141633 1978864069832896191106225)
              ·
                refine ⟨1484148052374672143329669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978864069832896191106225 1484148052374672143329669)
                ·
                  refine ⟨278277759820251026874313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484148052374672143329669 278277759820251026874313)
                  ·
                    rfl

theorem cell22_2438748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 4].length) (baseStart_2438748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438748 prefixEnd_2438748 := by exact prefixLift 2438748
  have htrace : WordTrace (prefixWord ++ tailWord_2438748) baseStart_2438748 baseEnd_2438748 := by
    simpa [prefixWord, tailWord_2438748, baseEnd_2438748] using wordTrace_append hprefix tailTrace_2438748
  have hstable : (prefixWord ++ tailWord_2438748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438748).length < 2 ^ (prefixWord ++ tailWord_2438748).sum := by decide
  have hdescent : baseEnd_2438748 < baseStart_2438748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438791 : List Nat := [1, 1, 4, 2, 1, 3, 1, 5, 1, 3]
def baseStart_2438791 : Nat := 118140960795 + 2438791 * 2 ^ 59
def prefixEnd_2438791 : Nat := 4983230072969 + 3 ^ 40 * 2438791 * 2
def baseEnd_2438791 : Nat := 834847999239515301797807

theorem tailTrace_2438791 : CollatzResearch.WordTrace tailWord_2438791 prefixEnd_2438791 834847999239515301797807 := by
  unfold tailWord_2438791
  simp only [CollatzResearch.WordTrace]
  refine ⟨88950015307684194187668227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59300010205122796125112151 88950015307684194187668227)
  ·
    refine ⟨133425022961526291281502341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88950015307684194187668227 133425022961526291281502341)
    ·
      refine ⟨25017191805286179615281689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133425022961526291281502341 25017191805286179615281689)
      ·
        refine ⟨18762893853964634711461267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25017191805286179615281689 18762893853964634711461267)
        ·
          refine ⟨28144340780946952067191901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18762893853964634711461267 28144340780946952067191901)
          ·
            refine ⟨10554127792855107025196963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28144340780946952067191901 10554127792855107025196963)
            ·
              refine ⟨15831191689282660537795445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10554127792855107025196963 15831191689282660537795445)
              ·
                refine ⟨1484174220870249425418323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15831191689282660537795445 1484174220870249425418323)
                ·
                  refine ⟨2226261331305374138127485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484174220870249425418323 2226261331305374138127485)
                  ·
                    refine ⟨834847999239515301797807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226261331305374138127485 834847999239515301797807)
                    ·
                      rfl

theorem cell22_2438791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_2438791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438791 prefixEnd_2438791 := by exact prefixLift 2438791
  have htrace : WordTrace (prefixWord ++ tailWord_2438791) baseStart_2438791 baseEnd_2438791 := by
    simpa [prefixWord, tailWord_2438791, baseEnd_2438791] using wordTrace_append hprefix tailTrace_2438791
  have hstable : (prefixWord ++ tailWord_2438791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438791).length < 2 ^ (prefixWord ++ tailWord_2438791).sum := by decide
  have hdescent : baseEnd_2438791 < baseStart_2438791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438832 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 6]
def baseStart_2438832 : Nat := 118140960795 + 2438832 * 2 ^ 59
def prefixEnd_2438832 : Nat := 4983230072969 + 3 ^ 40 * 2438832 * 2
def baseEnd_2438832 : Nat := 278287344792468287174227

theorem tailTrace_2438832 : CollatzResearch.WordTrace tailWord_2438832 prefixEnd_2438832 278287344792468287174227 := by
  unfold tailWord_2438832
  simp only [CollatzResearch.WordTrace]
  refine ⟨44475755350267829094955375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59301007133690438793273833 44475755350267829094955375)
  ·
    refine ⟨66713633025401743642433063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44475755350267829094955375 66713633025401743642433063)
    ·
      refine ⟨100070449538102615463649595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66713633025401743642433063 100070449538102615463649595)
      ·
        refine ⟨150105674307153923195474393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100070449538102615463649595 150105674307153923195474393)
        ·
          refine ⟨112579255730365442396605795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150105674307153923195474393 112579255730365442396605795)
          ·
            refine ⟨168868883595548163594908693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112579255730365442396605795 168868883595548163594908693)
            ·
              refine ⟨7915728918541320168511345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168868883595548163594908693 7915728918541320168511345)
              ·
                refine ⟨5936796688905990126383509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7915728918541320168511345 5936796688905990126383509)
                ·
                  refine ⟨278287344792468287174227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5936796688905990126383509 278287344792468287174227)
                  ·
                    rfl

theorem cell22_2438832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_2438832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438832 prefixEnd_2438832 := by exact prefixLift 2438832
  have htrace : WordTrace (prefixWord ++ tailWord_2438832) baseStart_2438832 baseEnd_2438832 := by
    simpa [prefixWord, tailWord_2438832, baseEnd_2438832] using wordTrace_append hprefix tailTrace_2438832
  have hstable : (prefixWord ++ tailWord_2438832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438832).length < 2 ^ (prefixWord ++ tailWord_2438832).sum := by decide
  have hdescent : baseEnd_2438832 < baseStart_2438832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438834 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_2438834 : Nat := 118140960795 + 2438834 * 2 ^ 59
def prefixEnd_2438834 : Nat := 4983230072969 + 3 ^ 40 * 2438834 * 2
def baseEnd_2438834 : Nat := 834862719018277522972675

theorem tailTrace_2438834 : CollatzResearch.WordTrace tailWord_2438834 prefixEnd_2438834 834862719018277522972675 := by
  unfold tailWord_2438834
  simp only [CollatzResearch.WordTrace]
  refine ⟨22237895911632103132870889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59301055764352275020989037 22237895911632103132870889)
  ·
    refine ⟨16678421933724077349653167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22237895911632103132870889 16678421933724077349653167)
    ·
      refine ⟨25017632900586116024479751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16678421933724077349653167 25017632900586116024479751)
      ·
        refine ⟨37526449350879174036719627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25017632900586116024479751 37526449350879174036719627)
        ·
          refine ⟨56289674026318761055079441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37526449350879174036719627 56289674026318761055079441)
          ·
            refine ⟨42217255519739070791309581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56289674026318761055079441 42217255519739070791309581)
            ·
              refine ⟨15831470819902151546741093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42217255519739070791309581 15831470819902151546741093)
              ·
                refine ⟨2968400778731653415013955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15831470819902151546741093 2968400778731653415013955)
                ·
                  refine ⟨4452601168097480122520933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968400778731653415013955 4452601168097480122520933)
                  ·
                    refine ⟨834862719018277522972675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452601168097480122520933 834862719018277522972675)
                    ·
                      rfl

theorem cell22_2438834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_2438834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438834 prefixEnd_2438834 := by exact prefixLift 2438834
  have htrace : WordTrace (prefixWord ++ tailWord_2438834) baseStart_2438834 baseEnd_2438834 := by
    simpa [prefixWord, tailWord_2438834, baseEnd_2438834] using wordTrace_append hprefix tailTrace_2438834
  have hstable : (prefixWord ++ tailWord_2438834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438834).length < 2 ^ (prefixWord ++ tailWord_2438834).sum := by decide
  have hdescent : baseEnd_2438834 < baseStart_2438834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438847 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 3, 5]
def baseStart_2438847 : Nat := 118140960795 + 2438847 * 2 ^ 59
def prefixEnd_2438847 : Nat := 4983230072969 + 3 ^ 40 * 2438847 * 2
def baseEnd_2438847 : Nat := 834867169183949822397635

theorem tailTrace_2438847 : CollatzResearch.WordTrace tailWord_2438847 prefixEnd_2438847 834867169183949822397635 := by
  unfold tailWord_2438847
  simp only [CollatzResearch.WordTrace]
  refine ⟨88952057795481315751706795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59301371863654210501137863 88952057795481315751706795)
  ·
    refine ⟨133428086693221973627560193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88952057795481315751706795 133428086693221973627560193)
    ·
      refine ⟨100071065019916480220670145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133428086693221973627560193 100071065019916480220670145)
      ·
        refine ⟨75053298764937360165502609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100071065019916480220670145 75053298764937360165502609)
        ·
          refine ⟨56289974073703020124126957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75053298764937360165502609 56289974073703020124126957)
          ·
            refine ⟨21108740277638632546547609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56289974073703020124126957 21108740277638632546547609)
            ·
              refine ⟨15831555208228974409910707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21108740277638632546547609 15831555208228974409910707)
              ·
                refine ⟨23747332812343461614866061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15831555208228974409910707 23747332812343461614866061)
                ·
                  refine ⟨8905249804628798105574773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23747332812343461614866061 8905249804628798105574773)
                  ·
                    refine ⟨834867169183949822397635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8905249804628798105574773 834867169183949822397635)
                    ·
                      rfl

theorem cell22_2438847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_2438847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438847 prefixEnd_2438847 := by exact prefixLift 2438847
  have htrace : WordTrace (prefixWord ++ tailWord_2438847) baseStart_2438847 baseEnd_2438847 := by
    simpa [prefixWord, tailWord_2438847, baseEnd_2438847] using wordTrace_append hprefix tailTrace_2438847
  have hstable : (prefixWord ++ tailWord_2438847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438847).length < 2 ^ (prefixWord ++ tailWord_2438847).sum := by decide
  have hdescent : baseEnd_2438847 < baseStart_2438847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438866 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 6]
def baseStart_2438866 : Nat := 118140960795 + 2438866 * 2 ^ 59
def prefixEnd_2438866 : Nat := 4983230072969 + 3 ^ 40 * 2438866 * 2
def baseEnd_2438866 : Nat := 278291224424080035390859

theorem tailTrace_2438866 : CollatzResearch.WordTrace tailWord_2438866 prefixEnd_2438866 278291224424080035390859 := by
  unfold tailWord_2438866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22238187695603120499162113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59301833854941654664432301 22238187695603120499162113)
  ·
    refine ⟨16678640771702340374371585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22238187695603120499162113 16678640771702340374371585)
    ·
      refine ⟨12508980578776755280778689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16678640771702340374371585 12508980578776755280778689)
      ·
        refine ⟨9381735434082566460584017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12508980578776755280778689 9381735434082566460584017)
        ·
          refine ⟨7036301575561924845438013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9381735434082566460584017 7036301575561924845438013)
          ·
            refine ⟨2638613090835721817039255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7036301575561924845438013 2638613090835721817039255)
            ·
              refine ⟨3957919636253582725558883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638613090835721817039255 3957919636253582725558883)
              ·
                refine ⟨5936879454380374088338325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957919636253582725558883 5936879454380374088338325)
                ·
                  refine ⟨278291224424080035390859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5936879454380374088338325 278291224424080035390859)
                  ·
                    rfl

theorem cell22_2438866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_2438866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438866 prefixEnd_2438866 := by exact prefixLift 2438866
  have htrace : WordTrace (prefixWord ++ tailWord_2438866) baseStart_2438866 baseEnd_2438866 := by
    simpa [prefixWord, tailWord_2438866, baseEnd_2438866] using wordTrace_append hprefix tailTrace_2438866
  have hstable : (prefixWord ++ tailWord_2438866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438866).length < 2 ^ (prefixWord ++ tailWord_2438866).sum := by decide
  have hdescent : baseEnd_2438866 < baseStart_2438866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438892 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_2438892 : Nat := 118140960795 + 2438892 * 2 ^ 59
def prefixEnd_2438892 : Nat := 4983230072969 + 3 ^ 40 * 2438892 * 2
def baseEnd_2438892 : Nat := 834882573603584705022497

theorem tailTrace_2438892 : CollatzResearch.WordTrace tailWord_2438892 prefixEnd_2438892 834882573603584705022497 := by
  unfold tailWord_2438892
  simp only [CollatzResearch.WordTrace]
  refine ⟨44476849540159144218547465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59302466053545525624729953 44476849540159144218547465)
  ·
    refine ⟨33357637155119358163910599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44476849540159144218547465 33357637155119358163910599)
    ·
      refine ⟨50036455732679037245865899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33357637155119358163910599 50036455732679037245865899)
      ·
        refine ⟨75054683599018555868798849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50036455732679037245865899 75054683599018555868798849)
        ·
          refine ⟨56291012699263916901599137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75054683599018555868798849 56291012699263916901599137)
          ·
            refine ⟨42218259524447937676199353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56291012699263916901599137 42218259524447937676199353)
            ·
              refine ⟨31663694643335953257149515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42218259524447937676199353 31663694643335953257149515)
              ·
                refine ⟨47495541965003929885724273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31663694643335953257149515 47495541965003929885724273)
                ·
                  refine ⟨35621656473752947414293205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47495541965003929885724273 35621656473752947414293205)
                  ·
                    refine ⟨834882573603584705022497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35621656473752947414293205 834882573603584705022497)
                    ·
                      rfl

theorem cell22_2438892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_2438892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438892 prefixEnd_2438892 := by exact prefixLift 2438892
  have htrace : WordTrace (prefixWord ++ tailWord_2438892) baseStart_2438892 baseEnd_2438892 := by
    simpa [prefixWord, tailWord_2438892, baseEnd_2438892] using wordTrace_append hprefix tailTrace_2438892
  have hstable : (prefixWord ++ tailWord_2438892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438892).length < 2 ^ (prefixWord ++ tailWord_2438892).sum := by decide
  have hdescent : baseEnd_2438892 < baseStart_2438892 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438909 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_2438909 : Nat := 118140960795 + 2438909 * 2 ^ 59
def prefixEnd_2438909 : Nat := 4983230072969 + 3 ^ 40 * 2438909 * 2
def baseEnd_2438909 : Nat := 834888393051002327347445

theorem tailTrace_2438909 : CollatzResearch.WordTrace tailWord_2438909 prefixEnd_2438909 834888393051002327347445 := by
  unfold tailWord_2438909
  simp only [CollatzResearch.WordTrace]
  refine ⟨88954319121256700340463781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59302879414171133560309187 88954319121256700340463781)
  ·
    refine ⟨16678934835235631313836959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88954319121256700340463781 16678934835235631313836959)
    ·
      refine ⟨25018402252853446970755439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16678934835235631313836959 25018402252853446970755439)
      ·
        refine ⟨37527603379280170456133159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25018402252853446970755439 37527603379280170456133159)
        ·
          refine ⟨56291405068920255684199739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37527603379280170456133159 56291405068920255684199739)
          ·
            refine ⟨84437107603380383526299609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56291405068920255684199739 84437107603380383526299609)
            ·
              refine ⟨63327830702535287644724707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84437107603380383526299609 63327830702535287644724707)
              ·
                refine ⟨94991746053802931467087061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63327830702535287644724707 94991746053802931467087061)
                ·
                  refine ⟨2226369048136006206259853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 94991746053802931467087061 2226369048136006206259853)
                  ·
                    refine ⟨834888393051002327347445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226369048136006206259853 834888393051002327347445)
                    ·
                      rfl

theorem cell22_2438909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_2438909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438909 prefixEnd_2438909 := by exact prefixLift 2438909
  have htrace : WordTrace (prefixWord ++ tailWord_2438909) baseStart_2438909 baseEnd_2438909 := by
    simpa [prefixWord, tailWord_2438909, baseEnd_2438909] using wordTrace_append hprefix tailTrace_2438909
  have hstable : (prefixWord ++ tailWord_2438909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438909).length < 2 ^ (prefixWord ++ tailWord_2438909).sum := by decide
  have hdescent : baseEnd_2438909 < baseStart_2438909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438973 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2438973 : Nat := 118140960795 + 2438973 * 2 ^ 59
def prefixEnd_2438973 : Nat := 4983230072969 + 3 ^ 40 * 2438973 * 2
def baseEnd_2438973 : Nat := 278303433852975831249083

theorem tailTrace_2438973 : CollatzResearch.WordTrace tailWord_2438973 prefixEnd_2438973 278303433852975831249083 := by
  unfold tailWord_2438973
  simp only [CollatzResearch.WordTrace]
  refine ⟨88956653393024839270793573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59304435595349892847195715 88956653393024839270793573)
  ·
    refine ⟨16679372511192157363273795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88956653393024839270793573 16679372511192157363273795)
    ·
      refine ⟨25019058766788236044910693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16679372511192157363273795 25019058766788236044910693)
      ·
        refine ⟨4691073518772794258420755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25019058766788236044910693 4691073518772794258420755)
        ·
          refine ⟨7036610278159191387631133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691073518772794258420755 7036610278159191387631133)
          ·
            refine ⟨2638728854309696770361675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7036610278159191387631133 2638728854309696770361675)
            ·
              refine ⟨3958093281464545155542513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638728854309696770361675 3958093281464545155542513)
              ·
                refine ⟨2968569961098408866656885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958093281464545155542513 2968569961098408866656885)
                ·
                  refine ⟨278303433852975831249083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968569961098408866656885 278303433852975831249083)
                  ·
                    rfl

theorem cell22_2438973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2438973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438973 prefixEnd_2438973 := by exact prefixLift 2438973
  have htrace : WordTrace (prefixWord ++ tailWord_2438973) baseStart_2438973 baseEnd_2438973 := by
    simpa [prefixWord, tailWord_2438973, baseEnd_2438973] using wordTrace_append hprefix tailTrace_2438973
  have hstable : (prefixWord ++ tailWord_2438973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438973).length < 2 ^ (prefixWord ++ tailWord_2438973).sum := by decide
  have hdescent : baseEnd_2438973 < baseStart_2438973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2438984 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 6]
def baseStart_2438984 : Nat := 118140960795 + 2438984 * 2 ^ 59
def prefixEnd_2438984 : Nat := 4983230072969 + 3 ^ 40 * 2438984 * 2
def baseEnd_2438984 : Nat := 278304689027909043907405

theorem tailTrace_2438984 : CollatzResearch.WordTrace tailWord_2438984 prefixEnd_2438984 278304689027909043907405 := by
  unfold tailWord_2438984
  simp only [CollatzResearch.WordTrace]
  refine ⟨44478527297992494074722003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59304703063989992099629337 44478527297992494074722003)
  ·
    refine ⟨66717790946988741112083005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44478527297992494074722003 66717790946988741112083005)
    ·
      refine ⟨25019171605120777917031127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66717790946988741112083005 25019171605120777917031127)
      ·
        refine ⟨37528757407681166875546691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25019171605120777917031127 37528757407681166875546691)
        ·
          refine ⟨56293136111521750313320037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37528757407681166875546691 56293136111521750313320037)
          ·
            refine ⟨10554963020910328183747507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56293136111521750313320037 10554963020910328183747507)
            ·
              refine ⟨15832444531365492275621261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10554963020910328183747507 15832444531365492275621261)
              ·
                refine ⟨5937166699262059603357973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15832444531365492275621261 5937166699262059603357973)
                ·
                  refine ⟨278304689027909043907405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5937166699262059603357973 278304689027909043907405)
                  ·
                    rfl

theorem cell22_2438984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_2438984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2438984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2438984 prefixEnd_2438984 := by exact prefixLift 2438984
  have htrace : WordTrace (prefixWord ++ tailWord_2438984) baseStart_2438984 baseEnd_2438984 := by
    simpa [prefixWord, tailWord_2438984, baseEnd_2438984] using wordTrace_append hprefix tailTrace_2438984
  have hstable : (prefixWord ++ tailWord_2438984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2438984).length < 2 ^ (prefixWord ++ tailWord_2438984).sum := by decide
  have hdescent : baseEnd_2438984 < baseStart_2438984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2438984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439016 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2439016 : Nat := 118140960795 + 2439016 * 2 ^ 59
def prefixEnd_2439016 : Nat := 4983230072969 + 3 ^ 40 * 2439016 * 2
def baseEnd_2439016 : Nat := 834925021337689714922117

theorem tailTrace_2439016 : CollatzResearch.WordTrace tailWord_2439016 prefixEnd_2439016 834925021337689714922117 := by
  unfold tailWord_2439016
  simp only [CollatzResearch.WordTrace]
  refine ⟨44479110865934528807304451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59305481154579371743072601 44479110865934528807304451)
  ·
    refine ⟨66718666298901793210956677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44479110865934528807304451 66718666298901793210956677)
    ·
      refine ⟨12509749931044086227054377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66718666298901793210956677 12509749931044086227054377)
      ·
        refine ⟨9382312448283064670290783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12509749931044086227054377 9382312448283064670290783)
        ·
          refine ⟨14073468672424597005436175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9382312448283064670290783 14073468672424597005436175)
          ·
            refine ⟨21110203008636895508154263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14073468672424597005436175 21110203008636895508154263)
            ·
              refine ⟨31665304512955343262231395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21110203008636895508154263 31665304512955343262231395)
              ·
                refine ⟨47497956769433014893347093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31665304512955343262231395 47497956769433014893347093)
                ·
                  refine ⟨2226466723567172573125645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47497956769433014893347093 2226466723567172573125645)
                  ·
                    refine ⟨834925021337689714922117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226466723567172573125645 834925021337689714922117)
                    ·
                      rfl

theorem cell22_2439016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2439016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439016 prefixEnd_2439016 := by exact prefixLift 2439016
  have htrace : WordTrace (prefixWord ++ tailWord_2439016) baseStart_2439016 baseEnd_2439016 := by
    simpa [prefixWord, tailWord_2439016, baseEnd_2439016] using wordTrace_append hprefix tailTrace_2439016
  have hstable : (prefixWord ++ tailWord_2439016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439016).length < 2 ^ (prefixWord ++ tailWord_2439016).sum := by decide
  have hdescent : baseEnd_2439016 < baseStart_2439016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439050 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_2439050 : Nat := 118140960795 + 2439050 * 2 ^ 59
def prefixEnd_2439050 : Nat := 4983230072969 + 3 ^ 40 * 2439050 * 2
def baseEnd_2439050 : Nat := 834936660232524959572013

theorem tailTrace_2439050 : CollatzResearch.WordTrace tailWord_2439050 prefixEnd_2439050 834936660232524959572013 := by
  unfold tailWord_2439050
  simp only [CollatzResearch.WordTrace]
  refine ⟨22239865453436470355336651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59306307875830587614231069 22239865453436470355336651)
  ·
    refine ⟨33359798180154705533004977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22239865453436470355336651 33359798180154705533004977)
    ·
      refine ⟨25019848635116029149753733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33359798180154705533004977 25019848635116029149753733)
      ·
        refine ⟨4691221619084255465578825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25019848635116029149753733 4691221619084255465578825)
        ·
          refine ⟨3518416214313191599184119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4691221619084255465578825 3518416214313191599184119)
          ·
            refine ⟨5277624321469787398776179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518416214313191599184119 5277624321469787398776179)
            ·
              refine ⟨7916436482204681098164269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5277624321469787398776179 7916436482204681098164269)
              ·
                refine ⟨2968663680826755411811601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7916436482204681098164269 2968663680826755411811601)
                ·
                  refine ⟨2226497760620066558858701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2968663680826755411811601 2226497760620066558858701)
                  ·
                    refine ⟨834936660232524959572013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226497760620066558858701 834936660232524959572013)
                    ·
                      rfl

theorem cell22_2439050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_2439050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439050 prefixEnd_2439050 := by exact prefixLift 2439050
  have htrace : WordTrace (prefixWord ++ tailWord_2439050) baseStart_2439050 baseEnd_2439050 := by
    simpa [prefixWord, tailWord_2439050, baseEnd_2439050] using wordTrace_append hprefix tailTrace_2439050
  have hstable : (prefixWord ++ tailWord_2439050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439050).length < 2 ^ (prefixWord ++ tailWord_2439050).sum := by decide
  have hdescent : baseEnd_2439050 < baseStart_2439050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439061 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2439061 : Nat := 118140960795 + 2439061 * 2 ^ 59
def prefixEnd_2439061 : Nat := 4983230072969 + 3 ^ 40 * 2439061 * 2
def baseEnd_2439061 : Nat := 834940425757324597546979

theorem tailTrace_2439061 : CollatzResearch.WordTrace tailWord_2439061 prefixEnd_2439061 834940425757324597546979 := by
  unfold tailWord_2439061
  simp only [CollatzResearch.WordTrace]
  refine ⟨88959863016706030299997037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59306575344470686866664691 88959863016706030299997037)
  ·
    refine ⟨33359948631264761362498889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88959863016706030299997037 33359948631264761362498889)
    ·
      refine ⟨25019961473448571021874167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33359948631264761362498889 25019961473448571021874167)
      ·
        refine ⟨37529942210172856532811251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25019961473448571021874167 37529942210172856532811251)
        ·
          refine ⟨56294913315259284799216877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37529942210172856532811251 56294913315259284799216877)
          ·
            refine ⟨21110592493222231799706329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56294913315259284799216877 21110592493222231799706329)
            ·
              refine ⟨15832944369916673849779747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21110592493222231799706329 15832944369916673849779747)
              ·
                refine ⟨23749416554875010774669621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15832944369916673849779747 23749416554875010774669621)
                ·
                  refine ⟨2226507802019532260125277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23749416554875010774669621 2226507802019532260125277)
                  ·
                    refine ⟨834940425757324597546979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226507802019532260125277 834940425757324597546979)
                    ·
                      rfl

theorem cell22_2439061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2439061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439061 prefixEnd_2439061 := by exact prefixLift 2439061
  have htrace : WordTrace (prefixWord ++ tailWord_2439061) baseStart_2439061 baseEnd_2439061 := by
    simpa [prefixWord, tailWord_2439061, baseEnd_2439061] using wordTrace_append hprefix tailTrace_2439061
  have hstable : (prefixWord ++ tailWord_2439061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439061).length < 2 ^ (prefixWord ++ tailWord_2439061).sum := by decide
  have hdescent : baseEnd_2439061 < baseStart_2439061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439086 : List Nat := [4, 1, 5, 1, 1, 2, 2, 2, 4]
def baseStart_2439086 : Nat := 118140960795 + 2439086 * 2 ^ 59
def prefixEnd_2439086 : Nat := 4983230072969 + 3 ^ 40 * 2439086 * 2
def baseEnd_2439086 : Nat := 278316327922744288557301

theorem tailTrace_2439086 : CollatzResearch.WordTrace tailWord_2439086 prefixEnd_2439086 278316327922744288557301 := by
  unfold tailWord_2439086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11120096855201932446207139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59307183227743639713104741 11120096855201932446207139)
  ·
    refine ⟨16680145282802898669310709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11120096855201932446207139 16680145282802898669310709)
    ·
      refine ⟨1563763620262771750247879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16680145282802898669310709 1563763620262771750247879)
      ·
        refine ⟨2345645430394157625371819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563763620262771750247879 2345645430394157625371819)
        ·
          refine ⟨3518468145591236438057729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345645430394157625371819 3518468145591236438057729)
          ·
            refine ⟨2638851109193427328543297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518468145591236438057729 2638851109193427328543297)
            ·
              refine ⟨1979138331895070496407473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638851109193427328543297 1979138331895070496407473)
              ·
                refine ⟨1484353748921302872305605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979138331895070496407473 1484353748921302872305605)
                ·
                  refine ⟨278316327922744288557301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484353748921302872305605 278316327922744288557301)
                  ·
                    rfl

theorem cell22_2439086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_2439086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439086 prefixEnd_2439086 := by exact prefixLift 2439086
  have htrace : WordTrace (prefixWord ++ tailWord_2439086) baseStart_2439086 baseEnd_2439086 := by
    simpa [prefixWord, tailWord_2439086, baseEnd_2439086] using wordTrace_append hprefix tailTrace_2439086
  have hstable : (prefixWord ++ tailWord_2439086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439086).length < 2 ^ (prefixWord ++ tailWord_2439086).sum := by decide
  have hdescent : baseEnd_2439086 < baseStart_2439086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439091 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 5]
def baseStart_2439091 : Nat := 118140960795 + 2439091 * 2 ^ 59
def prefixEnd_2439091 : Nat := 4983230072969 + 3 ^ 40 * 2439091 * 2
def baseEnd_2439091 : Nat := 278316898456804839765629

theorem tailTrace_2439091 : CollatzResearch.WordTrace tailWord_2439091 prefixEnd_2439091 278316898456804839765629 := by
  unfold tailWord_2439091
  simp only [CollatzResearch.WordTrace]
  refine ⟨88960957206597345423589127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59307304804398230282392751 88960957206597345423589127)
  ·
    refine ⟨133441435809896018135383691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88960957206597345423589127 133441435809896018135383691)
    ·
      refine ⟨200162153714844027203075537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133441435809896018135383691 200162153714844027203075537)
      ·
        refine ⟨150121615286133020402306653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200162153714844027203075537 150121615286133020402306653)
        ·
          refine ⟨56295605732299882650864995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150121615286133020402306653 56295605732299882650864995)
          ·
            refine ⟨84443408598449823976297493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56295605732299882650864995 84443408598449823976297493)
            ·
              refine ⟨3958284778052335498888945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84443408598449823976297493 3958284778052335498888945)
              ·
                refine ⟨2968713583539251624166709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958284778052335498888945 2968713583539251624166709)
                ·
                  refine ⟨278316898456804839765629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968713583539251624166709 278316898456804839765629)
                  ·
                    rfl

theorem cell22_2439091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 5].length) (baseStart_2439091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439091 prefixEnd_2439091 := by exact prefixLift 2439091
  have htrace : WordTrace (prefixWord ++ tailWord_2439091) baseStart_2439091 baseEnd_2439091 := by
    simpa [prefixWord, tailWord_2439091, baseEnd_2439091] using wordTrace_append hprefix tailTrace_2439091
  have hstable : (prefixWord ++ tailWord_2439091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439091).length < 2 ^ (prefixWord ++ tailWord_2439091).sum := by decide
  have hdescent : baseEnd_2439091 < baseStart_2439091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439153 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 6]
def baseStart_2439153 : Nat := 118140960795 + 2439153 * 2 ^ 59
def prefixEnd_2439153 : Nat := 4983230072969 + 3 ^ 40 * 2439153 * 2
def baseEnd_2439153 : Nat := 278323973079155674748899

theorem tailTrace_2439153 : CollatzResearch.WordTrace tailWord_2439153 prefixEnd_2439153 278323973079155674748899 := by
  unfold tailWord_2439153
  simp only [CollatzResearch.WordTrace]
  refine ⟨88963218532372730012346113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59308812354915153341564075 88963218532372730012346113)
  ·
    refine ⟨66722413899279547509259585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88963218532372730012346113 66722413899279547509259585)
    ·
      refine ⟨50041810424459660631944689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66722413899279547509259585 50041810424459660631944689)
      ·
        refine ⟨37531357818344745473958517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50041810424459660631944689 37531357818344745473958517)
        ·
          refine ⟨3518564795469819888183611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37531357818344745473958517 3518564795469819888183611)
          ·
            refine ⟨5277847193204729832275417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518564795469819888183611 5277847193204729832275417)
            ·
              refine ⟨3958385394903547374206563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5277847193204729832275417 3958385394903547374206563)
              ·
                refine ⟨5937578092355321061309845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958385394903547374206563 5937578092355321061309845)
                ·
                  refine ⟨278323973079155674748899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5937578092355321061309845 278323973079155674748899)
                  ·
                    rfl

theorem cell22_2439153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_2439153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439153 prefixEnd_2439153 := by exact prefixLift 2439153
  have htrace : WordTrace (prefixWord ++ tailWord_2439153) baseStart_2439153 baseEnd_2439153 := by
    simpa [prefixWord, tailWord_2439153, baseEnd_2439153] using wordTrace_append hprefix tailTrace_2439153
  have hstable : (prefixWord ++ tailWord_2439153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439153).length < 2 ^ (prefixWord ++ tailWord_2439153).sum := by decide
  have hdescent : baseEnd_2439153 < baseStart_2439153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439172 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2439172 : Nat := 118140960795 + 2439172 * 2 ^ 59
def prefixEnd_2439172 : Nat := 4983230072969 + 3 ^ 40 * 2439172 * 2
def baseEnd_2439172 : Nat := 834978423325757308021639

theorem tailTrace_2439172 : CollatzResearch.WordTrace tailWord_2439172 prefixEnd_2439172 834978423325757308021639 := by
  unfold tailWord_2439172
  simp only [CollatzResearch.WordTrace]
  refine ⟨44481955759651948128643885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59309274346202597504858513 44481955759651948128643885)
  ·
    refine ⟨16680733409869480548241457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44481955759651948128643885 16680733409869480548241457)
    ·
      refine ⟨12510550057402110411181093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16680733409869480548241457 12510550057402110411181093)
      ·
        refine ⟨2345728135762895702096455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12510550057402110411181093 2345728135762895702096455)
        ·
          refine ⟨3518592203644343553144683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345728135762895702096455 3518592203644343553144683)
          ·
            refine ⟨5277888305466515329717025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518592203644343553144683 5277888305466515329717025)
            ·
              refine ⟨3958416229099886497287769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5277888305466515329717025 3958416229099886497287769)
              ·
                refine ⟨2968812171824914872965827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958416229099886497287769 2968812171824914872965827)
                ·
                  refine ⟨4453218257737372309448741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968812171824914872965827 4453218257737372309448741)
                  ·
                    refine ⟨834978423325757308021639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453218257737372309448741 834978423325757308021639)
                    ·
                      rfl

theorem cell22_2439172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2439172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439172 prefixEnd_2439172 := by exact prefixLift 2439172
  have htrace : WordTrace (prefixWord ++ tailWord_2439172) baseStart_2439172 baseEnd_2439172 := by
    simpa [prefixWord, tailWord_2439172, baseEnd_2439172] using wordTrace_append hprefix tailTrace_2439172
  have hstable : (prefixWord ++ tailWord_2439172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439172).length < 2 ^ (prefixWord ++ tailWord_2439172).sum := by decide
  have hdescent : baseEnd_2439172 < baseStart_2439172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439260 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 5]
def baseStart_2439260 : Nat := 118140960795 + 2439260 * 2 ^ 59
def prefixEnd_2439260 : Nat := 4983230072969 + 3 ^ 40 * 2439260 * 2
def baseEnd_2439260 : Nat := 278336182508051470607123

theorem tailTrace_2439260 : CollatzResearch.WordTrace tailWord_2439260 prefixEnd_2439260 278336182508051470607123 := by
  unfold tailWord_2439260
  simp only [CollatzResearch.WordTrace]
  refine ⟨44483560571492543643245617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59311414095323391524327489 44483560571492543643245617)
  ·
    refine ⟨33362670428619407732434213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44483560571492543643245617 33362670428619407732434213)
    ·
      refine ⟨6255500705366138949831415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33362670428619407732434213 6255500705366138949831415)
      ·
        refine ⟨9383251058049208424747123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6255500705366138949831415 9383251058049208424747123)
        ·
          refine ⟨14074876587073812637120685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9383251058049208424747123 14074876587073812637120685)
          ·
            refine ⟨5278078720152679738920257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14074876587073812637120685 5278078720152679738920257)
            ·
              refine ⟨3958559040114509804190193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278078720152679738920257 3958559040114509804190193)
              ·
                refine ⟨2968919280085882353142645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958559040114509804190193 2968919280085882353142645)
                ·
                  refine ⟨278336182508051470607123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968919280085882353142645 278336182508051470607123)
                  ·
                    rfl

theorem cell22_2439260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_2439260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439260 prefixEnd_2439260 := by exact prefixLift 2439260
  have htrace : WordTrace (prefixWord ++ tailWord_2439260) baseStart_2439260 baseEnd_2439260 := by
    simpa [prefixWord, tailWord_2439260, baseEnd_2439260] using wordTrace_append hprefix tailTrace_2439260
  have hstable : (prefixWord ++ tailWord_2439260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439260).length < 2 ^ (prefixWord ++ tailWord_2439260).sum := by decide
  have hdescent : baseEnd_2439260 < baseStart_2439260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439264 : List Nat := [2, 1, 1, 3, 2, 5, 2, 2, 1, 3]
def baseStart_2439264 : Nat := 118140960795 + 2439264 * 2 ^ 59
def prefixEnd_2439264 : Nat := 4983230072969 + 3 ^ 40 * 2439264 * 2
def baseEnd_2439264 : Nat := 835009916805899734721357

theorem tailTrace_2439264 : CollatzResearch.WordTrace tailWord_2439264 prefixEnd_2439264 835009916805899734721357 := by
  unfold tailWord_2439264
  simp only [CollatzResearch.WordTrace]
  refine ⟨44483633517485297984818423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59311511356647063979757897 44483633517485297984818423)
  ·
    refine ⟨66725450276227946977227635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44483633517485297984818423 66725450276227946977227635)
    ·
      refine ⟨100088175414341920465841453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66725450276227946977227635 100088175414341920465841453)
      ·
        refine ⟨37533065780378220174690545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100088175414341920465841453 37533065780378220174690545)
        ·
          refine ⟨28149799335283665131017909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37533065780378220174690545 28149799335283665131017909)
          ·
            refine ⟨2639043687682843606032929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28149799335283665131017909 2639043687682843606032929)
            ·
              refine ⟨1979282765762132704524697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639043687682843606032929 1979282765762132704524697)
              ·
                refine ⟨1484462074321599528393523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979282765762132704524697 1484462074321599528393523)
                ·
                  refine ⟨2226693111482399292590285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484462074321599528393523 2226693111482399292590285)
                  ·
                    refine ⟨835009916805899734721357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226693111482399292590285 835009916805899734721357)
                    ·
                      rfl

theorem cell22_2439264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 1, 3].length) (baseStart_2439264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439264 prefixEnd_2439264 := by exact prefixLift 2439264
  have htrace : WordTrace (prefixWord ++ tailWord_2439264) baseStart_2439264 baseEnd_2439264 := by
    simpa [prefixWord, tailWord_2439264, baseEnd_2439264] using wordTrace_append hprefix tailTrace_2439264
  have hstable : (prefixWord ++ tailWord_2439264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439264).length < 2 ^ (prefixWord ++ tailWord_2439264).sum := by decide
  have hdescent : baseEnd_2439264 < baseStart_2439264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439303 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 1, 5]
def baseStart_2439303 : Nat := 118140960795 + 2439303 * 2 ^ 59
def prefixEnd_2439303 : Nat := 4983230072969 + 3 ^ 40 * 2439303 * 2
def baseEnd_2439303 : Nat := 835023267302916632996237

theorem tailTrace_2439303 : CollatzResearch.WordTrace tailWord_2439303 prefixEnd_2439303 835023267302916632996237 := by
  unfold tailWord_2439303
  simp only [CollatzResearch.WordTrace]
  refine ⟨88968689481829305630306563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59312459654552870420204375 88968689481829305630306563)
  ·
    refine ⟨133453034222743958445459845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88968689481829305630306563 133453034222743958445459845)
    ·
      refine ⟨25022443916764492208523721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133453034222743958445459845 25022443916764492208523721)
      ·
        refine ⟨18766832937573369156392791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25022443916764492208523721 18766832937573369156392791)
        ·
          refine ⟨28150249406360053734589187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18766832937573369156392791 28150249406360053734589187)
          ·
            refine ⟨42225374109540080601883781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28150249406360053734589187 42225374109540080601883781)
            ·
              refine ⟨7917257645538765112853209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42225374109540080601883781 7917257645538765112853209)
              ·
                refine ⟨5937943234154073834639907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7917257645538765112853209 5937943234154073834639907)
                ·
                  refine ⟨8906914851231110751959861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937943234154073834639907 8906914851231110751959861)
                  ·
                    refine ⟨835023267302916632996237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8906914851231110751959861 835023267302916632996237)
                    ·
                      rfl

theorem cell22_2439303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_2439303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439303 prefixEnd_2439303 := by exact prefixLift 2439303
  have htrace : WordTrace (prefixWord ++ tailWord_2439303) baseStart_2439303 baseEnd_2439303 := by
    simpa [prefixWord, tailWord_2439303, baseEnd_2439303] using wordTrace_append hprefix tailTrace_2439303
  have hstable : (prefixWord ++ tailWord_2439303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439303).length < 2 ^ (prefixWord ++ tailWord_2439303).sum := by decide
  have hdescent : baseEnd_2439303 < baseStart_2439303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439305 : List Nat := [1, 2, 1, 1, 4, 2, 4, 3, 4]
def baseStart_2439305 : Nat := 118140960795 + 2439305 * 2 ^ 59
def prefixEnd_2439305 : Nat := 4983230072969 + 3 ^ 40 * 2439305 * 2
def baseEnd_2439305 : Nat := 278341317314596431482077

theorem tailTrace_2439305 : CollatzResearch.WordTrace tailWord_2439305 prefixEnd_2439305 278341317314596431482077 := by
  unfold tailWord_2439305
  simp only [CollatzResearch.WordTrace]
  refine ⟨88968762427822059971879369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59312508285214706647919579 88968762427822059971879369)
  ·
    refine ⟨66726571820866544978909527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88968762427822059971879369 66726571820866544978909527)
    ·
      refine ⟨100089857731299817468364291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66726571820866544978909527 100089857731299817468364291)
      ·
        refine ⟨150134786596949726202546437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100089857731299817468364291 150134786596949726202546437)
        ·
          refine ⟨28150272486928073662977457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150134786596949726202546437 28150272486928073662977457)
          ·
            refine ⟨21112704365196055247233093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28150272486928073662977457 21112704365196055247233093)
            ·
              refine ⟨3958632068474260358856205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21112704365196055247233093 3958632068474260358856205)
              ·
                refine ⟨1484487025677847634571077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3958632068474260358856205 1484487025677847634571077)
                ·
                  refine ⟨278341317314596431482077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484487025677847634571077 278341317314596431482077)
                  ·
                    rfl

theorem cell22_2439305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 4].length) (baseStart_2439305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439305 prefixEnd_2439305 := by exact prefixLift 2439305
  have htrace : WordTrace (prefixWord ++ tailWord_2439305) baseStart_2439305 baseEnd_2439305 := by
    simpa [prefixWord, tailWord_2439305, baseEnd_2439305] using wordTrace_append hprefix tailTrace_2439305
  have hstable : (prefixWord ++ tailWord_2439305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439305).length < 2 ^ (prefixWord ++ tailWord_2439305).sum := by decide
  have hdescent : baseEnd_2439305 < baseStart_2439305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439388 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2439388 : Nat := 118140960795 + 2439388 * 2 ^ 59
def prefixEnd_2439388 : Nat := 4983230072969 + 3 ^ 40 * 2439388 * 2
def baseEnd_2439388 : Nat := 835052364540004744620977

theorem tailTrace_2439388 : CollatzResearch.WordTrace tailWord_2439388 prefixEnd_2439388 835052364540004744620977 := by
  unfold tailWord_2439388
  simp only [CollatzResearch.WordTrace]
  refine ⟨44485894843260682573575409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59314526457680910098100545 44485894843260682573575409)
  ·
    refine ⟨33364421132445511930181557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44485894843260682573575409 33364421132445511930181557)
    ·
      refine ⟨3127914481166766743454521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33364421132445511930181557 3127914481166766743454521)
      ·
        refine ⟨2345935860875075057590891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3127914481166766743454521 2345935860875075057590891)
        ·
          refine ⟨3518903791312612586386337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345935860875075057590891 3518903791312612586386337)
          ·
            refine ⟨2639177843484459439789753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518903791312612586386337 2639177843484459439789753)
            ·
              refine ⟨1979383382613344579842315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639177843484459439789753 1979383382613344579842315)
              ·
                refine ⟨2969075073920016869763473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979383382613344579842315 2969075073920016869763473)
                ·
                  refine ⟨2226806305440012652322605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2969075073920016869763473 2226806305440012652322605)
                  ·
                    refine ⟨835052364540004744620977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226806305440012652322605 835052364540004744620977)
                    ·
                      rfl

theorem cell22_2439388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2439388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439388 prefixEnd_2439388 := by exact prefixLift 2439388
  have htrace : WordTrace (prefixWord ++ tailWord_2439388) baseStart_2439388 baseEnd_2439388 := by
    simpa [prefixWord, tailWord_2439388, baseEnd_2439388] using wordTrace_append hprefix tailTrace_2439388
  have hstable : (prefixWord ++ tailWord_2439388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439388).length < 2 ^ (prefixWord ++ tailWord_2439388).sum := by decide
  have hdescent : baseEnd_2439388 < baseStart_2439388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439393 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2439393 : Nat := 118140960795 + 2439393 * 2 ^ 59
def prefixEnd_2439393 : Nat := 4983230072969 + 3 ^ 40 * 2439393 * 2
def baseEnd_2439393 : Nat := 835054076142186398245961

theorem tailTrace_2439393 : CollatzResearch.WordTrace tailWord_2439393 prefixEnd_2439393 835054076142186398245961 := by
  unfold tailWord_2439393
  simp only [CollatzResearch.WordTrace]
  refine ⟨88971972051503251001082833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59314648034335500667388555 88971972051503251001082833)
  ·
    refine ⟨66728979038627438250812125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88971972051503251001082833 66728979038627438250812125)
    ·
      refine ⟨25023367139485289344054547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66728979038627438250812125 25023367139485289344054547)
      ·
        refine ⟨37535050709227934016081821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25023367139485289344054547 37535050709227934016081821)
        ·
          refine ⟨14075644015960475256030683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37535050709227934016081821 14075644015960475256030683)
          ·
            refine ⟨21113466023940712884046025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14075644015960475256030683 21113466023940712884046025)
            ·
              refine ⟨15835099517955534663034519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21113466023940712884046025 15835099517955534663034519)
              ·
                refine ⟨23752649276933301994551779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15835099517955534663034519 23752649276933301994551779)
                ·
                  refine ⟨35628973915399952991827669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23752649276933301994551779 35628973915399952991827669)
                  ·
                    refine ⟨835054076142186398245961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35628973915399952991827669 835054076142186398245961)
                    ·
                      rfl

theorem cell22_2439393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2439393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439393 prefixEnd_2439393 := by exact prefixLift 2439393
  have htrace : WordTrace (prefixWord ++ tailWord_2439393) baseStart_2439393 baseEnd_2439393 := by
    simpa [prefixWord, tailWord_2439393, baseEnd_2439393] using wordTrace_append hprefix tailTrace_2439393
  have hstable : (prefixWord ++ tailWord_2439393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439393).length < 2 ^ (prefixWord ++ tailWord_2439393).sum := by decide
  have hdescent : baseEnd_2439393 < baseStart_2439393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439455 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 1, 5]
def baseStart_2439455 : Nat := 118140960795 + 2439455 * 2 ^ 59
def prefixEnd_2439455 : Nat := 4983230072969 + 3 ^ 40 * 2439455 * 2
def baseEnd_2439455 : Nat := 835075300009238903195771

theorem tailTrace_2439455 : CollatzResearch.WordTrace tailWord_2439455 prefixEnd_2439455 835075300009238903195771 := by
  unfold tailWord_2439455
  simp only [CollatzResearch.WordTrace]
  refine ⟨88974233377278635589839819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59316155584852423726559879 88974233377278635589839819)
  ·
    refine ⟨133461350065917953384759729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88974233377278635589839819 133461350065917953384759729)
    ·
      refine ⟨100096012549438465038569797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133461350065917953384759729 100096012549438465038569797)
      ·
        refine ⟨18768002353019712194731837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100096012549438465038569797 18768002353019712194731837)
        ·
          refine ⟨7038000882382392073024439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18768002353019712194731837 7038000882382392073024439)
          ·
            refine ⟨10557001323573588109536659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038000882382392073024439 10557001323573588109536659)
            ·
              refine ⟨15835501985360382164304989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10557001323573588109536659 15835501985360382164304989)
              ·
                refine ⟨5938313244510143311614371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15835501985360382164304989 5938313244510143311614371)
                ·
                  refine ⟨8907469866765214967421557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938313244510143311614371 8907469866765214967421557)
                  ·
                    refine ⟨835075300009238903195771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8907469866765214967421557 835075300009238903195771)
                    ·
                      rfl

theorem cell22_2439455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_2439455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439455 prefixEnd_2439455 := by exact prefixLift 2439455
  have htrace : WordTrace (prefixWord ++ tailWord_2439455) baseStart_2439455 baseEnd_2439455 := by
    simpa [prefixWord, tailWord_2439455, baseEnd_2439455] using wordTrace_append hprefix tailTrace_2439455
  have hstable : (prefixWord ++ tailWord_2439455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439455).length < 2 ^ (prefixWord ++ tailWord_2439455).sum := by decide
  have hdescent : baseEnd_2439455 < baseStart_2439455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439468 : List Nat := [2, 2, 1, 1, 1, 3, 2, 10]
def baseStart_2439468 : Nat := 118140960795 + 2439468 * 2 ^ 59
def prefixEnd_2439468 : Nat := 4983230072969 + 3 ^ 40 * 2439468 * 2
def baseEnd_2439468 : Nat := 92786638908323466957859

theorem tailTrace_2439468 : CollatzResearch.WordTrace tailWord_2439468 prefixEnd_2439468 92786638908323466957859 := by
  unfold tailWord_2439468
  simp only [CollatzResearch.WordTrace]
  refine ⟨44487353763115769405031529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59316471684154359206708705 44487353763115769405031529)
  ·
    refine ⟨33365515322336827053773647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44487353763115769405031529 33365515322336827053773647)
    ·
      refine ⟨50048272983505240580660471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33365515322336827053773647 50048272983505240580660471)
      ·
        refine ⟨75072409475257860870990707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50048272983505240580660471 75072409475257860870990707)
        ·
          refine ⟨112608614212886791306486061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75072409475257860870990707 112608614212886791306486061)
          ·
            refine ⟨42228230329832546739932273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112608614212886791306486061 42228230329832546739932273)
            ·
              refine ⟨31671172747374410054949205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42228230329832546739932273 31671172747374410054949205)
              ·
                refine ⟨92786638908323466957859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31671172747374410054949205 92786638908323466957859)
                ·
                  rfl

theorem cell22_2439468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 10].length) (baseStart_2439468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439468 prefixEnd_2439468 := by exact prefixLift 2439468
  have htrace : WordTrace (prefixWord ++ tailWord_2439468) baseStart_2439468 baseEnd_2439468 := by
    simpa [prefixWord, tailWord_2439468, baseEnd_2439468] using wordTrace_append hprefix tailTrace_2439468
  have hstable : (prefixWord ++ tailWord_2439468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439468).length < 2 ^ (prefixWord ++ tailWord_2439468).sum := by decide
  have hdescent : baseEnd_2439468 < baseStart_2439468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439474 : List Nat := [3, 2, 1, 1, 5, 1, 2, 3, 4]
def baseStart_2439474 : Nat := 118140960795 + 2439474 * 2 ^ 59
def prefixEnd_2439474 : Nat := 4983230072969 + 3 ^ 40 * 2439474 * 2
def baseEnd_2439474 : Nat := 278360601365843062323571

theorem tailTrace_2439474 : CollatzResearch.WordTrace tailWord_2439474 prefixEnd_2439474 278360601365843062323571 := by
  unfold tailWord_2439474
  simp only [CollatzResearch.WordTrace]
  refine ⟨22243731591052450458695369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59316617576139867889854317 22243731591052450458695369)
  ·
    refine ⟨16682798693289337844021527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22243731591052450458695369 16682798693289337844021527)
    ·
      refine ⟨25024198039934006766032291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16682798693289337844021527 25024198039934006766032291)
      ·
        refine ⟨37536297059901010149048437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25024198039934006766032291 37536297059901010149048437)
        ·
          refine ⟨3519027849365719701473291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37536297059901010149048437 3519027849365719701473291)
          ·
            refine ⟨5278541774048579552209937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519027849365719701473291 5278541774048579552209937)
            ·
              refine ⟨3958906330536434664157453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278541774048579552209937 3958906330536434664157453)
              ·
                refine ⟨1484589873951162999059045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3958906330536434664157453 1484589873951162999059045)
                ·
                  refine ⟨278360601365843062323571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484589873951162999059045 278360601365843062323571)
                  ·
                    rfl

theorem cell22_2439474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_2439474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439474 prefixEnd_2439474 := by exact prefixLift 2439474
  have htrace : WordTrace (prefixWord ++ tailWord_2439474) baseStart_2439474 baseEnd_2439474 := by
    simpa [prefixWord, tailWord_2439474, baseEnd_2439474] using wordTrace_append hprefix tailTrace_2439474
  have hstable : (prefixWord ++ tailWord_2439474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439474).length < 2 ^ (prefixWord ++ tailWord_2439474).sum := by decide
  have hdescent : baseEnd_2439474 < baseStart_2439474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439476 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 1, 4]
def baseStart_2439476 : Nat := 118140960795 + 2439476 * 2 ^ 59
def prefixEnd_2439476 : Nat := 4983230072969 + 3 ^ 40 * 2439476 * 2
def baseEnd_2439476 : Nat := 835082488738401848420707

theorem tailTrace_2439476 : CollatzResearch.WordTrace tailWord_2439476 prefixEnd_2439476 835082488738401848420707 := by
  unfold tailWord_2439476
  simp only [CollatzResearch.WordTrace]
  refine ⟨44487499655101278088177141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59316666206801704117569521 44487499655101278088177141)
  ·
    refine ⟨4170703092665744820766607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44487499655101278088177141 4170703092665744820766607)
    ·
      refine ⟨6256054638998617231149911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4170703092665744820766607 6256054638998617231149911)
      ·
        refine ⟨9384081958497925846724867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256054638998617231149911 9384081958497925846724867)
        ·
          refine ⟨14076122937746888770087301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9384081958497925846724867 14076122937746888770087301)
          ·
            refine ⟨2639273050827541644391369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14076122937746888770087301 2639273050827541644391369)
            ·
              refine ⟨1979454788120656233293527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639273050827541644391369 1979454788120656233293527)
              ·
                refine ⟨2969182182180984349940291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979454788120656233293527 2969182182180984349940291)
                ·
                  refine ⟨4453773273271476524910437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969182182180984349940291 4453773273271476524910437)
                  ·
                    refine ⟨835082488738401848420707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453773273271476524910437 835082488738401848420707)
                    ·
                      rfl

theorem cell22_2439476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_2439476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439476 prefixEnd_2439476 := by exact prefixLift 2439476
  have htrace : WordTrace (prefixWord ++ tailWord_2439476) baseStart_2439476 baseEnd_2439476 := by
    simpa [prefixWord, tailWord_2439476, baseEnd_2439476] using wordTrace_append hprefix tailTrace_2439476
  have hstable : (prefixWord ++ tailWord_2439476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439476).length < 2 ^ (prefixWord ++ tailWord_2439476).sum := by decide
  have hdescent : baseEnd_2439476 < baseStart_2439476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439489 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2439489 : Nat := 118140960795 + 2439489 * 2 ^ 59
def prefixEnd_2439489 : Nat := 4983230072969 + 3 ^ 40 * 2439489 * 2
def baseEnd_2439489 : Nat := 835086938904074147845667

theorem tailTrace_2439489 : CollatzResearch.WordTrace tailWord_2439489 prefixEnd_2439489 835086938904074147845667 := by
  unfold tailWord_2439489
  simp only [CollatzResearch.WordTrace]
  refine ⟨88975473459155459396577521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59316982306103639597718347 88975473459155459396577521)
  ·
    refine ⟨66731605094366594547433141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88975473459155459396577521 66731605094366594547433141)
    ·
      refine ⟨6256087977596868238821857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66731605094366594547433141 6256087977596868238821857)
      ·
        refine ⟨4692065983197651179116393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6256087977596868238821857 4692065983197651179116393)
        ·
          refine ⟨3519049487398238384337295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4692065983197651179116393 3519049487398238384337295)
          ·
            refine ⟨5278574231097357576505943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519049487398238384337295 5278574231097357576505943)
            ·
              refine ⟨7917861346646036364758915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278574231097357576505943 7917861346646036364758915)
              ·
                refine ⟨11876792019969054547138373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7917861346646036364758915 11876792019969054547138373)
                ·
                  refine ⟨2226898503744197727588445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11876792019969054547138373 2226898503744197727588445)
                  ·
                    refine ⟨835086938904074147845667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2226898503744197727588445 835086938904074147845667)
                    ·
                      rfl

theorem cell22_2439489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2439489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439489 prefixEnd_2439489 := by exact prefixLift 2439489
  have htrace : WordTrace (prefixWord ++ tailWord_2439489) baseStart_2439489 baseEnd_2439489 := by
    simpa [prefixWord, tailWord_2439489, baseEnd_2439489] using wordTrace_append hprefix tailTrace_2439489
  have hstable : (prefixWord ++ tailWord_2439489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439489).length < 2 ^ (prefixWord ++ tailWord_2439489).sum := by decide
  have hdescent : baseEnd_2439489 < baseStart_2439489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439564 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 5]
def baseStart_2439564 : Nat := 118140960795 + 2439564 * 2 ^ 59
def prefixEnd_2439564 : Nat := 4983230072969 + 3 ^ 40 * 2439564 * 2
def baseEnd_2439564 : Nat := 278370870978932984073479

theorem tailTrace_2439564 : CollatzResearch.WordTrace tailWord_2439564 prefixEnd_2439564 278370870978932984073479 := by
  unfold tailWord_2439564
  simp only [CollatzResearch.WordTrace]
  refine ⟨44489104466941873602778873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59318805955922498137038497 44489104466941873602778873)
  ·
    refine ⟨33366828350206405202084155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44489104466941873602778873 33366828350206405202084155)
    ·
      refine ⟨50050242525309607803126233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33366828350206405202084155 50050242525309607803126233)
      ·
        refine ⟨37537681893982205852344675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50050242525309607803126233 37537681893982205852344675)
        ·
          refine ⟨56306522840973308778517013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37537681893982205852344675 56306522840973308778517013)
          ·
            refine ⟨2639368258170623848992985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56306522840973308778517013 2639368258170623848992985)
            ·
              refine ⟨1979526193627967886744739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639368258170623848992985 1979526193627967886744739)
              ·
                refine ⟨2969289290441951830117109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979526193627967886744739 2969289290441951830117109)
                ·
                  refine ⟨278370870978932984073479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2969289290441951830117109 278370870978932984073479)
                  ·
                    rfl

theorem cell22_2439564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 5].length) (baseStart_2439564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439564 prefixEnd_2439564 := by exact prefixLift 2439564
  have htrace : WordTrace (prefixWord ++ tailWord_2439564) baseStart_2439564 baseEnd_2439564 := by
    simpa [prefixWord, tailWord_2439564, baseEnd_2439564] using wordTrace_append hprefix tailTrace_2439564
  have hstable : (prefixWord ++ tailWord_2439564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439564).length < 2 ^ (prefixWord ++ tailWord_2439564).sum := by decide
  have hdescent : baseEnd_2439564 < baseStart_2439564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439575 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 6]
def baseStart_2439575 : Nat := 118140960795 + 2439575 * 2 ^ 59
def prefixEnd_2439575 : Nat := 4983230072969 + 3 ^ 40 * 2439575 * 2
def baseEnd_2439575 : Nat := 278372126153866196731801

theorem tailTrace_2439575 : CollatzResearch.WordTrace tailWord_2439575 prefixEnd_2439575 278372126153866196731801 := by
  unfold tailWord_2439575
  simp only [CollatzResearch.WordTrace]
  refine ⟨88978610136843896084208179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59319073424562597389472119 88978610136843896084208179)
  ·
    refine ⟨133467915205265844126312269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88978610136843896084208179 133467915205265844126312269)
    ·
      refine ⟨50050468201974691547367101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133467915205265844126312269 50050468201974691547367101)
      ·
        refine ⟨18768925575740509330262663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50050468201974691547367101 18768925575740509330262663)
        ·
          refine ⟨28153388363610763995393995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18768925575740509330262663 28153388363610763995393995)
          ·
            refine ⟨42230082545416145993090993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28153388363610763995393995 42230082545416145993090993)
            ·
              refine ⟨31672561909062109494818245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42230082545416145993090993 31672561909062109494818245)
              ·
                refine ⟨5938605357949145530278421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31672561909062109494818245 5938605357949145530278421)
                ·
                  refine ⟨278372126153866196731801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5938605357949145530278421 278372126153866196731801)
                  ·
                    rfl

theorem cell22_2439575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 6].length) (baseStart_2439575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439575 prefixEnd_2439575 := by exact prefixLift 2439575
  have htrace : WordTrace (prefixWord ++ tailWord_2439575) baseStart_2439575 baseEnd_2439575 := by
    simpa [prefixWord, tailWord_2439575, baseEnd_2439575] using wordTrace_append hprefix tailTrace_2439575
  have hstable : (prefixWord ++ tailWord_2439575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439575).length < 2 ^ (prefixWord ++ tailWord_2439575).sum := by decide
  have hdescent : baseEnd_2439575 < baseStart_2439575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439609 : List Nat := [1, 2, 1, 4, 3, 2, 1, 4, 4]
def baseStart_2439609 : Nat := 118140960795 + 2439609 * 2 ^ 59
def prefixEnd_2439609 : Nat := 4983230072969 + 3 ^ 40 * 2439609 * 2
def baseEnd_2439609 : Nat := 278376005785477944948433

theorem tailTrace_2439609 : CollatzResearch.WordTrace tailWord_2439609 prefixEnd_2439609 278376005785477944948433 := by
  unfold tailWord_2439609
  simp only [CollatzResearch.WordTrace]
  refine ⟨88979850218720719890945881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59319900145813813260630587 88979850218720719890945881)
  ·
    refine ⟨66734887664040539918209411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88979850218720719890945881 66734887664040539918209411)
    ·
      refine ⟨100102331496060809877314117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66734887664040539918209411 100102331496060809877314117)
      ·
        refine ⟨18769187155511401851996397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100102331496060809877314117 18769187155511401851996397)
        ·
          refine ⟨7038445183316775694498649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18769187155511401851996397 7038445183316775694498649)
          ·
            refine ⟨5278833887487581770873987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7038445183316775694498649 5278833887487581770873987)
            ·
              refine ⟨7918250831231372656310981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278833887487581770873987 7918250831231372656310981)
              ·
                refine ⟨1484672030855882373058309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7918250831231372656310981 1484672030855882373058309)
                ·
                  refine ⟨278376005785477944948433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484672030855882373058309 278376005785477944948433)
                  ·
                    rfl

theorem cell22_2439609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 4].length) (baseStart_2439609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439609 prefixEnd_2439609 := by exact prefixLift 2439609
  have htrace : WordTrace (prefixWord ++ tailWord_2439609) baseStart_2439609 baseEnd_2439609 := by
    simpa [prefixWord, tailWord_2439609, baseEnd_2439609] using wordTrace_append hprefix tailTrace_2439609
  have hstable : (prefixWord ++ tailWord_2439609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439609).length < 2 ^ (prefixWord ++ tailWord_2439609).sum := by decide
  have hdescent : baseEnd_2439609 < baseStart_2439609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439624 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 2, 3]
def baseStart_2439624 : Nat := 118140960795 + 2439624 * 2 ^ 59
def prefixEnd_2439624 : Nat := 4983230072969 + 3 ^ 40 * 2439624 * 2
def baseEnd_2439624 : Nat := 835133152162978795720253

theorem tailTrace_2439624 : CollatzResearch.WordTrace tailWord_2439624 prefixEnd_2439624 835133152162978795720253 := by
  unfold tailWord_2439624
  simp only [CollatzResearch.WordTrace]
  refine ⟨44490198656833188726370963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59320264875777584968494617 44490198656833188726370963)
  ·
    refine ⟨66735297985249783089556445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44490198656833188726370963 66735297985249783089556445)
    ·
      refine ⟨25025736744468668658583667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66735297985249783089556445 25025736744468668658583667)
      ·
        refine ⟨37538605116703002987875501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25025736744468668658583667 37538605116703002987875501)
        ·
          refine ⟨14076976918763626120453313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37538605116703002987875501 14076976918763626120453313)
          ·
            refine ⟨10557732689072719590339985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14076976918763626120453313 10557732689072719590339985)
            ·
              refine ⟨7918299516804539692754989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10557732689072719590339985 7918299516804539692754989)
              ·
                refine ⟨2969362318801702384783121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7918299516804539692754989 2969362318801702384783121)
                ·
                  refine ⟨2227021739101276788587341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2969362318801702384783121 2227021739101276788587341)
                  ·
                    refine ⟨835133152162978795720253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227021739101276788587341 835133152162978795720253)
                    ·
                      rfl

theorem cell22_2439624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_2439624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439624 prefixEnd_2439624 := by exact prefixLift 2439624
  have htrace : WordTrace (prefixWord ++ tailWord_2439624) baseStart_2439624 baseEnd_2439624 := by
    simpa [prefixWord, tailWord_2439624, baseEnd_2439624] using wordTrace_append hprefix tailTrace_2439624
  have hstable : (prefixWord ++ tailWord_2439624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439624).length < 2 ^ (prefixWord ++ tailWord_2439624).sum := by decide
  have hdescent : baseEnd_2439624 < baseStart_2439624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439720 : List Nat := [2, 1, 5, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2439720 : Nat := 118140960795 + 2439720 * 2 ^ 59
def prefixEnd_2439720 : Nat := 4983230072969 + 3 ^ 40 * 2439720 * 2
def baseEnd_2439720 : Nat := 835166014924866545319959

theorem tailTrace_2439720 : CollatzResearch.WordTrace tailWord_2439720 prefixEnd_2439720 835166014924866545319959 := by
  unfold tailWord_2439720
  simp only [CollatzResearch.WordTrace]
  refine ⟨44491949360659292924118307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59322599147545723898824409 44491949360659292924118307)
  ·
    refine ⟨66737924040988939386177461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44491949360659292924118307 66737924040988939386177461)
    ·
      refine ⟨6256680378842713067454137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66737924040988939386177461 6256680378842713067454137)
      ·
        refine ⟨4692510284132034800590603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6256680378842713067454137 4692510284132034800590603)
        ·
          refine ⟨7038765426198052200885905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692510284132034800590603 7038765426198052200885905)
          ·
            refine ⟨5279074069648539150664429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7038765426198052200885905 5279074069648539150664429)
            ·
              refine ⟨1979652776118202181499161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5279074069648539150664429 1979652776118202181499161)
              ·
                refine ⟨1484739582088651636124371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979652776118202181499161 1484739582088651636124371)
                ·
                  refine ⟨2227109373132977454186557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1484739582088651636124371 2227109373132977454186557)
                  ·
                    refine ⟨835166014924866545319959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227109373132977454186557 835166014924866545319959)
                    ·
                      rfl

theorem cell22_2439720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2439720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439720 prefixEnd_2439720 := by exact prefixLift 2439720
  have htrace : WordTrace (prefixWord ++ tailWord_2439720) baseStart_2439720 baseEnd_2439720 := by
    simpa [prefixWord, tailWord_2439720, baseEnd_2439720] using wordTrace_append hprefix tailTrace_2439720
  have hstable : (prefixWord ++ tailWord_2439720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439720).length < 2 ^ (prefixWord ++ tailWord_2439720).sum := by decide
  have hdescent : baseEnd_2439720 < baseStart_2439720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439772 : List Nat := [2, 2, 4, 1, 13]
def baseStart_2439772 : Nat := 118140960795 + 2439772 * 2 ^ 59
def prefixEnd_2439772 : Nat := 4983230072969 + 3 ^ 40 * 2439772 * 2
def baseEnd_2439772 : Nat := 3436970434516690300493

theorem tailTrace_2439772 : CollatzResearch.WordTrace tailWord_2439772 prefixEnd_2439772 3436970434516690300493 := by
  unfold tailWord_2439772
  simp only [CollatzResearch.WordTrace]
  refine ⟨44492897658565099364564785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59323863544753465819419713 44492897658565099364564785)
  ·
    refine ⟨33369673243923824523423589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44492897658565099364564785 33369673243923824523423589)
    ·
      refine ⟨6256813733235717098141923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33369673243923824523423589 6256813733235717098141923)
      ·
        refine ⟨9385220599853575647212885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256813733235717098141923 9385220599853575647212885)
        ·
          refine ⟨3436970434516690300493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9385220599853575647212885 3436970434516690300493)
          ·
            rfl

theorem cell22_2439772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 13].length) (baseStart_2439772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439772 prefixEnd_2439772 := by exact prefixLift 2439772
  have htrace : WordTrace (prefixWord ++ tailWord_2439772) baseStart_2439772 baseEnd_2439772 := by
    simpa [prefixWord, tailWord_2439772, baseEnd_2439772] using wordTrace_append hprefix tailTrace_2439772
  have hstable : (prefixWord ++ tailWord_2439772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439772).length < 2 ^ (prefixWord ++ tailWord_2439772).sum := by decide
  have hdescent : baseEnd_2439772 < baseStart_2439772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439789 : List Nat := [1, 5, 1, 1, 3, 1, 3, 7]
def baseStart_2439789 : Nat := 118140960795 + 2439789 * 2 ^ 59
def prefixEnd_2439789 : Nat := 4983230072969 + 3 ^ 40 * 2439789 * 2
def baseEnd_2439789 : Nat := 92798848337219262816083

theorem tailTrace_2439789 : CollatzResearch.WordTrace tailWord_2439789 prefixEnd_2439789 92798848337219262816083 := by
  unfold tailWord_2439789
  simp only [CollatzResearch.WordTrace]
  refine ⟨88986415358068610632498421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59324276905379073754998947 88986415358068610632498421)
  ·
    refine ⟨8342476439818932246796727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88986415358068610632498421 8342476439818932246796727)
    ·
      refine ⟨12513714659728398370195091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8342476439818932246796727 12513714659728398370195091)
      ·
        refine ⟨18770571989592597555292637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513714659728398370195091 18770571989592597555292637)
        ·
          refine ⟨7038964496097224083234739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18770571989592597555292637 7038964496097224083234739)
          ·
            refine ⟨10558446744145836124852109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038964496097224083234739 10558446744145836124852109)
            ·
              refine ⟨3959417529054688546819541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10558446744145836124852109 3959417529054688546819541)
              ·
                refine ⟨92798848337219262816083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3959417529054688546819541 92798848337219262816083)
                ·
                  rfl

theorem cell22_2439789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 7].length) (baseStart_2439789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439789 prefixEnd_2439789 := by exact prefixLift 2439789
  have htrace : WordTrace (prefixWord ++ tailWord_2439789) baseStart_2439789 baseEnd_2439789 := by
    simpa [prefixWord, tailWord_2439789, baseEnd_2439789] using wordTrace_append hprefix tailTrace_2439789
  have hstable : (prefixWord ++ tailWord_2439789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439789).length < 2 ^ (prefixWord ++ tailWord_2439789).sum := by decide
  have hdescent : baseEnd_2439789 < baseStart_2439789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439804 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 5, 3]
def baseStart_2439804 : Nat := 118140960795 + 2439804 * 2 ^ 59
def prefixEnd_2439804 : Nat := 4983230072969 + 3 ^ 40 * 2439804 * 2
def baseEnd_2439804 : Nat := 835194769841518326219701

theorem tailTrace_2439804 : CollatzResearch.WordTrace tailWord_2439804 prefixEnd_2439804 835194769841518326219701 := by
  unfold tailWord_2439804
  simp only [CollatzResearch.WordTrace]
  refine ⟨44493481226507134097147233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59324641635342845462862977 44493481226507134097147233)
  ·
    refine ⟨33370110919880350572860425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44493481226507134097147233 33370110919880350572860425)
    ·
      refine ⟨25027583189910262929645319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33370110919880350572860425 25027583189910262929645319)
      ·
        refine ⟨37541374784865394394467979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25027583189910262929645319 37541374784865394394467979)
        ·
          refine ⟨56312062177298091591701969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37541374784865394394467979 56312062177298091591701969)
          ·
            refine ⟨42234046632973568693776477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56312062177298091591701969 42234046632973568693776477)
            ·
              refine ⟨15837767487365088260166179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42234046632973568693776477 15837767487365088260166179)
              ·
                refine ⟨23756651231047632390249269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15837767487365088260166179 23756651231047632390249269)
                ·
                  refine ⟨2227186052910715536585869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23756651231047632390249269 2227186052910715536585869)
                  ·
                    refine ⟨835194769841518326219701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227186052910715536585869 835194769841518326219701)
                    ·
                      rfl

theorem cell22_2439804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_2439804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439804 prefixEnd_2439804 := by exact prefixLift 2439804
  have htrace : WordTrace (prefixWord ++ tailWord_2439804) baseStart_2439804 baseEnd_2439804 := by
    simpa [prefixWord, tailWord_2439804, baseEnd_2439804] using wordTrace_append hprefix tailTrace_2439804
  have hstable : (prefixWord ++ tailWord_2439804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439804).length < 2 ^ (prefixWord ++ tailWord_2439804).sum := by decide
  have hdescent : baseEnd_2439804 < baseStart_2439804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439817 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 7]
def baseStart_2439817 : Nat := 118140960795 + 2439817 * 2 ^ 59
def prefixEnd_2439817 : Nat := 4983230072969 + 3 ^ 40 * 2439817 * 2
def baseEnd_2439817 : Nat := 278399740002396875214887

theorem tailTrace_2439817 : CollatzResearch.WordTrace tailWord_2439817 prefixEnd_2439817 278399740002396875214887 := by
  unfold tailWord_2439817
  simp only [CollatzResearch.WordTrace]
  refine ⟨88987436601967171414517705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59324957734644780943011803 88987436601967171414517705)
  ·
    refine ⟨66740577451475378560888279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88987436601967171414517705 66740577451475378560888279)
    ·
      refine ⟨100110866177213067841332419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66740577451475378560888279 100110866177213067841332419)
      ·
        refine ⟨150166299265819601761998629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100110866177213067841332419 150166299265819601761998629)
        ·
          refine ⟨28156181112341175330374743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150166299265819601761998629 28156181112341175330374743)
          ·
            refine ⟨42234271668511762995562115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28156181112341175330374743 42234271668511762995562115)
            ·
              refine ⟨63351407502767644493343173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42234271668511762995562115 63351407502767644493343173)
              ·
                refine ⟨11878388906768933342501845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63351407502767644493343173 11878388906768933342501845)
                ·
                  refine ⟨278399740002396875214887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11878388906768933342501845 278399740002396875214887)
                  ·
                    rfl

theorem cell22_2439817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_2439817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439817 prefixEnd_2439817 := by exact prefixLift 2439817
  have htrace : WordTrace (prefixWord ++ tailWord_2439817) baseStart_2439817 baseEnd_2439817 := by
    simpa [prefixWord, tailWord_2439817, baseEnd_2439817] using wordTrace_append hprefix tailTrace_2439817
  have hstable : (prefixWord ++ tailWord_2439817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439817).length < 2 ^ (prefixWord ++ tailWord_2439817).sum := by decide
  have hdescent : baseEnd_2439817 < baseStart_2439817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439838 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_2439838 : Nat := 118140960795 + 2439838 * 2 ^ 59
def prefixEnd_2439838 : Nat := 4983230072969 + 3 ^ 40 * 2439838 * 2
def baseEnd_2439838 : Nat := 835206408736353570869597

theorem tailTrace_2439838 : CollatzResearch.WordTrace tailWord_2439838 prefixEnd_2439838 835206408736353570869597 := by
  unfold tailWord_2439838
  simp only [CollatzResearch.WordTrace]
  refine ⟨11123525316861386500129021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59325468356594061334021445 11123525316861386500129021)
  ·
    refine ⟨4171321993823019937548383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11123525316861386500129021 4171321993823019937548383)
    ·
      refine ⟨6256982990734529906322575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4171321993823019937548383 6256982990734529906322575)
      ·
        refine ⟨9385474486101794859483863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256982990734529906322575 9385474486101794859483863)
        ·
          refine ⟨14078211729152692289225795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9385474486101794859483863 14078211729152692289225795)
          ·
            refine ⟨21117317593729038433838693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14078211729152692289225795 21117317593729038433838693)
            ·
              refine ⟨3959497048824194706344755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21117317593729038433838693 3959497048824194706344755)
              ·
                refine ⟨5939245573236292059517133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959497048824194706344755 5939245573236292059517133)
                ·
                  refine ⟨2227217089963609522318925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5939245573236292059517133 2227217089963609522318925)
                  ·
                    refine ⟨835206408736353570869597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227217089963609522318925 835206408736353570869597)
                    ·
                      rfl

theorem cell22_2439838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_2439838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439838 prefixEnd_2439838 := by exact prefixLift 2439838
  have htrace : WordTrace (prefixWord ++ tailWord_2439838) baseStart_2439838 baseEnd_2439838 := by
    simpa [prefixWord, tailWord_2439838, baseEnd_2439838] using wordTrace_append hprefix tailTrace_2439838
  have hstable : (prefixWord ++ tailWord_2439838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439838).length < 2 ^ (prefixWord ++ tailWord_2439838).sum := by decide
  have hdescent : baseEnd_2439838 < baseStart_2439838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2439896 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 6]
def baseStart_2439896 : Nat := 118140960795 + 2439896 * 2 ^ 59
def prefixEnd_2439896 : Nat := 4983230072969 + 3 ^ 40 * 2439896 * 2
def baseEnd_2439896 : Nat := 278408754440553584306473

theorem tailTrace_2439896 : CollatzResearch.WordTrace tailWord_2439896 prefixEnd_2439896 278408754440553584306473 := by
  unfold tailWord_2439896
  simp only [CollatzResearch.WordTrace]
  refine ⟨44495158984340483953321771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59326878645787311937762361 44495158984340483953321771)
  ·
    refine ⟨66742738476510725929982657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44495158984340483953321771 66742738476510725929982657)
    ·
      refine ⟨50057053857383044447486993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66742738476510725929982657 50057053857383044447486993)
      ·
        refine ⟨37542790393037283335615245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50057053857383044447486993 37542790393037283335615245)
        ·
          refine ⟨14078546397388981250855717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37542790393037283335615245 14078546397388981250855717)
          ·
            refine ⟨2639727449510433984535447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14078546397388981250855717 2639727449510433984535447)
            ·
              refine ⟨3959591174265650976803171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639727449510433984535447 3959591174265650976803171)
              ·
                refine ⟨5939386761398476465204757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959591174265650976803171 5939386761398476465204757)
                ·
                  refine ⟨278408754440553584306473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5939386761398476465204757 278408754440553584306473)
                  ·
                    rfl

theorem cell22_2439896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 6].length) (baseStart_2439896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2439896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2439896 prefixEnd_2439896 := by exact prefixLift 2439896
  have htrace : WordTrace (prefixWord ++ tailWord_2439896) baseStart_2439896 baseEnd_2439896 := by
    simpa [prefixWord, tailWord_2439896, baseEnd_2439896] using wordTrace_append hprefix tailTrace_2439896
  have hstable : (prefixWord ++ tailWord_2439896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2439896).length < 2 ^ (prefixWord ++ tailWord_2439896).sum := by decide
  have hdescent : baseEnd_2439896 < baseStart_2439896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2439896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440020 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 5]
def baseStart_2440020 : Nat := 118140960795 + 2440020 * 2 ^ 59
def prefixEnd_2440020 : Nat := 4983230072969 + 3 ^ 40 * 2440020 * 2
def baseEnd_2440020 : Nat := 278422903685255254273013

theorem tailTrace_2440020 : CollatzResearch.WordTrace tailWord_2440020 prefixEnd_2440020 278422903685255254273013 := by
  unfold tailWord_2440020
  simp only [CollatzResearch.WordTrace]
  refine ⟨44497420310115868542078757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59329893746821158056105009 44497420310115868542078757)
  ·
    refine ⟨8343266308146725351639767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44497420310115868542078757 8343266308146725351639767)
    ·
      refine ⟨12514899462220088027459651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8343266308146725351639767 12514899462220088027459651)
      ·
        refine ⟨18772349193330132041189477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12514899462220088027459651 18772349193330132041189477)
        ·
          refine ⟨3519815473749399757723027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18772349193330132041189477 3519815473749399757723027)
          ·
            refine ⟨5279723210624099636584541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519815473749399757723027 5279723210624099636584541)
            ·
              refine ⟨1979896203984037363719203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5279723210624099636584541 1979896203984037363719203)
              ·
                refine ⟨2969844305976056045578805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979896203984037363719203 2969844305976056045578805)
                ·
                  refine ⟨278422903685255254273013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2969844305976056045578805 278422903685255254273013)
                  ·
                    rfl

theorem cell22_2440020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_2440020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440020 prefixEnd_2440020 := by exact prefixLift 2440020
  have htrace : WordTrace (prefixWord ++ tailWord_2440020) baseStart_2440020 baseEnd_2440020 := by
    simpa [prefixWord, tailWord_2440020, baseEnd_2440020] using wordTrace_append hprefix tailTrace_2440020
  have hstable : (prefixWord ++ tailWord_2440020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440020).length < 2 ^ (prefixWord ++ tailWord_2440020).sum := by decide
  have hdescent : baseEnd_2440020 < baseStart_2440020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440048 : List Nat := [2, 1, 1, 1, 4, 1, 5, 3, 4]
def baseStart_2440048 : Nat := 118140960795 + 2440048 * 2 ^ 59
def prefixEnd_2440048 : Nat := 4983230072969 + 3 ^ 40 * 2440048 * 2
def baseEnd_2440048 : Nat := 278426098675994341039651

theorem tailTrace_2440048 : CollatzResearch.WordTrace tailWord_2440048 prefixEnd_2440048 278426098675994341039651 := by
  unfold tailWord_2440048
  simp only [CollatzResearch.WordTrace]
  refine ⟨44497930932065148933088399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59330574576086865244117865 44497930932065148933088399)
  ·
    refine ⟨66746896398097723399632599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44497930932065148933088399 66746896398097723399632599)
    ·
      refine ⟨100120344597146585099448899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66746896398097723399632599 100120344597146585099448899)
      ·
        refine ⟨150180516895719877649173349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100120344597146585099448899 150180516895719877649173349)
        ·
          refine ⟨28158846917947477059220003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150180516895719877649173349 28158846917947477059220003)
          ·
            refine ⟨42238270376921215588830005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28158846917947477059220003 42238270376921215588830005)
            ·
              refine ⟨3959837847836363961452813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42238270376921215588830005 3959837847836363961452813)
              ·
                refine ⟨1484939192938636485544805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3959837847836363961452813 1484939192938636485544805)
                ·
                  refine ⟨278426098675994341039651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484939192938636485544805 278426098675994341039651)
                  ·
                    rfl

theorem cell22_2440048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_2440048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440048 prefixEnd_2440048 := by exact prefixLift 2440048
  have htrace : WordTrace (prefixWord ++ tailWord_2440048) baseStart_2440048 baseEnd_2440048 := by
    simpa [prefixWord, tailWord_2440048, baseEnd_2440048] using wordTrace_append hprefix tailTrace_2440048
  have hstable : (prefixWord ++ tailWord_2440048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440048).length < 2 ^ (prefixWord ++ tailWord_2440048).sum := by decide
  have hdescent : baseEnd_2440048 < baseStart_2440048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440059 : List Nat := [1, 1, 1, 1, 1, 5, 12]
def baseStart_2440059 : Nat := 118140960795 + 2440059 * 2 ^ 59
def prefixEnd_2440059 : Nat := 4983230072969 + 3 ^ 40 * 2440059 * 2
def baseEnd_2440059 : Nat := 30936372650103061521997

theorem tailTrace_2440059 : CollatzResearch.WordTrace tailWord_2440059 prefixEnd_2440059 30936372650103061521997 := by
  unfold tailWord_2440059
  simp only [CollatzResearch.WordTrace]
  refine ⟨88996263067090446744827231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59330842044726964496551487 88996263067090446744827231)
  ·
    refine ⟨133494394600635670117240847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88996263067090446744827231 133494394600635670117240847)
    ·
      refine ⟨200241591900953505175861271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133494394600635670117240847 200241591900953505175861271)
      ·
        refine ⟨300362387851430257763791907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200241591900953505175861271 300362387851430257763791907)
        ·
          refine ⟨450543581777145386645687861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300362387851430257763791907 450543581777145386645687861)
          ·
            refine ⟨42238460791607379998033237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 450543581777145386645687861 42238460791607379998033237)
            ·
              refine ⟨30936372650103061521997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 42238460791607379998033237 30936372650103061521997)
              ·
                rfl

theorem cell22_2440059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 12].length) (baseStart_2440059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440059 prefixEnd_2440059 := by exact prefixLift 2440059
  have htrace : WordTrace (prefixWord ++ tailWord_2440059) baseStart_2440059 baseEnd_2440059 := by
    simpa [prefixWord, tailWord_2440059, baseEnd_2440059] using wordTrace_append hprefix tailTrace_2440059
  have hstable : (prefixWord ++ tailWord_2440059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440059).length < 2 ^ (prefixWord ++ tailWord_2440059).sum := by decide
  have hdescent : baseEnd_2440059 < baseStart_2440059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440061 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_2440061 : Nat := 118140960795 + 2440061 * 2 ^ 59
def prefixEnd_2440061 : Nat := 4983230072969 + 3 ^ 40 * 2440061 * 2
def baseEnd_2440061 : Nat := 835282746193655322543913

theorem tailTrace_2440061 : CollatzResearch.WordTrace tailWord_2440061 prefixEnd_2440061 835282746193655322543913 := by
  unfold tailWord_2440061
  simp only [CollatzResearch.WordTrace]
  refine ⟨88996336013083201086400037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59330890675388800724266691 88996336013083201086400037)
  ·
    refine ⟨16686813002453100203700007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88996336013083201086400037 16686813002453100203700007)
    ·
      refine ⟨25030219503679650305550011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16686813002453100203700007 25030219503679650305550011)
      ·
        refine ⟨37545329255519475458325017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25030219503679650305550011 37545329255519475458325017)
        ·
          refine ⟨28158996941639606593743763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37545329255519475458325017 28158996941639606593743763)
          ·
            refine ⟨42238495412459409890615645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28158996941639606593743763 42238495412459409890615645)
            ·
              refine ⟨15839435779672278708980867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42238495412459409890615645 15839435779672278708980867)
              ·
                refine ⟨23759153669508418063471301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15839435779672278708980867 23759153669508418063471301)
                ·
                  refine ⟨4454841313032828386900869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23759153669508418063471301 4454841313032828386900869)
                  ·
                    refine ⟨835282746193655322543913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4454841313032828386900869 835282746193655322543913)
                    ·
                      rfl

theorem cell22_2440061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_2440061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440061 prefixEnd_2440061 := by exact prefixLift 2440061
  have htrace : WordTrace (prefixWord ++ tailWord_2440061) baseStart_2440061 baseEnd_2440061 := by
    simpa [prefixWord, tailWord_2440061, baseEnd_2440061] using wordTrace_append hprefix tailTrace_2440061
  have hstable : (prefixWord ++ tailWord_2440061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440061).length < 2 ^ (prefixWord ++ tailWord_2440061).sum := by decide
  have hdescent : baseEnd_2440061 < baseStart_2440061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440210 : List Nat := [3, 2, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2440210 : Nat := 118140960795 + 2440210 * 2 ^ 59
def prefixEnd_2440210 : Nat := 4983230072969 + 3 ^ 40 * 2440210 * 2
def baseEnd_2440210 : Nat := 835333751938668600568457

theorem tailTrace_2440210 : CollatzResearch.WordTrace tailWord_2440210 prefixEnd_2440210 835333751938668600568457 := by
  unfold tailWord_2440210
  simp only [CollatzResearch.WordTrace]
  refine ⟨22250442622385849883393521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59334513659695599689049389 22250442622385849883393521)
  ·
    refine ⟨16687831966789387412545141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22250442622385849883393521 16687831966789387412545141)
    ·
      refine ⟨1564484246886505069926107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16687831966789387412545141 1564484246886505069926107)
      ·
        refine ⟨2346726370329757604889161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564484246886505069926107 2346726370329757604889161)
        ·
          refine ⟨1760044777747318203666871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2346726370329757604889161 1760044777747318203666871)
          ·
            refine ⟨2640067166620977305500307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760044777747318203666871 2640067166620977305500307)
            ·
              refine ⟨3960100749931465958250461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640067166620977305500307 3960100749931465958250461)
              ·
                refine ⟨1485037781224299734343923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3960100749931465958250461 1485037781224299734343923)
                ·
                  refine ⟨2227556671836449601515885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485037781224299734343923 2227556671836449601515885)
                  ·
                    refine ⟨835333751938668600568457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227556671836449601515885 835333751938668600568457)
                    ·
                      rfl

theorem cell22_2440210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2440210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440210 prefixEnd_2440210 := by exact prefixLift 2440210
  have htrace : WordTrace (prefixWord ++ tailWord_2440210) baseStart_2440210 baseEnd_2440210 := by
    simpa [prefixWord, tailWord_2440210, baseEnd_2440210] using wordTrace_append hprefix tailTrace_2440210
  have hstable : (prefixWord ++ tailWord_2440210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440210).length < 2 ^ (prefixWord ++ tailWord_2440210).sum := by decide
  have hdescent : baseEnd_2440210 < baseStart_2440210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440213 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2440213 : Nat := 118140960795 + 2440213 * 2 ^ 59
def prefixEnd_2440213 : Nat := 4983230072969 + 3 ^ 40 * 2440213 * 2
def baseEnd_2440213 : Nat := 835334778899977592743447

theorem tailTrace_2440213 : CollatzResearch.WordTrace tailWord_2440213 prefixEnd_2440213 835334778899977592743447 := by
  unfold tailWord_2440213
  simp only [CollatzResearch.WordTrace]
  refine ⟨89001879908532531045933293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59334586605688354030622195 89001879908532531045933293)
  ·
    refine ⟨33375704965699699142224985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89001879908532531045933293 33375704965699699142224985)
    ·
      refine ⟨25031778724274774356668739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33375704965699699142224985 25031778724274774356668739)
      ·
        refine ⟨37547668086412161535003109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25031778724274774356668739 37547668086412161535003109)
        ·
          refine ⟨7040187766202280287813083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37547668086412161535003109 7040187766202280287813083)
          ·
            refine ⟨10560281649303420431719625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7040187766202280287813083 10560281649303420431719625)
            ·
              refine ⟨7920211236977565323789719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10560281649303420431719625 7920211236977565323789719)
              ·
                refine ⟨11880316855466347985684579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7920211236977565323789719 11880316855466347985684579)
                ·
                  refine ⟨17820475283199521978526869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11880316855466347985684579 17820475283199521978526869)
                  ·
                    refine ⟨835334778899977592743447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17820475283199521978526869 835334778899977592743447)
                    ·
                      rfl

theorem cell22_2440213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2440213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440213 prefixEnd_2440213 := by exact prefixLift 2440213
  have htrace : WordTrace (prefixWord ++ tailWord_2440213) baseStart_2440213 baseEnd_2440213 := by
    simpa [prefixWord, tailWord_2440213, baseEnd_2440213] using wordTrace_append hprefix tailTrace_2440213
  have hstable : (prefixWord ++ tailWord_2440213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440213).length < 2 ^ (prefixWord ++ tailWord_2440213).sum := by decide
  have hdescent : baseEnd_2440213 < baseStart_2440213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440215 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 4, 3]
def baseStart_2440215 : Nat := 118140960795 + 2440215 * 2 ^ 59
def prefixEnd_2440215 : Nat := 4983230072969 + 3 ^ 40 * 2440215 * 2
def baseEnd_2440215 : Nat := 835335463540850254193441

theorem tailTrace_2440215 : CollatzResearch.WordTrace tailWord_2440215 prefixEnd_2440215 835335463540850254193441 := by
  unfold tailWord_2440215
  simp only [CollatzResearch.WordTrace]
  refine ⟨89001952854525285387506099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59334635236350190258337399 89001952854525285387506099)
  ·
    refine ⟨133502929281787928081259149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89001952854525285387506099 133502929281787928081259149)
    ·
      refine ⟨50063598480670473030472181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133502929281787928081259149 50063598480670473030472181)
      ·
        refine ⟨4693462357562856846606767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50063598480670473030472181 4693462357562856846606767)
        ·
          refine ⟨7040193536344285269910151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693462357562856846606767 7040193536344285269910151)
          ·
            refine ⟨10560290304516427904865227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7040193536344285269910151 10560290304516427904865227)
            ·
              refine ⟨15840435456774641857297841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10560290304516427904865227 15840435456774641857297841)
              ·
                refine ⟨11880326592580981392973381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15840435456774641857297841 11880326592580981392973381)
                ·
                  refine ⟨2227561236108934011182509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11880326592580981392973381 2227561236108934011182509)
                  ·
                    refine ⟨835335463540850254193441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227561236108934011182509 835335463540850254193441)
                    ·
                      rfl

theorem cell22_2440215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_2440215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440215 prefixEnd_2440215 := by exact prefixLift 2440215
  have htrace : WordTrace (prefixWord ++ tailWord_2440215) baseStart_2440215 baseEnd_2440215 := by
    simpa [prefixWord, tailWord_2440215, baseEnd_2440215] using wordTrace_append hprefix tailTrace_2440215
  have hstable : (prefixWord ++ tailWord_2440215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440215).length < 2 ^ (prefixWord ++ tailWord_2440215).sum := by decide
  have hdescent : baseEnd_2440215 < baseStart_2440215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440228 : List Nat := [2, 3, 1, 4, 1, 1, 10]
def baseStart_2440228 : Nat := 118140960795 + 2440228 * 2 ^ 59
def prefixEnd_2440228 : Nat := 4983230072969 + 3 ^ 40 * 2440228 * 2
def baseEnd_2440228 : Nat := 30938515322463798282163

theorem tailTrace_2440228 : CollatzResearch.WordTrace tailWord_2440228 prefixEnd_2440228 30938515322463798282163 := by
  unfold tailWord_2440228
  simp only [CollatzResearch.WordTrace]
  refine ⟨44501213501739094303864669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59334951335652125738486225 44501213501739094303864669)
  ·
    refine ⟨16687955063152160363949251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44501213501739094303864669 16687955063152160363949251)
    ·
      refine ⟨25031932594728240545923877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16687955063152160363949251 25031932594728240545923877)
      ·
        refine ⟨4693487361511545102360727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25031932594728240545923877 4693487361511545102360727)
        ·
          refine ⟨7040231042267317653541091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693487361511545102360727 7040231042267317653541091)
          ·
            refine ⟨10560346563400976480311637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7040231042267317653541091 10560346563400976480311637)
            ·
              refine ⟨30938515322463798282163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10560346563400976480311637 30938515322463798282163)
              ·
                rfl

theorem cell22_2440228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 10].length) (baseStart_2440228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440228 prefixEnd_2440228 := by exact prefixLift 2440228
  have htrace : WordTrace (prefixWord ++ tailWord_2440228) baseStart_2440228 baseEnd_2440228 := by
    simpa [prefixWord, tailWord_2440228, baseEnd_2440228] using wordTrace_append hprefix tailTrace_2440228
  have hstable : (prefixWord ++ tailWord_2440228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440228).length < 2 ^ (prefixWord ++ tailWord_2440228).sum := by decide
  have hdescent : baseEnd_2440228 < baseStart_2440228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440234 : List Nat := [3, 1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_2440234 : Nat := 118140960795 + 2440234 * 2 ^ 59
def prefixEnd_2440234 : Nat := 4983230072969 + 3 ^ 40 * 2440234 * 2
def baseEnd_2440234 : Nat := 278447322543046845989461

theorem tailTrace_2440234 : CollatzResearch.WordTrace tailWord_2440234 prefixEnd_2440234 278447322543046845989461 := by
  unfold tailWord_2440234
  simp only [CollatzResearch.WordTrace]
  refine ⟨22250661460364112908111939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59335097227637634421631837 22250661460364112908111939)
  ·
    refine ⟨33375992190546169362167909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22250661460364112908111939 33375992190546169362167909)
    ·
      refine ⟨6257998535727406755406483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33375992190546169362167909 6257998535727406755406483)
      ·
        refine ⟨9386997803591110133109725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6257998535727406755406483 9386997803591110133109725)
        ·
          refine ⟨3520124176346666299916147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9386997803591110133109725 3520124176346666299916147)
          ·
            refine ⟨5280186264519999449874221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520124176346666299916147 5280186264519999449874221)
            ·
              refine ⟨1980069849194999793702833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5280186264519999449874221 1980069849194999793702833)
              ·
                refine ⟨1485052386896249845277125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980069849194999793702833 1485052386896249845277125)
                ·
                  refine ⟨278447322543046845989461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1485052386896249845277125 278447322543046845989461)
                  ·
                    rfl

theorem cell22_2440234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_2440234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440234 prefixEnd_2440234 := by exact prefixLift 2440234
  have htrace : WordTrace (prefixWord ++ tailWord_2440234) baseStart_2440234 baseEnd_2440234 := by
    simpa [prefixWord, tailWord_2440234, baseEnd_2440234] using wordTrace_append hprefix tailTrace_2440234
  have hstable : (prefixWord ++ tailWord_2440234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440234).length < 2 ^ (prefixWord ++ tailWord_2440234).sum := by decide
  have hdescent : baseEnd_2440234 < baseStart_2440234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440249 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 2, 3]
def baseStart_2440249 : Nat := 118140960795 + 2440249 * 2 ^ 59
def prefixEnd_2440249 : Nat := 4983230072969 + 3 ^ 40 * 2440249 * 2
def baseEnd_2440249 : Nat := 835347102435685498843337

theorem tailTrace_2440249 : CollatzResearch.WordTrace tailWord_2440249 prefixEnd_2440249 835347102435685498843337 := by
  unfold tailWord_2440249
  simp only [CollatzResearch.WordTrace]
  refine ⟨89003192936402109194243801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59335461957601406129495867 89003192936402109194243801)
  ·
    refine ⟨66752394702301581895682851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89003192936402109194243801 66752394702301581895682851)
    ·
      refine ⟨100128592053452372843524277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66752394702301581895682851 100128592053452372843524277)
      ·
        refine ⟨9387055505011159954080401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100128592053452372843524277 9387055505011159954080401)
        ·
          refine ⟨7040291628758369965560301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9387055505011159954080401 7040291628758369965560301)
          ·
            refine ⟨2640109360784388737085113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7040291628758369965560301 2640109360784388737085113)
            ·
              refine ⟨1980082020588291552813835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2640109360784388737085113 1980082020588291552813835)
              ·
                refine ⟨2970123030882437329220753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980082020588291552813835 2970123030882437329220753)
                ·
                  refine ⟨2227592273161827996915565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2970123030882437329220753 2227592273161827996915565)
                  ·
                    refine ⟨835347102435685498843337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227592273161827996915565 835347102435685498843337)
                    ·
                      rfl

theorem cell22_2440249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_2440249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440249 prefixEnd_2440249 := by exact prefixLift 2440249
  have htrace : WordTrace (prefixWord ++ tailWord_2440249) baseStart_2440249 baseEnd_2440249 := by
    simpa [prefixWord, tailWord_2440249, baseEnd_2440249] using wordTrace_append hprefix tailTrace_2440249
  have hstable : (prefixWord ++ tailWord_2440249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440249).length < 2 ^ (prefixWord ++ tailWord_2440249).sum := by decide
  have hdescent : baseEnd_2440249 < baseStart_2440249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440277 : List Nat := [1, 3, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_2440277 : Nat := 118140960795 + 2440277 * 2 ^ 59
def prefixEnd_2440277 : Nat := 4983230072969 + 3 ^ 40 * 2440277 * 2
def baseEnd_2440277 : Nat := 835356687407902759143251

theorem tailTrace_2440277 : CollatzResearch.WordTrace tailWord_2440277 prefixEnd_2440277 835356687407902759143251 := by
  unfold tailWord_2440277
  simp only [CollatzResearch.WordTrace]
  refine ⟨89004214180300669976263085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59336142786867113317508723 89004214180300669976263085)
  ·
    refine ⟨33376580317612751241098657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89004214180300669976263085 33376580317612751241098657)
    ·
      refine ⟨25032435238209563430823993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33376580317612751241098657 25032435238209563430823993)
      ·
        refine ⟨18774326428657172573117995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25032435238209563430823993 18774326428657172573117995)
        ·
          refine ⟨28161489642985758859676993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18774326428657172573117995 28161489642985758859676993)
          ·
            refine ⟨21121117232239319144757745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28161489642985758859676993 21121117232239319144757745)
            ·
              refine ⟨15840837924179489358568309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21121117232239319144757745 15840837924179489358568309)
              ·
                refine ⟨1485078555391827127365779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15840837924179489358568309 1485078555391827127365779)
                ·
                  refine ⟨2227617833087740691048669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485078555391827127365779 2227617833087740691048669)
                  ·
                    refine ⟨835356687407902759143251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227617833087740691048669 835356687407902759143251)
                    ·
                      rfl

theorem cell22_2440277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_2440277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440277 prefixEnd_2440277 := by exact prefixLift 2440277
  have htrace : WordTrace (prefixWord ++ tailWord_2440277) baseStart_2440277 baseEnd_2440277 := by
    simpa [prefixWord, tailWord_2440277, baseEnd_2440277] using wordTrace_append hprefix tailTrace_2440277
  have hstable : (prefixWord ++ tailWord_2440277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440277).length < 2 ^ (prefixWord ++ tailWord_2440277).sum := by decide
  have hdescent : baseEnd_2440277 < baseStart_2440277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440288 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 2, 5]
def baseStart_2440288 : Nat := 118140960795 + 2440288 * 2 ^ 59
def prefixEnd_2440288 : Nat := 4983230072969 + 3 ^ 40 * 2440288 * 2
def baseEnd_2440288 : Nat := 835360452932702397118217

theorem tailTrace_2440288 : CollatzResearch.WordTrace tailWord_2440288 prefixEnd_2440288 835360452932702397118217 := by
  unfold tailWord_2440288
  simp only [CollatzResearch.WordTrace]
  refine ⟨44502307691630409427456759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59336410255507212569942345 44502307691630409427456759)
  ·
    refine ⟨66753461537445614141185139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44502307691630409427456759 66753461537445614141185139)
    ·
      refine ⟨100130192306168421211777709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66753461537445614141185139 100130192306168421211777709)
      ·
        refine ⟨37548822114813157954416641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100130192306168421211777709 37548822114813157954416641)
        ·
          refine ⟨28161616586109868465812481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37548822114813157954416641 28161616586109868465812481)
          ·
            refine ⟨21121212439582401349359361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28161616586109868465812481 21121212439582401349359361)
            ·
              refine ⟨15840909329686801012019521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21121212439582401349359361 15840909329686801012019521)
              ·
                refine ⟨11880681997265100759014641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15840909329686801012019521 11880681997265100759014641)
                ·
                  refine ⟨8910511497948825569260981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11880681997265100759014641 8910511497948825569260981)
                  ·
                    refine ⟨835360452932702397118217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8910511497948825569260981 835360452932702397118217)
                    ·
                      rfl

theorem cell22_2440288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_2440288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440288 prefixEnd_2440288 := by exact prefixLift 2440288
  have htrace : WordTrace (prefixWord ++ tailWord_2440288) baseStart_2440288 baseEnd_2440288 := by
    simpa [prefixWord, tailWord_2440288, baseEnd_2440288] using wordTrace_append hprefix tailTrace_2440288
  have hstable : (prefixWord ++ tailWord_2440288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440288).length < 2 ^ (prefixWord ++ tailWord_2440288).sum := by decide
  have hdescent : baseEnd_2440288 < baseStart_2440288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440303 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 5, 4]
def baseStart_2440303 : Nat := 118140960795 + 2440303 * 2 ^ 59
def prefixEnd_2440303 : Nat := 4983230072969 + 3 ^ 40 * 2440303 * 2
def baseEnd_2440303 : Nat := 835365587739247357993171

theorem tailTrace_2440303 : CollatzResearch.WordTrace tailWord_2440303 prefixEnd_2440303 835365587739247357993171 := by
  unfold tailWord_2440303
  simp only [CollatzResearch.WordTrace]
  refine ⟨89005162478206476416709563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59336774985470984277806375 89005162478206476416709563)
  ·
    refine ⟨133507743717309714625064345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89005162478206476416709563 133507743717309714625064345)
    ·
      refine ⟨100130807787982285968798259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133507743717309714625064345 100130807787982285968798259)
      ·
        refine ⟨150196211681973428953197389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100130807787982285968798259 150196211681973428953197389)
        ·
          refine ⟨56323579380740035857449021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150196211681973428953197389 56323579380740035857449021)
          ·
            refine ⟨21121342267777513446543383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56323579380740035857449021 21121342267777513446543383)
            ·
              refine ⟨31682013401666270169815075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21121342267777513446543383 31682013401666270169815075)
              ·
                refine ⟨47523020102499405254722613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31682013401666270169815075 47523020102499405254722613)
                ·
                  refine ⟨4455283134609319242630245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47523020102499405254722613 4455283134609319242630245)
                  ·
                    refine ⟨835365587739247357993171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4455283134609319242630245 835365587739247357993171)
                    ·
                      rfl

theorem cell22_2440303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_2440303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440303 prefixEnd_2440303 := by exact prefixLift 2440303
  have htrace : WordTrace (prefixWord ++ tailWord_2440303) baseStart_2440303 baseEnd_2440303 := by
    simpa [prefixWord, tailWord_2440303, baseEnd_2440303] using wordTrace_append hprefix tailTrace_2440303
  have hstable : (prefixWord ++ tailWord_2440303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440303).length < 2 ^ (prefixWord ++ tailWord_2440303).sum := by decide
  have hdescent : baseEnd_2440303 < baseStart_2440303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440378 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_2440378 : Nat := 118140960795 + 2440378 * 2 ^ 59
def prefixEnd_2440378 : Nat := 4983230072969 + 3 ^ 40 * 2440378 * 2
def baseEnd_2440378 : Nat := 835391261771972162367941

theorem tailTrace_2440378 : CollatzResearch.WordTrace tailWord_2440378 prefixEnd_2440378 835391261771972162367941 := by
  unfold tailWord_2440378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22251974488233691056422447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59338598635289842817126525 22251974488233691056422447)
  ·
    refine ⟨33377961732350536584633671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22251974488233691056422447 33377961732350536584633671)
    ·
      refine ⟨50066942598525804876950507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33377961732350536584633671 50066942598525804876950507)
      ·
        refine ⟨75100413897788707315425761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50066942598525804876950507 75100413897788707315425761)
        ·
          refine ⟨56325310423341530486569321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75100413897788707315425761 56325310423341530486569321)
          ·
            refine ⟨42243982817506147864926991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56325310423341530486569321 42243982817506147864926991)
            ·
              refine ⟨63365974226259221797390487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42243982817506147864926991 63365974226259221797390487)
              ·
                refine ⟨95048961339388832696085731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63365974226259221797390487 95048961339388832696085731)
                ·
                  refine ⟨142573442009083249044128597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95048961339388832696085731 142573442009083249044128597)
                  ·
                    refine ⟨835391261771972162367941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 142573442009083249044128597 835391261771972162367941)
                    ·
                      rfl

theorem cell22_2440378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_2440378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440378 prefixEnd_2440378 := by exact prefixLift 2440378
  have htrace : WordTrace (prefixWord ++ tailWord_2440378) baseStart_2440378 baseEnd_2440378 := by
    simpa [prefixWord, tailWord_2440378, baseEnd_2440378] using wordTrace_append hprefix tailTrace_2440378
  have hstable : (prefixWord ++ tailWord_2440378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440378).length < 2 ^ (prefixWord ++ tailWord_2440378).sum := by decide
  have hdescent : baseEnd_2440378 < baseStart_2440378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440380 : List Nat := [2, 2, 2, 3, 2, 2, 1, 8]
def baseStart_2440380 : Nat := 118140960795 + 2440380 * 2 ^ 59
def prefixEnd_2440380 : Nat := 4983230072969 + 3 ^ 40 * 2440380 * 2
def baseEnd_2440380 : Nat := 92821327379204980424215

theorem tailTrace_2440380 : CollatzResearch.WordTrace tailWord_2440380 prefixEnd_2440380 92821327379204980424215 := by
  unfold tailWord_2440380
  simp only [CollatzResearch.WordTrace]
  refine ⟨44503985449463759283631297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59338647265951679044841729 44503985449463759283631297)
  ·
    refine ⟨33377989087097819462723473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44503985449463759283631297 33377989087097819462723473)
    ·
      refine ⟨25033491815323364597042605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33377989087097819462723473 25033491815323364597042605)
      ·
        refine ⟨9387559430746261723890977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25033491815323364597042605 9387559430746261723890977)
        ·
          refine ⟨7040669573059696292918233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9387559430746261723890977 7040669573059696292918233)
          ·
            refine ⟨5280502179794772219688675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7040669573059696292918233 5280502179794772219688675)
            ·
              refine ⟨7920753269692158329533013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5280502179794772219688675 7920753269692158329533013)
              ·
                refine ⟨92821327379204980424215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7920753269692158329533013 92821327379204980424215)
                ·
                  rfl

theorem cell22_2440380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 8].length) (baseStart_2440380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440380 prefixEnd_2440380 := by exact prefixLift 2440380
  have htrace : WordTrace (prefixWord ++ tailWord_2440380) baseStart_2440380 baseEnd_2440380 := by
    simpa [prefixWord, tailWord_2440380, baseEnd_2440380] using wordTrace_append hprefix tailTrace_2440380
  have hstable : (prefixWord ++ tailWord_2440380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440380).length < 2 ^ (prefixWord ++ tailWord_2440380).sum := by decide
  have hdescent : baseEnd_2440380 < baseStart_2440380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440519 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 2, 3]
def baseStart_2440519 : Nat := 118140960795 + 2440519 * 2 ^ 59
def prefixEnd_2440519 : Nat := 4983230072969 + 3 ^ 40 * 2440519 * 2
def baseEnd_2440519 : Nat := 835439528953494794592509

theorem tailTrace_2440519 : CollatzResearch.WordTrace tailWord_2440519 prefixEnd_2440519 835439528953494794592509 := by
  unfold tailWord_2440519
  simp only [CollatzResearch.WordTrace]
  refine ⟨89013040645423945306572611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59342027096949296871048407 89013040645423945306572611)
  ·
    refine ⟨133519560968135917959858917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89013040645423945306572611 133519560968135917959858917)
    ·
      refine ⟨25034917681525484617473547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133519560968135917959858917 25034917681525484617473547)
      ·
        refine ⟨37552376522288226926210321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25034917681525484617473547 37552376522288226926210321)
        ·
          refine ⟨28164282391716170194657741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37552376522288226926210321 28164282391716170194657741)
          ·
            refine ⟨10561605896893563822996653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28164282391716170194657741 10561605896893563822996653)
            ·
              refine ⟨3960602211335086433623745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10561605896893563822996653 3960602211335086433623745)
              ·
                refine ⟨2970451658501314825217809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3960602211335086433623745 2970451658501314825217809)
                ·
                  refine ⟨2227838743875986118913357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2970451658501314825217809 2227838743875986118913357)
                  ·
                    refine ⟨835439528953494794592509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2227838743875986118913357 835439528953494794592509)
                    ·
                      rfl

theorem cell22_2440519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_2440519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440519 prefixEnd_2440519 := by exact prefixLift 2440519
  have htrace : WordTrace (prefixWord ++ tailWord_2440519) baseStart_2440519 baseEnd_2440519 := by
    simpa [prefixWord, tailWord_2440519, baseEnd_2440519] using wordTrace_append hprefix tailTrace_2440519
  have hstable : (prefixWord ++ tailWord_2440519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440519).length < 2 ^ (prefixWord ++ tailWord_2440519).sum := by decide
  have hdescent : baseEnd_2440519 < baseStart_2440519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440545 : List Nat := [1, 2, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2440545 : Nat := 118140960795 + 2440545 * 2 ^ 59
def prefixEnd_2440545 : Nat := 4983230072969 + 3 ^ 40 * 2440545 * 2
def baseEnd_2440545 : Nat := 835448429284839393442429

theorem tailTrace_2440545 : CollatzResearch.WordTrace tailWord_2440545 prefixEnd_2440545 835448429284839393442429 := by
  unfold tailWord_2440545
  simp only [CollatzResearch.WordTrace]
  refine ⟨89013988943329751747019089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59342659295553167831346059 89013988943329751747019089)
  ·
    refine ⟨66760491707497313810264317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89013988943329751747019089 66760491707497313810264317)
    ·
      refine ⟨25035184390311492678849119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66760491707497313810264317 25035184390311492678849119)
      ·
        refine ⟨37552776585467239018273679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25035184390311492678849119 37552776585467239018273679)
        ·
          refine ⟨56329164878200858527410519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37552776585467239018273679 56329164878200858527410519)
          ·
            refine ⟨84493747317301287791115779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56329164878200858527410519 84493747317301287791115779)
            ·
              refine ⟨126740620975951931686673669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84493747317301287791115779 126740620975951931686673669)
              ·
                refine ⟨23763866432990987191251313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126740620975951931686673669 23763866432990987191251313)
                ·
                  refine ⟨17822899824743240393438485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23763866432990987191251313 17822899824743240393438485)
                  ·
                    refine ⟨835448429284839393442429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17822899824743240393438485 835448429284839393442429)
                    ·
                      rfl

theorem cell22_2440545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2440545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440545 prefixEnd_2440545 := by exact prefixLift 2440545
  have htrace : WordTrace (prefixWord ++ tailWord_2440545) baseStart_2440545 baseEnd_2440545 := by
    simpa [prefixWord, tailWord_2440545, baseEnd_2440545] using wordTrace_append hprefix tailTrace_2440545
  have hstable : (prefixWord ++ tailWord_2440545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440545).length < 2 ^ (prefixWord ++ tailWord_2440545).sum := by decide
  have hdescent : baseEnd_2440545 < baseStart_2440545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440560 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 9]
def baseStart_2440560 : Nat := 118140960795 + 2440560 * 2 ^ 59
def prefixEnd_2440560 : Nat := 4983230072969 + 3 ^ 40 * 2440560 * 2
def baseEnd_2440560 : Nat := 278484521363794784772461

theorem tailTrace_2440560 : CollatzResearch.WordTrace tailWord_2440560 prefixEnd_2440560 278484521363794784772461 := by
  unfold tailWord_2440560
  simp only [CollatzResearch.WordTrace]
  refine ⟨44507268019137704654407567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59343024025516939539210089 44507268019137704654407567)
  ·
    refine ⟨66760902028706556981611351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44507268019137704654407567 66760902028706556981611351)
    ·
      refine ⟨100141353043059835472417027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66760902028706556981611351 100141353043059835472417027)
      ·
        refine ⟨150212029564589753208625541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100141353043059835472417027 150212029564589753208625541)
        ·
          refine ⟨28164755543360578726617289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150212029564589753208625541 28164755543360578726617289)
          ·
            refine ⟨21123566657520434044962967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28164755543360578726617289 21123566657520434044962967)
            ·
              refine ⟨31685349986280651067444451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21123566657520434044962967 31685349986280651067444451)
              ·
                refine ⟨47528024979420976601166677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31685349986280651067444451 47528024979420976601166677)
                ·
                  refine ⟨278484521363794784772461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47528024979420976601166677 278484521363794784772461)
                  ·
                    rfl

theorem cell22_2440560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_2440560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440560 prefixEnd_2440560 := by exact prefixLift 2440560
  have htrace : WordTrace (prefixWord ++ tailWord_2440560) baseStart_2440560 baseEnd_2440560 := by
    simpa [prefixWord, tailWord_2440560, baseEnd_2440560] using wordTrace_append hprefix tailTrace_2440560
  have hstable : (prefixWord ++ tailWord_2440560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440560).length < 2 ^ (prefixWord ++ tailWord_2440560).sum := by decide
  have hdescent : baseEnd_2440560 < baseStart_2440560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440637 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_2440637 : Nat := 118140960795 + 2440637 * 2 ^ 59
def prefixEnd_2440637 : Nat := 4983230072969 + 3 ^ 40 * 2440637 * 2
def baseEnd_2440637 : Nat := 835479922764981820142147

theorem tailTrace_2440637 : CollatzResearch.WordTrace tailWord_2440637 prefixEnd_2440637 835479922764981820142147 := by
  unfold tailWord_2440637
  simp only [CollatzResearch.WordTrace]
  refine ⟨89017344458996451459368165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59344896305997634306245443 89017344458996451459368165)
  ·
    refine ⟨16690752086061834648631531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89017344458996451459368165 16690752086061834648631531)
    ·
      refine ⟨25036128129092751972947297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16690752086061834648631531 25036128129092751972947297)
      ·
        refine ⟨18777096096819563979710473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25036128129092751972947297 18777096096819563979710473)
        ·
          refine ⟨14082822072614672984782855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18777096096819563979710473 14082822072614672984782855)
          ·
            refine ⟨21124233108922009477174283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14082822072614672984782855 21124233108922009477174283)
            ·
              refine ⟨31686349663383014215761425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21124233108922009477174283 31686349663383014215761425)
              ·
                refine ⟨23764762247537260661821069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31686349663383014215761425 23764762247537260661821069)
                ·
                  refine ⟨8911785842826472748182901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23764762247537260661821069 8911785842826472748182901)
                  ·
                    refine ⟨835479922764981820142147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8911785842826472748182901 835479922764981820142147)
                    ·
                      rfl

theorem cell22_2440637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_2440637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440637 prefixEnd_2440637 := by exact prefixLift 2440637
  have htrace : WordTrace (prefixWord ++ tailWord_2440637) baseStart_2440637 baseEnd_2440637 := by
    simpa [prefixWord, tailWord_2440637, baseEnd_2440637] using wordTrace_append hprefix tailTrace_2440637
  have hstable : (prefixWord ++ tailWord_2440637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440637).length < 2 ^ (prefixWord ++ tailWord_2440637).sum := by decide
  have hdescent : baseEnd_2440637 < baseStart_2440637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440669 : List Nat := [1, 4, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_2440669 : Nat := 118140960795 + 2440669 * 2 ^ 59
def prefixEnd_2440669 : Nat := 4983230072969 + 3 ^ 40 * 2440669 * 2
def baseEnd_2440669 : Nat := 835490877018944403342049

theorem tailTrace_2440669 : CollatzResearch.WordTrace tailWord_2440669 prefixEnd_2440669 835490877018944403342049 := by
  unfold tailWord_2440669
  simp only [CollatzResearch.WordTrace]
  refine ⟨89018511594880520924533061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59345674396587013949688707 89018511594880520924533061)
  ·
    refine ⟨16690970924040097673349949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89018511594880520924533061 16690970924040097673349949)
    ·
      refine ⟨6259114096515036627506231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16690970924040097673349949 6259114096515036627506231)
      ·
        refine ⟨9388671144772554941259347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6259114096515036627506231 9388671144772554941259347)
        ·
          refine ⟨14083006717158832411889021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9388671144772554941259347 14083006717158832411889021)
          ·
            refine ⟨5281127518934562154458383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14083006717158832411889021 5281127518934562154458383)
            ·
              refine ⟨7921691278401843231687575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281127518934562154458383 7921691278401843231687575)
              ·
                refine ⟨11882536917602764847531363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7921691278401843231687575 11882536917602764847531363)
                ·
                  refine ⟨17823805376404147271297045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11882536917602764847531363 17823805376404147271297045)
                  ·
                    refine ⟨835490877018944403342049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17823805376404147271297045 835490877018944403342049)
                    ·
                      rfl

theorem cell22_2440669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_2440669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440669 prefixEnd_2440669 := by exact prefixLift 2440669
  have htrace : WordTrace (prefixWord ++ tailWord_2440669) baseStart_2440669 baseEnd_2440669 := by
    simpa [prefixWord, tailWord_2440669, baseEnd_2440669] using wordTrace_append hprefix tailTrace_2440669
  have hstable : (prefixWord ++ tailWord_2440669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440669).length < 2 ^ (prefixWord ++ tailWord_2440669).sum := by decide
  have hdescent : baseEnd_2440669 < baseStart_2440669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440718 : List Nat := [4, 1, 1, 2, 5, 1, 2, 6]
def baseStart_2440718 : Nat := 118140960795 + 2440718 * 2 ^ 59
def prefixEnd_2440718 : Nat := 4983230072969 + 3 ^ 40 * 2440718 * 2
def baseEnd_2440718 : Nat := 92834183413369400985211

theorem tailTrace_2440718 : CollatzResearch.WordTrace tailWord_2440718 prefixEnd_2440718 92834183413369400985211 := by
  unfold tailWord_2440718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11127537346462875286633351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59346865847802001528711205 11127537346462875286633351)
  ·
    refine ⟨16691306019694312929950027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11127537346462875286633351 16691306019694312929950027)
    ·
      refine ⟨25036959029541469394925041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16691306019694312929950027 25036959029541469394925041)
      ·
        refine ⟨18777719272156102046193781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25036959029541469394925041 18777719272156102046193781)
        ·
          refine ⟨1760411181764634566830667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18777719272156102046193781 1760411181764634566830667)
          ·
            refine ⟨2640616772646951850246001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760411181764634566830667 2640616772646951850246001)
            ·
              refine ⟨1980462579485213887684501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2640616772646951850246001 1980462579485213887684501)
              ·
                refine ⟨92834183413369400985211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1980462579485213887684501 92834183413369400985211)
                ·
                  rfl

theorem cell22_2440718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_2440718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440718 prefixEnd_2440718 := by exact prefixLift 2440718
  have htrace : WordTrace (prefixWord ++ tailWord_2440718) baseStart_2440718 baseEnd_2440718 := by
    simpa [prefixWord, tailWord_2440718, baseEnd_2440718] using wordTrace_append hprefix tailTrace_2440718
  have hstable : (prefixWord ++ tailWord_2440718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440718).length < 2 ^ (prefixWord ++ tailWord_2440718).sum := by decide
  have hdescent : baseEnd_2440718 < baseStart_2440718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440808 : List Nat := [2, 1, 4, 3, 1, 2, 1, 4, 4]
def baseStart_2440808 : Nat := 118140960795 + 2440808 * 2 ^ 59
def prefixEnd_2440808 : Nat := 4983230072969 + 3 ^ 40 * 2440808 * 2
def baseEnd_2440808 : Nat := 278512819853198124705541

theorem tailTrace_2440808 : CollatzResearch.WordTrace tailWord_2440808 prefixEnd_2440808 278512819853198124705541 := by
  unfold tailWord_2440808
  simp only [CollatzResearch.WordTrace]
  refine ⟨44511790670688473831921539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59349054227584631775895385 44511790670688473831921539)
  ·
    refine ⟨66767686006032710747882309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44511790670688473831921539 66767686006032710747882309)
    ·
      refine ⟨12518941126131133265227933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66767686006032710747882309 12518941126131133265227933)
      ·
        refine ⟨4694602922299174974460475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12518941126131133265227933 4694602922299174974460475)
        ·
          refine ⟨7041904383448762461690713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694602922299174974460475 7041904383448762461690713)
          ·
            refine ⟨5281428287586571846268035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7041904383448762461690713 5281428287586571846268035)
            ·
              refine ⟨7922142431379857769402053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5281428287586571846268035 7922142431379857769402053)
              ·
                refine ⟨1485401705883723331762885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7922142431379857769402053 1485401705883723331762885)
                ·
                  refine ⟨278512819853198124705541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1485401705883723331762885 278512819853198124705541)
                  ·
                    rfl

theorem cell22_2440808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 4].length) (baseStart_2440808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440808 prefixEnd_2440808 := by exact prefixLift 2440808
  have htrace : WordTrace (prefixWord ++ tailWord_2440808) baseStart_2440808 baseEnd_2440808 := by
    simpa [prefixWord, tailWord_2440808, baseEnd_2440808] using wordTrace_append hprefix tailTrace_2440808
  have hstable : (prefixWord ++ tailWord_2440808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440808).length < 2 ^ (prefixWord ++ tailWord_2440808).sum := by decide
  have hdescent : baseEnd_2440808 < baseStart_2440808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440868 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 3, 3]
def baseStart_2440868 : Nat := 118140960795 + 2440868 * 2 ^ 59
def prefixEnd_2440868 : Nat := 4983230072969 + 3 ^ 40 * 2440868 * 2
def baseEnd_2440868 : Nat := 835558998785774217616439

theorem tailTrace_2440868 : CollatzResearch.WordTrace tailWord_2440868 prefixEnd_2440868 835558998785774217616439 := by
  unfold tailWord_2440868
  simp only [CollatzResearch.WordTrace]
  refine ⟨44512884860579788955513629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59350513147439718607351505 44512884860579788955513629)
  ·
    refine ⟨16692331822717420858317611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44512884860579788955513629 16692331822717420858317611)
    ·
      refine ⟨25038497734076131287476417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16692331822717420858317611 25038497734076131287476417)
      ·
        refine ⟨18778873300557098465607313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25038497734076131287476417 18778873300557098465607313)
        ·
          refine ⟨14084154975417823849205485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18778873300557098465607313 14084154975417823849205485)
          ·
            refine ⟨5281558115781683943452057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14084154975417823849205485 5281558115781683943452057)
            ·
              refine ⟨3961168586836262957589043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5281558115781683943452057 3961168586836262957589043)
              ·
                refine ⟨5941752880254394436383565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961168586836262957589043 5941752880254394436383565)
                ·
                  refine ⟨2228157330095397913643837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5941752880254394436383565 2228157330095397913643837)
                  ·
                    refine ⟨835558998785774217616439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228157330095397913643837 835558998785774217616439)
                    ·
                      rfl

theorem cell22_2440868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_2440868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440868 prefixEnd_2440868 := by exact prefixLift 2440868
  have htrace : WordTrace (prefixWord ++ tailWord_2440868) baseStart_2440868 baseEnd_2440868 := by
    simpa [prefixWord, tailWord_2440868, baseEnd_2440868] using wordTrace_append hprefix tailTrace_2440868
  have hstable : (prefixWord ++ tailWord_2440868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440868).length < 2 ^ (prefixWord ++ tailWord_2440868).sum := by decide
  have hdescent : baseEnd_2440868 < baseStart_2440868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440879 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 2, 5]
def baseStart_2440879 : Nat := 118140960795 + 2440879 * 2 ^ 59
def prefixEnd_2440879 : Nat := 4983230072969 + 3 ^ 40 * 2440879 * 2
def baseEnd_2440879 : Nat := 835562764310573855591405

theorem tailTrace_2440879 : CollatzResearch.WordTrace tailWord_2440879 prefixEnd_2440879 835562764310573855591405 := by
  unfold tailWord_2440879
  simp only [CollatzResearch.WordTrace]
  refine ⟨89026170924119726789677691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59350780616079817859785127 89026170924119726789677691)
  ·
    refine ⟨133539256386179590184516537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89026170924119726789677691 133539256386179590184516537)
    ·
      refine ⟨100154442289634692638387403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133539256386179590184516537 100154442289634692638387403)
      ·
        refine ⟨150231663434452038957581105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100154442289634692638387403 150231663434452038957581105)
        ·
          refine ⟨112673747575839029218185829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150231663434452038957581105 112673747575839029218185829)
          ·
            refine ⟨21126327670469817978409843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112673747575839029218185829 21126327670469817978409843)
            ·
              refine ⟨31689491505704726967614765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21126327670469817978409843 31689491505704726967614765)
              ·
                refine ⟨11883559314639272612855537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31689491505704726967614765 11883559314639272612855537)
                ·
                  refine ⟨8912669485979454459641653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11883559314639272612855537 8912669485979454459641653)
                  ·
                    refine ⟨835562764310573855591405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8912669485979454459641653 835562764310573855591405)
                    ·
                      rfl

theorem cell22_2440879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_2440879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440879 prefixEnd_2440879 := by exact prefixLift 2440879
  have htrace : WordTrace (prefixWord ++ tailWord_2440879) baseStart_2440879 baseEnd_2440879 := by
    simpa [prefixWord, tailWord_2440879, baseEnd_2440879] using wordTrace_append hprefix tailTrace_2440879
  have hstable : (prefixWord ++ tailWord_2440879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440879).length < 2 ^ (prefixWord ++ tailWord_2440879).sum := by decide
  have hdescent : baseEnd_2440879 < baseStart_2440879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440939 : List Nat := [1, 1, 1, 1, 2, 4, 2, 1, 3, 6]
def baseStart_2440939 : Nat := 118140960795 + 2440939 * 2 ^ 59
def prefixEnd_2440939 : Nat := 4983230072969 + 3 ^ 40 * 2440939 * 2
def baseEnd_2440939 : Nat := 835583303536753699091221

theorem tailTrace_2440939 : CollatzResearch.WordTrace tailWord_2440939 prefixEnd_2440939 835583303536753699091221 := by
  unfold tailWord_2440939
  simp only [CollatzResearch.WordTrace]
  refine ⟨89028359303902357036861871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59352239535934904691241247 89028359303902357036861871)
  ·
    refine ⟨133542538955853535555292807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89028359303902357036861871 133542538955853535555292807)
    ·
      refine ⟨200313808433780303332939211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133542538955853535555292807 200313808433780303332939211)
      ·
        refine ⟨300470712650670454999408817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200313808433780303332939211 300470712650670454999408817)
        ·
          refine ⟨225353034488002841249556613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300470712650670454999408817 225353034488002841249556613)
          ·
            refine ⟨42253693966500532734291865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225353034488002841249556613 42253693966500532734291865)
            ·
              refine ⟨31690270474875399550718899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42253693966500532734291865 31690270474875399550718899)
              ·
                refine ⟨47535405712313099326078349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31690270474875399550718899 47535405712313099326078349)
                ·
                  refine ⟨17825777142117412247279381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47535405712313099326078349 17825777142117412247279381)
                  ·
                    refine ⟨835583303536753699091221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17825777142117412247279381 835583303536753699091221)
                    ·
                      rfl

theorem cell22_2440939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_2440939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440939 prefixEnd_2440939 := by exact prefixLift 2440939
  have htrace : WordTrace (prefixWord ++ tailWord_2440939) baseStart_2440939 baseEnd_2440939 := by
    simpa [prefixWord, tailWord_2440939, baseEnd_2440939] using wordTrace_append hprefix tailTrace_2440939
  have hstable : (prefixWord ++ tailWord_2440939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440939).length < 2 ^ (prefixWord ++ tailWord_2440939).sum := by decide
  have hdescent : baseEnd_2440939 < baseStart_2440939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2440966 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2440966 : Nat := 118140960795 + 2440966 * 2 ^ 59
def prefixEnd_2440966 : Nat := 4983230072969 + 3 ^ 40 * 2440966 * 2
def baseEnd_2440966 : Nat := 278530848729511542888713

theorem tailTrace_2440966 : CollatzResearch.WordTrace tailWord_2440966 prefixEnd_2440966 278530848729511542888713 := by
  unfold tailWord_2440966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782167002337641895252961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59352896049869693765396501 2782167002337641895252961)
  ·
    refine ⟨2086625251753231421439721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2782167002337641895252961 2086625251753231421439721)
    ·
      refine ⟨1564968938814923566079791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2086625251753231421439721 1564968938814923566079791)
      ·
        refine ⟨2347453408222385349119687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564968938814923566079791 2347453408222385349119687)
        ·
          refine ⟨3521180112333578023679531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2347453408222385349119687 3521180112333578023679531)
          ·
            refine ⟨5281770168500367035519297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521180112333578023679531 5281770168500367035519297)
            ·
              refine ⟨3961327626375275276639473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5281770168500367035519297 3961327626375275276639473)
              ·
                refine ⟨2970995719781456457479605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3961327626375275276639473 2970995719781456457479605)
                ·
                  refine ⟨278530848729511542888713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2970995719781456457479605 278530848729511542888713)
                  ·
                    rfl

theorem cell22_2440966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2440966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2440966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2440966 prefixEnd_2440966 := by exact prefixLift 2440966
  have htrace : WordTrace (prefixWord ++ tailWord_2440966) baseStart_2440966 baseEnd_2440966 := by
    simpa [prefixWord, tailWord_2440966, baseEnd_2440966] using wordTrace_append hprefix tailTrace_2440966
  have hstable : (prefixWord ++ tailWord_2440966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2440966).length < 2 ^ (prefixWord ++ tailWord_2440966).sum := by decide
  have hdescent : baseEnd_2440966 < baseStart_2440966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2440966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441020 : List Nat := [2, 2, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_2441020 : Nat := 118140960795 + 2441020 * 2 ^ 59
def prefixEnd_2441020 : Nat := 4983230072969 + 3 ^ 40 * 2441020 * 2
def baseEnd_2441020 : Nat := 835611031492096487815973

theorem tailTrace_2441020 : CollatzResearch.WordTrace tailWord_2441020 prefixEnd_2441020 835611031492096487815973 := by
  unfold tailWord_2441020
  simp only [CollatzResearch.WordTrace]
  refine ⟨44515656808304453935280257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59354209077739271913707009 44515656808304453935280257)
  ·
    refine ⟨33386742606228340451460193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44515656808304453935280257 33386742606228340451460193)
    ·
      refine ⟨25040056954671255338595145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33386742606228340451460193 25040056954671255338595145)
      ·
        refine ⟨18780042716003441503946359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25040056954671255338595145 18780042716003441503946359)
        ·
          refine ⟨28170064074005162255919539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18780042716003441503946359 28170064074005162255919539)
          ·
            refine ⟨42255096111007743383879309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28170064074005162255919539 42255096111007743383879309)
            ·
              refine ⟨15845661041627903768954741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42255096111007743383879309 15845661041627903768954741)
              ·
                refine ⟨1485530722652615978339507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15845661041627903768954741 1485530722652615978339507)
                ·
                  refine ⟨2228296083978923967509261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485530722652615978339507 2228296083978923967509261)
                  ·
                    refine ⟨835611031492096487815973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228296083978923967509261 835611031492096487815973)
                    ·
                      rfl

theorem cell22_2441020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_2441020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441020 prefixEnd_2441020 := by exact prefixLift 2441020
  have htrace : WordTrace (prefixWord ++ tailWord_2441020) baseStart_2441020 baseEnd_2441020 := by
    simpa [prefixWord, tailWord_2441020, baseEnd_2441020] using wordTrace_append hprefix tailTrace_2441020
  have hstable : (prefixWord ++ tailWord_2441020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441020).length < 2 ^ (prefixWord ++ tailWord_2441020).sum := by decide
  have hdescent : baseEnd_2441020 < baseStart_2441020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441031 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 2, 5]
def baseStart_2441031 : Nat := 118140960795 + 2441031 * 2 ^ 59
def prefixEnd_2441031 : Nat := 4983230072969 + 3 ^ 40 * 2441031 * 2
def baseEnd_2441031 : Nat := 835614797016896125790939

theorem tailTrace_2441031 : CollatzResearch.WordTrace tailWord_2441031 prefixEnd_2441031 835614797016896125790939 := by
  unfold tailWord_2441031
  simp only [CollatzResearch.WordTrace]
  refine ⟨89031714819569056749210947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59354476546379371166140631 89031714819569056749210947)
  ·
    refine ⟨133547572229353585123816421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89031714819569056749210947 133547572229353585123816421)
    ·
      refine ⟨25040169793003797210715579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133547572229353585123816421 25040169793003797210715579)
      ·
        refine ⟨37560254689505695816073369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25040169793003797210715579 37560254689505695816073369)
        ·
          refine ⟨28170191017129271862055027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37560254689505695816073369 28170191017129271862055027)
          ·
            refine ⟨42255286525693907793082541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28170191017129271862055027 42255286525693907793082541)
            ·
              refine ⟨15845732447135215422405953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42255286525693907793082541 15845732447135215422405953)
              ·
                refine ⟨11884299335351411566804465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15845732447135215422405953 11884299335351411566804465)
                ·
                  refine ⟨8913224501513558675103349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11884299335351411566804465 8913224501513558675103349)
                  ·
                    refine ⟨835614797016896125790939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8913224501513558675103349 835614797016896125790939)
                    ·
                      rfl

theorem cell22_2441031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_2441031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441031 prefixEnd_2441031 := by exact prefixLift 2441031
  have htrace : WordTrace (prefixWord ++ tailWord_2441031) baseStart_2441031 baseEnd_2441031 := by
    simpa [prefixWord, tailWord_2441031, baseEnd_2441031] using wordTrace_append hprefix tailTrace_2441031
  have hstable : (prefixWord ++ tailWord_2441031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441031).length < 2 ^ (prefixWord ++ tailWord_2441031).sum := by decide
  have hdescent : baseEnd_2441031 < baseStart_2441031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441037 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2441037 : Nat := 118140960795 + 2441037 * 2 ^ 59
def prefixEnd_2441037 : Nat := 4983230072969 + 3 ^ 40 * 2441037 * 2
def baseEnd_2441037 : Nat := 835616850939514110140921

theorem tailTrace_2441037 : CollatzResearch.WordTrace tailWord_2441037 prefixEnd_2441037 835616850939514110140921 := by
  unfold tailWord_2441037
  simp only [CollatzResearch.WordTrace]
  refine ⟨89031933657547319773929365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59354622438364879849286243 89031933657547319773929365)
  ·
    refine ⟨4173371890197530614402939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89031933657547319773929365 4173371890197530614402939)
    ·
      refine ⟨6260057835296295921604409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4173371890197530614402939 6260057835296295921604409)
      ·
        refine ⟨4695043376472221941203307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6260057835296295921604409 4695043376472221941203307)
        ·
          refine ⟨7042565064708332911804961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4695043376472221941203307 7042565064708332911804961)
          ·
            refine ⟨5281923798531249683853721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7042565064708332911804961 5281923798531249683853721)
            ·
              refine ⟨3961442848898437262890291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5281923798531249683853721 3961442848898437262890291)
              ·
                refine ⟨5942164273347655894335437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961442848898437262890291 5942164273347655894335437)
                ·
                  refine ⟨2228311602505370960375789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5942164273347655894335437 2228311602505370960375789)
                  ·
                    refine ⟨835616850939514110140921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228311602505370960375789 835616850939514110140921)
                    ·
                      rfl

theorem cell22_2441037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2441037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441037 prefixEnd_2441037 := by exact prefixLift 2441037
  have htrace : WordTrace (prefixWord ++ tailWord_2441037) baseStart_2441037 baseEnd_2441037 := by
    simpa [prefixWord, tailWord_2441037, baseEnd_2441037] using wordTrace_append hprefix tailTrace_2441037
  have hstable : (prefixWord ++ tailWord_2441037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441037).length < 2 ^ (prefixWord ++ tailWord_2441037).sum := by decide
  have hdescent : baseEnd_2441037 < baseStart_2441037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441093 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_2441093 : Nat := 118140960795 + 2441093 * 2 ^ 59
def prefixEnd_2441093 : Nat := 4983230072969 + 3 ^ 40 * 2441093 * 2
def baseEnd_2441093 : Nat := 835636020883948630740749

theorem tailTrace_2441093 : CollatzResearch.WordTrace tailWord_2441093 prefixEnd_2441093 835636020883948630740749 := by
  unfold tailWord_2441093
  simp only [CollatzResearch.WordTrace]
  refine ⟨89033976145344441337967933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59355984096896294225311955 89033976145344441337967933)
  ·
    refine ⟨33387741054504165501737975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89033976145344441337967933 33387741054504165501737975)
    ·
      refine ⟨50081611581756248252606963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33387741054504165501737975 50081611581756248252606963)
      ·
        refine ⟨75122417372634372378910445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50081611581756248252606963 75122417372634372378910445)
        ·
          refine ⟨28170906514737889642091417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75122417372634372378910445 28170906514737889642091417)
          ·
            refine ⟨21128179886053417231568563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28170906514737889642091417 21128179886053417231568563)
            ·
              refine ⟨31692269829080125847352845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21128179886053417231568563 31692269829080125847352845)
              ·
                refine ⟨11884601185905047192757317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31692269829080125847352845 11884601185905047192757317)
                ·
                  refine ⟨2228362722357196348641997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11884601185905047192757317 2228362722357196348641997)
                  ·
                    refine ⟨835636020883948630740749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228362722357196348641997 835636020883948630740749)
                    ·
                      rfl

theorem cell22_2441093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_2441093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441093 prefixEnd_2441093 := by exact prefixLift 2441093
  have htrace : WordTrace (prefixWord ++ tailWord_2441093) baseStart_2441093 baseEnd_2441093 := by
    simpa [prefixWord, tailWord_2441093, baseEnd_2441093] using wordTrace_append hprefix tailTrace_2441093
  have hstable : (prefixWord ++ tailWord_2441093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441093).length < 2 ^ (prefixWord ++ tailWord_2441093).sum := by decide
  have hdescent : baseEnd_2441093 < baseStart_2441093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441095 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 6]
def baseStart_2441095 : Nat := 118140960795 + 2441095 * 2 ^ 59
def prefixEnd_2441095 : Nat := 4983230072969 + 3 ^ 40 * 2441095 * 2
def baseEnd_2441095 : Nat := 278545568508273764063581

theorem tailTrace_2441095 : CollatzResearch.WordTrace tailWord_2441095 prefixEnd_2441095 278545568508273764063581 := by
  unfold tailWord_2441095
  simp only [CollatzResearch.WordTrace]
  refine ⟨89034049091337195679540739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59356032727558130453027159 89034049091337195679540739)
  ·
    refine ⟨133551073637005793519311109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89034049091337195679540739 133551073637005793519311109)
    ·
      refine ⟨25040826306938586284870833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133551073637005793519311109 25040826306938586284870833)
      ·
        refine ⟨18780619730203939713653125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25040826306938586284870833 18780619730203939713653125)
        ·
          refine ⟨3521366199413238696309961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18780619730203939713653125 3521366199413238696309961)
          ·
            refine ⟨2641024649559929022232471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3521366199413238696309961 2641024649559929022232471)
            ·
              refine ⟨3961536974339893533348707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641024649559929022232471 3961536974339893533348707)
              ·
                refine ⟨5942305461509840300023061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3961536974339893533348707 5942305461509840300023061)
                ·
                  refine ⟨278545568508273764063581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5942305461509840300023061 278545568508273764063581)
                  ·
                    rfl

theorem cell22_2441095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 6].length) (baseStart_2441095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441095 prefixEnd_2441095 := by exact prefixLift 2441095
  have htrace : WordTrace (prefixWord ++ tailWord_2441095) baseStart_2441095 baseEnd_2441095 := by
    simpa [prefixWord, tailWord_2441095, baseEnd_2441095] using wordTrace_append hprefix tailTrace_2441095
  have hstable : (prefixWord ++ tailWord_2441095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441095).length < 2 ^ (prefixWord ++ tailWord_2441095).sum := by decide
  have hdescent : baseEnd_2441095 < baseStart_2441095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441136 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_2441136 : Nat := 118140960795 + 2441136 * 2 ^ 59
def prefixEnd_2441136 : Nat := 4983230072969 + 3 ^ 40 * 2441136 * 2
def baseEnd_2441136 : Nat := 835650740662710851915617

theorem tailTrace_2441136 : CollatzResearch.WordTrace tailWord_2441136 prefixEnd_2441136 835650740662710851915617 := by
  unfold tailWord_2441136
  simp only [CollatzResearch.WordTrace]
  refine ⟨44517772242094329840891631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59357029656125773121188841 44517772242094329840891631)
  ·
    refine ⟨66776658363141494761337447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44517772242094329840891631 66776658363141494761337447)
    ·
      refine ⟨100164987544712242142006171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66776658363141494761337447 100164987544712242142006171)
      ·
        refine ⟨150247481317068363213009257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100164987544712242142006171 150247481317068363213009257)
        ·
          refine ⟨112685610987801272409756943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150247481317068363213009257 112685610987801272409756943)
          ·
            refine ⟨169028416481701908614635415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112685610987801272409756943 169028416481701908614635415)
            ·
              refine ⟨253542624722552862921953123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169028416481701908614635415 253542624722552862921953123)
              ·
                refine ⟨380313937083829294382929685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253542624722552862921953123 380313937083829294382929685)
                ·
                  refine ⟨17827215800804498174199829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 380313937083829294382929685 17827215800804498174199829)
                  ·
                    refine ⟨835650740662710851915617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17827215800804498174199829 835650740662710851915617)
                    ·
                      rfl

theorem cell22_2441136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_2441136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441136 prefixEnd_2441136 := by exact prefixLift 2441136
  have htrace : WordTrace (prefixWord ++ tailWord_2441136) baseStart_2441136 baseEnd_2441136 := by
    simpa [prefixWord, tailWord_2441136, baseEnd_2441136] using wordTrace_append hprefix tailTrace_2441136
  have hstable : (prefixWord ++ tailWord_2441136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441136).length < 2 ^ (prefixWord ++ tailWord_2441136).sum := by decide
  have hdescent : baseEnd_2441136 < baseStart_2441136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441140 : List Nat := [2, 5, 2, 1, 2, 10]
def baseStart_2441140 : Nat := 118140960795 + 2441140 * 2 ^ 59
def prefixEnd_2441140 : Nat := 4983230072969 + 3 ^ 40 * 2441140 * 2
def baseEnd_2441140 : Nat := 10316692715363656479205

theorem tailTrace_2441140 : CollatzResearch.WordTrace tailWord_2441140 prefixEnd_2441140 10316692715363656479205 := by
  unfold tailWord_2441140
  simp only [CollatzResearch.WordTrace]
  refine ⟨44517845188087084182464437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59357126917449445576619249 44517845188087084182464437)
  ·
    refine ⟨4173547986383164142106041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44517845188087084182464437 4173547986383164142106041)
    ·
      refine ⟨3130160989787373106579531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4173547986383164142106041 3130160989787373106579531)
      ·
        refine ⟨4695241484681059659869297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130160989787373106579531 4695241484681059659869297)
        ·
          refine ⟨3521431113510794744901973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4695241484681059659869297 3521431113510794744901973)
          ·
            refine ⟨10316692715363656479205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3521431113510794744901973 10316692715363656479205)
            ·
              rfl

theorem cell22_2441140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 10].length) (baseStart_2441140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441140 prefixEnd_2441140 := by exact prefixLift 2441140
  have htrace : WordTrace (prefixWord ++ tailWord_2441140) baseStart_2441140 baseEnd_2441140 := by
    simpa [prefixWord, tailWord_2441140, baseEnd_2441140] using wordTrace_append hprefix tailTrace_2441140
  have hstable : (prefixWord ++ tailWord_2441140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441140).length < 2 ^ (prefixWord ++ tailWord_2441140).sum := by decide
  have hdescent : baseEnd_2441140 < baseStart_2441140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441168 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 5]
def baseStart_2441168 : Nat := 118140960795 + 2441168 * 2 ^ 59
def prefixEnd_2441168 : Nat := 4983230072969 + 3 ^ 40 * 2441168 * 2
def baseEnd_2441168 : Nat := 278553898305557811705173

theorem tailTrace_2441168 : CollatzResearch.WordTrace tailWord_2441168 prefixEnd_2441168 278553898305557811705173 := by
  unfold tailWord_2441168
  simp only [CollatzResearch.WordTrace]
  refine ⟨44518355810036364573474079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59357807746715152764632105 44518355810036364573474079)
  ·
    refine ⟨66777533715054546860211119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44518355810036364573474079 66777533715054546860211119)
    ·
      refine ⟨100166300572581820290316679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66777533715054546860211119 100166300572581820290316679)
      ·
        refine ⟨150249450858872730435475019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100166300572581820290316679 150249450858872730435475019)
        ·
          refine ⟨225374176288309095653212529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150249450858872730435475019 225374176288309095653212529)
          ·
            refine ⟨169030632216231821739909397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225374176288309095653212529 169030632216231821739909397)
            ·
              refine ⟨7923310885135866644058253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169030632216231821739909397 7923310885135866644058253)
              ·
                refine ⟨2971241581925949991521845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7923310885135866644058253 2971241581925949991521845)
                ·
                  refine ⟨278553898305557811705173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2971241581925949991521845 278553898305557811705173)
                  ·
                    rfl

theorem cell22_2441168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 5].length) (baseStart_2441168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441168 prefixEnd_2441168 := by exact prefixLift 2441168
  have htrace : WordTrace (prefixWord ++ tailWord_2441168) baseStart_2441168 baseEnd_2441168 := by
    simpa [prefixWord, tailWord_2441168, baseEnd_2441168] using wordTrace_append hprefix tailTrace_2441168
  have hstable : (prefixWord ++ tailWord_2441168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441168).length < 2 ^ (prefixWord ++ tailWord_2441168).sum := by decide
  have hdescent : baseEnd_2441168 < baseStart_2441168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441213 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 6]
def baseStart_2441213 : Nat := 118140960795 + 2441213 * 2 ^ 59
def prefixEnd_2441213 : Nat := 4983230072969 + 3 ^ 40 * 2441213 * 2
def baseEnd_2441213 : Nat := 278559033112102772580127

theorem tailTrace_2441213 : CollatzResearch.WordTrace tailWord_2441213 prefixEnd_2441213 278559033112102772580127 := by
  unfold tailWord_2441213
  simp only [CollatzResearch.WordTrace]
  refine ⟨89038352904909701832336293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59358901936606467888224195 89038352904909701832336293)
  ·
    refine ⟨16694691169670569093563055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89038352904909701832336293 16694691169670569093563055)
    ·
      refine ⟨25042036754505853640344583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16694691169670569093563055 25042036754505853640344583)
      ·
        refine ⟨37563055131758780460516875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25042036754505853640344583 37563055131758780460516875)
        ·
          refine ⟨56344582697638170690775313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37563055131758780460516875 56344582697638170690775313)
          ·
            refine ⟨42258437023228628018081485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56344582697638170690775313 42258437023228628018081485)
            ·
              refine ⟨15846913883710735506780557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42258437023228628018081485 15846913883710735506780557)
              ·
                refine ⟨5942592706391525815042709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15846913883710735506780557 5942592706391525815042709)
                ·
                  refine ⟨278559033112102772580127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5942592706391525815042709 278559033112102772580127)
                  ·
                    rfl

theorem cell22_2441213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_2441213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441213 prefixEnd_2441213 := by exact prefixLift 2441213
  have htrace : WordTrace (prefixWord ++ tailWord_2441213) baseStart_2441213 baseEnd_2441213 := by
    simpa [prefixWord, tailWord_2441213, baseEnd_2441213] using wordTrace_append hprefix tailTrace_2441213
  have hstable : (prefixWord ++ tailWord_2441213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441213).length < 2 ^ (prefixWord ++ tailWord_2441213).sum := by decide
  have hdescent : baseEnd_2441213 < baseStart_2441213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441262 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2441262 : Nat := 118140960795 + 2441262 * 2 ^ 59
def prefixEnd_2441262 : Nat := 4983230072969 + 3 ^ 40 * 2441262 * 2
def baseEnd_2441262 : Nat := 835693873037688523265231

theorem tailTrace_2441262 : CollatzResearch.WordTrace tailWord_2441262 prefixEnd_2441262 835693873037688523265231 := by
  unfold tailWord_2441262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11130017510216522900108755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59360093387821455467246693 11130017510216522900108755)
  ·
    refine ⟨16695026265324784350163133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11130017510216522900108755 16695026265324784350163133)
    ·
      refine ⟨6260634849496794131311175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16695026265324784350163133 6260634849496794131311175)
      ·
        refine ⟨9390952274245191196966763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6260634849496794131311175 9390952274245191196966763)
        ·
          refine ⟨14086428411367786795450145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9390952274245191196966763 14086428411367786795450145)
          ·
            refine ⟨10564821308525840096587609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14086428411367786795450145 10564821308525840096587609)
            ·
              refine ⟨7923615981394380072440707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10564821308525840096587609 7923615981394380072440707)
              ·
                refine ⟨11885423972091570108661061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7923615981394380072440707 11885423972091570108661061)
                ·
                  refine ⟨2228516994767169395373949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11885423972091570108661061 2228516994767169395373949)
                  ·
                    refine ⟨835693873037688523265231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228516994767169395373949 835693873037688523265231)
                    ·
                      rfl

theorem cell22_2441262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2441262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441262 prefixEnd_2441262 := by exact prefixLift 2441262
  have htrace : WordTrace (prefixWord ++ tailWord_2441262) baseStart_2441262 baseEnd_2441262 := by
    simpa [prefixWord, tailWord_2441262, baseEnd_2441262] using wordTrace_append hprefix tailTrace_2441262
  have hstable : (prefixWord ++ tailWord_2441262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441262).length < 2 ^ (prefixWord ++ tailWord_2441262).sum := by decide
  have hdescent : baseEnd_2441262 < baseStart_2441262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441288 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 4, 6]
def baseStart_2441288 : Nat := 118140960795 + 2441288 * 2 ^ 59
def prefixEnd_2441288 : Nat := 4983230072969 + 3 ^ 40 * 2441288 * 2
def baseEnd_2441288 : Nat := 835702773369033122115151

theorem tailTrace_2441288 : CollatzResearch.WordTrace tailWord_2441288 prefixEnd_2441288 835702773369033122115151 := by
  unfold tailWord_2441288
  simp only [CollatzResearch.WordTrace]
  refine ⟨44520544189818994820658259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59360725586425326427544345 44520544189818994820658259)
  ·
    refine ⟨66780816284728492230987389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44520544189818994820658259 66780816284728492230987389)
    ·
      refine ⟨25042806106773184586620271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66780816284728492230987389 25042806106773184586620271)
      ·
        refine ⟨37564209160159776879930407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25042806106773184586620271 37564209160159776879930407)
        ·
          refine ⟨56346313740239665319895611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37564209160159776879930407 56346313740239665319895611)
          ·
            refine ⟨84519470610359497979843417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56346313740239665319895611 84519470610359497979843417)
            ·
              refine ⟨63389602957769623484882563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84519470610359497979843417 63389602957769623484882563)
              ·
                refine ⟨95084404436654435227323845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63389602957769623484882563 95084404436654435227323845)
                ·
                  refine ⟨17828325831872706605123221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95084404436654435227323845 17828325831872706605123221)
                  ·
                    refine ⟨835702773369033122115151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17828325831872706605123221 835702773369033122115151)
                    ·
                      rfl

theorem cell22_2441288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_2441288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441288 prefixEnd_2441288 := by exact prefixLift 2441288
  have htrace : WordTrace (prefixWord ++ tailWord_2441288) baseStart_2441288 baseEnd_2441288 := by
    simpa [prefixWord, tailWord_2441288, baseEnd_2441288] using wordTrace_append hprefix tailTrace_2441288
  have hstable : (prefixWord ++ tailWord_2441288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441288).length < 2 ^ (prefixWord ++ tailWord_2441288).sum := by decide
  have hdescent : baseEnd_2441288 < baseStart_2441288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441290 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_2441290 : Nat := 118140960795 + 2441290 * 2 ^ 59
def prefixEnd_2441290 : Nat := 4983230072969 + 3 ^ 40 * 2441290 * 2
def baseEnd_2441290 : Nat := 835703458009905783565145

theorem tailTrace_2441290 : CollatzResearch.WordTrace tailWord_2441290 prefixEnd_2441290 835703458009905783565145 := by
  unfold tailWord_2441290
  simp only [CollatzResearch.WordTrace]
  refine ⟨22260290331407685995722331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59360774217087162655259549 22260290331407685995722331)
  ·
    refine ⟨33390435497111528993583497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22260290331407685995722331 33390435497111528993583497)
    ·
      refine ⟨25042826622833646745187623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33390435497111528993583497 25042826622833646745187623)
      ·
        refine ⟨37564239934250470117781435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25042826622833646745187623 37564239934250470117781435)
        ·
          refine ⟨56346359901375705176672153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37564239934250470117781435 56346359901375705176672153)
          ·
            refine ⟨42259769926031778882504115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56346359901375705176672153 42259769926031778882504115)
            ·
              refine ⟨63389654889047668323756173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42259769926031778882504115 63389654889047668323756173)
              ·
                refine ⟨23771120583392875621408565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63389654889047668323756173 23771120583392875621408565)
                ·
                  refine ⟨2228542554693082089507053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23771120583392875621408565 2228542554693082089507053)
                  ·
                    refine ⟨835703458009905783565145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228542554693082089507053 835703458009905783565145)
                    ·
                      rfl

theorem cell22_2441290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_2441290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441290 prefixEnd_2441290 := by exact prefixLift 2441290
  have htrace : WordTrace (prefixWord ++ tailWord_2441290) baseStart_2441290 baseEnd_2441290 := by
    simpa [prefixWord, tailWord_2441290, baseEnd_2441290] using wordTrace_append hprefix tailTrace_2441290
  have hstable : (prefixWord ++ tailWord_2441290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441290).length < 2 ^ (prefixWord ++ tailWord_2441290).sum := by decide
  have hdescent : baseEnd_2441290 < baseStart_2441290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441303 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 9]
def baseStart_2441303 : Nat := 118140960795 + 2441303 * 2 ^ 59
def prefixEnd_2441303 : Nat := 4983230072969 + 3 ^ 40 * 2441303 * 2
def baseEnd_2441303 : Nat := 278569302725192694330035

theorem tailTrace_2441303 : CollatzResearch.WordTrace tailWord_2441303 prefixEnd_2441303 278569302725192694330035 := by
  unfold tailWord_2441303
  simp only [CollatzResearch.WordTrace]
  refine ⟨89041635474583647203112563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59361090316389098135408375 89041635474583647203112563)
  ·
    refine ⟨133562453211875470804668845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89041635474583647203112563 133562453211875470804668845)
    ·
      refine ⟨50085919954453301551750817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133562453211875470804668845 50085919954453301551750817)
      ·
        refine ⟨37564439965839976163813113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50085919954453301551750817 37564439965839976163813113)
        ·
          refine ⟨28173329974379982122859835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37564439965839976163813113 28173329974379982122859835)
          ·
            refine ⟨42259994961569973184289753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28173329974379982122859835 42259994961569973184289753)
            ·
              refine ⟨31694996221177479888217315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42259994961569973184289753 31694996221177479888217315)
              ·
                refine ⟨47542494331766219832325973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31694996221177479888217315 47542494331766219832325973)
                ·
                  refine ⟨278569302725192694330035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47542494331766219832325973 278569302725192694330035)
                  ·
                    rfl

theorem cell22_2441303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 9].length) (baseStart_2441303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441303 prefixEnd_2441303 := by exact prefixLift 2441303
  have htrace : WordTrace (prefixWord ++ tailWord_2441303) baseStart_2441303 baseEnd_2441303 := by
    simpa [prefixWord, tailWord_2441303, baseEnd_2441303] using wordTrace_append hprefix tailTrace_2441303
  have hstable : (prefixWord ++ tailWord_2441303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441303).length < 2 ^ (prefixWord ++ tailWord_2441303).sum := by decide
  have hdescent : baseEnd_2441303 < baseStart_2441303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441324 : List Nat := [2, 2, 1, 1, 3, 4, 1, 4, 1, 3]
def baseStart_2441324 : Nat := 118140960795 + 2441324 * 2 ^ 59
def prefixEnd_2441324 : Nat := 4983230072969 + 3 ^ 40 * 2441324 * 2
def baseEnd_2441324 : Nat := 835715096904741028215041

theorem tailTrace_2441324 : CollatzResearch.WordTrace tailWord_2441324 prefixEnd_2441324 835715096904741028215041 := by
  unfold tailWord_2441324
  simp only [CollatzResearch.WordTrace]
  refine ⟨44521200703753783894813513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59361600938338378526418017 44521200703753783894813513)
  ·
    refine ⟨33390900527815337921110135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44521200703753783894813513 33390900527815337921110135)
    ·
      refine ⟨50086350791723006881665203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33390900527815337921110135 50086350791723006881665203)
      ·
        refine ⟨75129526187584510322497805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50086350791723006881665203 75129526187584510322497805)
        ·
          refine ⟨28173572320344191370936677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75129526187584510322497805 28173572320344191370936677)
          ·
            refine ⟨5282544810064535882050627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28173572320344191370936677 5282544810064535882050627)
            ·
              refine ⟨7923817215096803823075941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282544810064535882050627 7923817215096803823075941)
              ·
                refine ⟨1485715727830650716826739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7923817215096803823075941 1485715727830650716826739)
                ·
                  refine ⟨2228573591745976075240109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1485715727830650716826739 2228573591745976075240109)
                  ·
                    refine ⟨835715096904741028215041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228573591745976075240109 835715096904741028215041)
                    ·
                      rfl

theorem cell22_2441324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 1, 3].length) (baseStart_2441324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441324 prefixEnd_2441324 := by exact prefixLift 2441324
  have htrace : WordTrace (prefixWord ++ tailWord_2441324) baseStart_2441324 baseEnd_2441324 := by
    simpa [prefixWord, tailWord_2441324, baseEnd_2441324] using wordTrace_append hprefix tailTrace_2441324
  have hstable : (prefixWord ++ tailWord_2441324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441324).length < 2 ^ (prefixWord ++ tailWord_2441324).sum := by decide
  have hdescent : baseEnd_2441324 < baseStart_2441324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441335 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 2, 5]
def baseStart_2441335 : Nat := 118140960795 + 2441335 * 2 ^ 59
def prefixEnd_2441335 : Nat := 4983230072969 + 3 ^ 40 * 2441335 * 2
def baseEnd_2441335 : Nat := 835718862429540666190007

theorem tailTrace_2441335 : CollatzResearch.WordTrace tailWord_2441335 prefixEnd_2441335 835718862429540666190007 := by
  unfold tailWord_2441335
  simp only [CollatzResearch.WordTrace]
  refine ⟨89042802610467716668277459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59361868406978477778851639 89042802610467716668277459)
  ·
    refine ⟨133564203915701575002416189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89042802610467716668277459 133564203915701575002416189)
    ·
      refine ⟨50086576468388090625906071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133564203915701575002416189 50086576468388090625906071)
      ·
        refine ⟨75129864702582135938859107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50086576468388090625906071 75129864702582135938859107)
        ·
          refine ⟨112694797053873203908288661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75129864702582135938859107 112694797053873203908288661)
          ·
            refine ⟨5282568611900306433201031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112694797053873203908288661 5282568611900306433201031)
            ·
              refine ⟨7923852917850459649801547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282568611900306433201031 7923852917850459649801547)
              ·
                refine ⟨11885779376775689474702321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7923852917850459649801547 11885779376775689474702321)
                ·
                  refine ⟨8914334532581767106026741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11885779376775689474702321 8914334532581767106026741)
                  ·
                    refine ⟨835718862429540666190007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8914334532581767106026741 835718862429540666190007)
                    ·
                      rfl

theorem cell22_2441335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_2441335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441335 prefixEnd_2441335 := by exact prefixLift 2441335
  have htrace : WordTrace (prefixWord ++ tailWord_2441335) baseStart_2441335 baseEnd_2441335 := by
    simpa [prefixWord, tailWord_2441335, baseEnd_2441335] using wordTrace_append hprefix tailTrace_2441335
  have hstable : (prefixWord ++ tailWord_2441335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441335).length < 2 ^ (prefixWord ++ tailWord_2441335).sum := by decide
  have hdescent : baseEnd_2441335 < baseStart_2441335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441412 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2441412 : Nat := 118140960795 + 2441412 * 2 ^ 59
def prefixEnd_2441412 : Nat := 4983230072969 + 3 ^ 40 * 2441412 * 2
def baseEnd_2441412 : Nat := 835745221103138132014771

theorem tailTrace_2441412 : CollatzResearch.WordTrace tailWord_2441412 prefixEnd_2441412 835745221103138132014771 := by
  unfold tailWord_2441412
  simp only [CollatzResearch.WordTrace]
  refine ⟨44522805515594379409415245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59363740687459172545886993 44522805515594379409415245)
  ·
    refine ⟨16696052068347892278530717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44522805515594379409415245 16696052068347892278530717)
    ·
      refine ⟨6261019525630459604449019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16696052068347892278530717 6261019525630459604449019)
      ·
        refine ⟨9391529288445689406673529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261019525630459604449019 9391529288445689406673529)
        ·
          refine ⟨7043646966334267055005147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9391529288445689406673529 7043646966334267055005147)
          ·
            refine ⟨10565470449501400582507721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7043646966334267055005147 10565470449501400582507721)
            ·
              refine ⟨7924102837126050436880791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10565470449501400582507721 7924102837126050436880791)
              ·
                refine ⟨11886154255689075655321187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7924102837126050436880791 11886154255689075655321187)
                ·
                  refine ⟨17829231383533613482981781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11886154255689075655321187 17829231383533613482981781)
                  ·
                    refine ⟨835745221103138132014771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17829231383533613482981781 835745221103138132014771)
                    ·
                      rfl

theorem cell22_2441412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2441412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441412 prefixEnd_2441412 := by exact prefixLift 2441412
  have htrace : WordTrace (prefixWord ++ tailWord_2441412) baseStart_2441412 baseEnd_2441412 := by
    simpa [prefixWord, tailWord_2441412, baseEnd_2441412] using wordTrace_append hprefix tailTrace_2441412
  have hstable : (prefixWord ++ tailWord_2441412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441412).length < 2 ^ (prefixWord ++ tailWord_2441412).sum := by decide
  have hdescent : baseEnd_2441412 < baseStart_2441412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441429 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2441429 : Nat := 118140960795 + 2441429 * 2 ^ 59
def prefixEnd_2441429 : Nat := 4983230072969 + 3 ^ 40 * 2441429 * 2
def baseEnd_2441429 : Nat := 835751040550555754339719

theorem tailTrace_2441429 : CollatzResearch.WordTrace tailWord_2441429 prefixEnd_2441429 835751040550555754339719 := by
  unfold tailWord_2441429
  simp only [CollatzResearch.WordTrace]
  refine ⟨89046231072127170722199341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59364154048084780481466227 89046231072127170722199341)
  ·
    refine ⟨33392336652047689020824753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89046231072127170722199341 33392336652047689020824753)
    ·
      refine ⟨25044252489035766765618565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33392336652047689020824753 25044252489035766765618565)
      ·
        refine ⟨4695797341694206268553481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25044252489035766765618565 4695797341694206268553481)
        ·
          refine ⟨3521848006270654701415111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4695797341694206268553481 3521848006270654701415111)
          ·
            refine ⟨5282772009405982052122667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521848006270654701415111 5282772009405982052122667)
            ·
              refine ⟨7924158014108973078184001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5282772009405982052122667 7924158014108973078184001)
              ·
                refine ⟨5943118510581729808638001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7924158014108973078184001 5943118510581729808638001)
                ·
                  refine ⟨4457338882936297356478501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5943118510581729808638001 4457338882936297356478501)
                  ·
                    refine ⟨835751040550555754339719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4457338882936297356478501 835751040550555754339719)
                    ·
                      rfl

theorem cell22_2441429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2441429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441429 prefixEnd_2441429 := by exact prefixLift 2441429
  have htrace : WordTrace (prefixWord ++ tailWord_2441429) baseStart_2441429 baseEnd_2441429 := by
    simpa [prefixWord, tailWord_2441429, baseEnd_2441429] using wordTrace_append hprefix tailTrace_2441429
  have hstable : (prefixWord ++ tailWord_2441429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441429).length < 2 ^ (prefixWord ++ tailWord_2441429).sum := by decide
  have hdescent : baseEnd_2441429 < baseStart_2441429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441440 : List Nat := [2, 1, 1, 3, 1, 3, 2, 1, 2, 6]
def baseStart_2441440 : Nat := 118140960795 + 2441440 * 2 ^ 59
def prefixEnd_2441440 : Nat := 4983230072969 + 3 ^ 40 * 2441440 * 2
def baseEnd_2441440 : Nat := 835754806075355392314685

theorem tailTrace_2441440 : CollatzResearch.WordTrace tailWord_2441440 prefixEnd_2441440 835754806075355392314685 := by
  unfold tailWord_2441440
  simp only [CollatzResearch.WordTrace]
  refine ⟨44523316137543659800424887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59364421516724879733899849 44523316137543659800424887)
  ·
    refine ⟨66784974206315489700637331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44523316137543659800424887 66784974206315489700637331)
    ·
      refine ⟨100177461309473234550955997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66784974206315489700637331 100177461309473234550955997)
      ·
        refine ⟨37566547991052462956608499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100177461309473234550955997 37566547991052462956608499)
        ·
          refine ⟨56349821986578694434912749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37566547991052462956608499 56349821986578694434912749)
          ·
            refine ⟨21131183244967010413092281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56349821986578694434912749 21131183244967010413092281)
            ·
              refine ⟨15848387433725257809819211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21131183244967010413092281 15848387433725257809819211)
              ·
                refine ⟨23772581150587886714728817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15848387433725257809819211 23772581150587886714728817)
                ·
                  refine ⟨17829435862940915036046613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23772581150587886714728817 17829435862940915036046613)
                  ·
                    refine ⟨835754806075355392314685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17829435862940915036046613 835754806075355392314685)
                    ·
                      rfl

theorem cell22_2441440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_2441440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441440 prefixEnd_2441440 := by exact prefixLift 2441440
  have htrace : WordTrace (prefixWord ++ tailWord_2441440) baseStart_2441440 baseEnd_2441440 := by
    simpa [prefixWord, tailWord_2441440, baseEnd_2441440] using wordTrace_append hprefix tailTrace_2441440
  have hstable : (prefixWord ++ tailWord_2441440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441440).length < 2 ^ (prefixWord ++ tailWord_2441440).sum := by decide
  have hdescent : baseEnd_2441440 < baseStart_2441440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441532 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2441532 : Nat := 118140960795 + 2441532 * 2 ^ 59
def prefixEnd_2441532 : Nat := 4983230072969 + 3 ^ 40 * 2441532 * 2
def baseEnd_2441532 : Nat := 835786299555497819014403

theorem tailTrace_2441532 : CollatzResearch.WordTrace tailWord_2441532 prefixEnd_2441532 835786299555497819014403 := by
  unfold tailWord_2441532
  simp only [CollatzResearch.WordTrace]
  refine ⟨44524993895377009656599425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59366658527169346208799233 44524993895377009656599425)
  ·
    refine ⟨33393745421532757242449569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44524993895377009656599425 33393745421532757242449569)
    ·
      refine ⟨25045309066149567931837177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33393745421532757242449569 25045309066149567931837177)
      ·
        refine ⟨18783981799612175948877883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25045309066149567931837177 18783981799612175948877883)
        ·
          refine ⟨28175972699418263923316825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18783981799612175948877883 28175972699418263923316825)
          ·
            refine ⟨21131979524563697942487619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28175972699418263923316825 21131979524563697942487619)
            ·
              refine ⟨31697969286845546913731429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21131979524563697942487619 31697969286845546913731429)
              ·
                refine ⟨5943369241283540046324643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31697969286845546913731429 5943369241283540046324643)
                ·
                  refine ⟨8915053861925310069486965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5943369241283540046324643 8915053861925310069486965)
                  ·
                    refine ⟨835786299555497819014403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8915053861925310069486965 835786299555497819014403)
                    ·
                      rfl

theorem cell22_2441532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2441532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441532 prefixEnd_2441532 := by exact prefixLift 2441532
  have htrace : WordTrace (prefixWord ++ tailWord_2441532) baseStart_2441532 baseEnd_2441532 := by
    simpa [prefixWord, tailWord_2441532, baseEnd_2441532] using wordTrace_append hprefix tailTrace_2441532
  have hstable : (prefixWord ++ tailWord_2441532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441532).length < 2 ^ (prefixWord ++ tailWord_2441532).sum := by decide
  have hdescent : baseEnd_2441532 < baseStart_2441532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441607 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 7]
def baseStart_2441607 : Nat := 118140960795 + 2441607 * 2 ^ 59
def prefixEnd_2441607 : Nat := 4983230072969 + 3 ^ 40 * 2441607 * 2
def baseEnd_2441607 : Nat := 278603991196074207796391

theorem tailTrace_2441607 : CollatzResearch.WordTrace tailWord_2441607 prefixEnd_2441607 278603991196074207796391 := by
  unfold tailWord_2441607
  simp only [CollatzResearch.WordTrace]
  refine ⟨89052723265482307122179075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59368482176988204748119383 89052723265482307122179075)
  ·
    refine ⟨133579084898223460683268613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89052723265482307122179075 133579084898223460683268613)
    ·
      refine ⟨25046078418416898878112865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133579084898223460683268613 25046078418416898878112865)
      ·
        refine ⟨18784558813812674158584649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25046078418416898878112865 18784558813812674158584649)
        ·
          refine ⟨14088419110359505618938487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18784558813812674158584649 14088419110359505618938487)
          ·
            refine ⟨21132628665539258428407731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14088419110359505618938487 21132628665539258428407731)
            ·
              refine ⟨31698942998308887642611597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21132628665539258428407731 31698942998308887642611597)
              ·
                refine ⟨11887103624365832865979349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31698942998308887642611597 11887103624365832865979349)
                ·
                  refine ⟨278603991196074207796391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11887103624365832865979349 278603991196074207796391)
                  ·
                    rfl

theorem cell22_2441607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 7].length) (baseStart_2441607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441607 prefixEnd_2441607 := by exact prefixLift 2441607
  have htrace : WordTrace (prefixWord ++ tailWord_2441607) baseStart_2441607 baseEnd_2441607 := by
    simpa [prefixWord, tailWord_2441607, baseEnd_2441607] using wordTrace_append hprefix tailTrace_2441607
  have hstable : (prefixWord ++ tailWord_2441607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441607).length < 2 ^ (prefixWord ++ tailWord_2441607).sum := by decide
  have hdescent : baseEnd_2441607 < baseStart_2441607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441611 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 3, 3]
def baseStart_2441611 : Nat := 118140960795 + 2441611 * 2 ^ 59
def prefixEnd_2441611 : Nat := 4983230072969 + 3 ^ 40 * 2441611 * 2
def baseEnd_2441611 : Nat := 835813342869967946289161

theorem tailTrace_2441611 : CollatzResearch.WordTrace tailWord_2441611 prefixEnd_2441611 835813342869967946289161 := by
  unfold tailWord_2441611
  simp only [CollatzResearch.WordTrace]
  refine ⟨89052869157467815805324687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59368579438311877203549791 89052869157467815805324687)
  ·
    refine ⟨133579303736201723707987031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89052869157467815805324687 133579303736201723707987031)
    ·
      refine ⟨200368955604302585561980547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133579303736201723707987031 200368955604302585561980547)
      ·
        refine ⟨300553433406453878342970821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200368955604302585561980547 300553433406453878342970821)
        ·
          refine ⟨56353768763710102189307029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300553433406453878342970821 56353768763710102189307029)
          ·
            refine ⟨2641582910798911040123767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56353768763710102189307029 2641582910798911040123767)
            ·
              refine ⟨3962374366198366560185651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641582910798911040123767 3962374366198366560185651)
              ·
                refine ⟨5943561549297549840278477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962374366198366560185651 5943561549297549840278477)
                ·
                  refine ⟨2228835580986581190104429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5943561549297549840278477 2228835580986581190104429)
                  ·
                    refine ⟨835813342869967946289161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228835580986581190104429 835813342869967946289161)
                    ·
                      rfl

theorem cell22_2441611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 3].length) (baseStart_2441611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441611 prefixEnd_2441611 := by exact prefixLift 2441611
  have htrace : WordTrace (prefixWord ++ tailWord_2441611) baseStart_2441611 baseEnd_2441611 := by
    simpa [prefixWord, tailWord_2441611, baseEnd_2441611] using wordTrace_append hprefix tailTrace_2441611
  have hstable : (prefixWord ++ tailWord_2441611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441611).length < 2 ^ (prefixWord ++ tailWord_2441611).sum := by decide
  have hdescent : baseEnd_2441611 < baseStart_2441611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441667 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 5, 5]
def baseStart_2441667 : Nat := 118140960795 + 2441667 * 2 ^ 59
def prefixEnd_2441667 : Nat := 4983230072969 + 3 ^ 40 * 2441667 * 2
def baseEnd_2441667 : Nat := 835832512814402466888989

theorem tailTrace_2441667 : CollatzResearch.WordTrace tailWord_2441667 prefixEnd_2441667 835832512814402466888989 := by
  unfold tailWord_2441667
  simp only [CollatzResearch.WordTrace]
  refine ⟨89054911645264937369363255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59369941096843291579575503 89054911645264937369363255)
  ·
    refine ⟨133582367467897406054044883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89054911645264937369363255 133582367467897406054044883)
    ·
      refine ⟨200373551201846109081067325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133582367467897406054044883 200373551201846109081067325)
      ·
        refine ⟨75140081700692290905400247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200373551201846109081067325 75140081700692290905400247)
        ·
          refine ⟨112710122551038436358100371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75140081700692290905400247 112710122551038436358100371)
          ·
            refine ⟨169065183826557654537150557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112710122551038436358100371 169065183826557654537150557)
            ·
              refine ⟨63399443934959120451431459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169065183826557654537150557 63399443934959120451431459)
              ·
                refine ⟨95099165902438680677147189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63399443934959120451431459 95099165902438680677147189)
                ·
                  refine ⟨8915546803353626313482549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95099165902438680677147189 8915546803353626313482549)
                  ·
                    refine ⟨835832512814402466888989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8915546803353626313482549 835832512814402466888989)
                    ·
                      rfl

theorem cell22_2441667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_2441667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441667 prefixEnd_2441667 := by exact prefixLift 2441667
  have htrace : WordTrace (prefixWord ++ tailWord_2441667) baseStart_2441667 baseEnd_2441667 := by
    simpa [prefixWord, tailWord_2441667, baseEnd_2441667] using wordTrace_append hprefix tailTrace_2441667
  have hstable : (prefixWord ++ tailWord_2441667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441667).length < 2 ^ (prefixWord ++ tailWord_2441667).sum := by decide
  have hdescent : baseEnd_2441667 < baseStart_2441667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441686 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2441686 : Nat := 118140960795 + 2441686 * 2 ^ 59
def prefixEnd_2441686 : Nat := 4983230072969 + 3 ^ 40 * 2441686 * 2
def baseEnd_2441686 : Nat := 278613005634230916887977

theorem tailTrace_2441686 : CollatzResearch.WordTrace tailWord_2441686 prefixEnd_2441686 278613005634230916887977 := by
  unfold tailWord_2441686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565975289512256475894057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59370403088130735742869941 5565975289512256475894057)
  ·
    refine ⟨4174481467134192356920543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5565975289512256475894057 4174481467134192356920543)
    ·
      refine ⟨6261722200701288535380815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4174481467134192356920543 6261722200701288535380815)
      ·
        refine ⟨9392583301051932803071223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261722200701288535380815 9392583301051932803071223)
        ·
          refine ⟨14088874951577899204606835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9392583301051932803071223 14088874951577899204606835)
          ·
            refine ⟨21133312427366848806910253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14088874951577899204606835 21133312427366848806910253)
            ·
              refine ⟨7924992160262568302591345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21133312427366848806910253 7924992160262568302591345)
              ·
                refine ⟨5943744120196926226943509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7924992160262568302591345 5943744120196926226943509)
                ·
                  refine ⟨278613005634230916887977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5943744120196926226943509 278613005634230916887977)
                  ·
                    rfl

theorem cell22_2441686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2441686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441686 prefixEnd_2441686 := by exact prefixLift 2441686
  have htrace : WordTrace (prefixWord ++ tailWord_2441686) baseStart_2441686 baseEnd_2441686 := by
    simpa [prefixWord, tailWord_2441686, baseEnd_2441686] using wordTrace_append hprefix tailTrace_2441686
  have hstable : (prefixWord ++ tailWord_2441686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441686).length < 2 ^ (prefixWord ++ tailWord_2441686).sum := by decide
  have hdescent : baseEnd_2441686 < baseStart_2441686 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441735 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 2, 3]
def baseStart_2441735 : Nat := 118140960795 + 2441735 * 2 ^ 59
def prefixEnd_2441735 : Nat := 4983230072969 + 3 ^ 40 * 2441735 * 2
def baseEnd_2441735 : Nat := 835855790604072956188781

theorem tailTrace_2441735 : CollatzResearch.WordTrace tailWord_2441735 prefixEnd_2441735 835855790604072956188781 := by
  unfold tailWord_2441735
  simp only [CollatzResearch.WordTrace]
  refine ⟨89057391809018584982838659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59371594539345723321892439 89057391809018584982838659)
  ·
    refine ⟨133586087713527877474257989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89057391809018584982838659 133586087713527877474257989)
    ·
      refine ⟨25047391446286477026423373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133586087713527877474257989 25047391446286477026423373)
      ·
        refine ⟨9392771792357428884908765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25047391446286477026423373 9392771792357428884908765)
        ·
          refine ⟨3522289422134035831840787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9392771792357428884908765 3522289422134035831840787)
          ·
            refine ⟨5283434133201053747761181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522289422134035831840787 5283434133201053747761181)
            ·
              refine ⟨1981287799950395155410443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5283434133201053747761181 1981287799950395155410443)
              ·
                refine ⟨2971931699925592733115665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981287799950395155410443 2971931699925592733115665)
                ·
                  refine ⟨2228948774944194549836749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2971931699925592733115665 2228948774944194549836749)
                  ·
                    refine ⟨835855790604072956188781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2228948774944194549836749 835855790604072956188781)
                    ·
                      rfl

theorem cell22_2441735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_2441735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441735 prefixEnd_2441735 := by exact prefixLift 2441735
  have htrace : WordTrace (prefixWord ++ tailWord_2441735) baseStart_2441735 baseEnd_2441735 := by
    simpa [prefixWord, tailWord_2441735, baseEnd_2441735] using wordTrace_append hprefix tailTrace_2441735
  have hstable : (prefixWord ++ tailWord_2441735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441735).length < 2 ^ (prefixWord ++ tailWord_2441735).sum := by decide
  have hdescent : baseEnd_2441735 < baseStart_2441735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441748 : List Nat := [2, 4, 3, 1, 1, 1, 4, 6]
def baseStart_2441748 : Nat := 118140960795 + 2441748 * 2 ^ 59
def prefixEnd_2441748 : Nat := 4983230072969 + 3 ^ 40 * 2441748 * 2
def baseEnd_2441748 : Nat := 92873360085527250623749

theorem tailTrace_2441748 : CollatzResearch.WordTrace tailWord_2441748 prefixEnd_2441748 92873360085527250623749 := by
  unfold tailWord_2441748
  simp only [CollatzResearch.WordTrace]
  refine ⟨44528932978985744101530949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59371910638647658802041265 44528932978985744101530949)
  ·
    refine ⟨8349174933559827019037053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44528932978985744101530949 8349174933559827019037053)
    ·
      refine ⟨3130940600084935132138895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8349174933559827019037053 3130940600084935132138895)
      ·
        refine ⟨4696410900127402698208343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3130940600084935132138895 4696410900127402698208343)
        ·
          refine ⟨7044616350191104047312515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4696410900127402698208343 7044616350191104047312515)
          ·
            refine ⟨10566924525286656070968773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7044616350191104047312515 10566924525286656070968773)
            ·
              refine ⟨1981298348491248013306645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10566924525286656070968773 1981298348491248013306645)
              ·
                refine ⟨92873360085527250623749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1981298348491248013306645 92873360085527250623749)
                ·
                  rfl

theorem cell22_2441748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 6].length) (baseStart_2441748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441748 prefixEnd_2441748 := by exact prefixLift 2441748
  have htrace : WordTrace (prefixWord ++ tailWord_2441748) baseStart_2441748 baseEnd_2441748 := by
    simpa [prefixWord, tailWord_2441748, baseEnd_2441748] using wordTrace_append hprefix tailTrace_2441748
  have hstable : (prefixWord ++ tailWord_2441748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441748).length < 2 ^ (prefixWord ++ tailWord_2441748).sum := by decide
  have hdescent : baseEnd_2441748 < baseStart_2441748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441793 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 5]
def baseStart_2441793 : Nat := 118140960795 + 2441793 * 2 ^ 59
def prefixEnd_2441793 : Nat := 4983230072969 + 3 ^ 40 * 2441793 * 2
def baseEnd_2441793 : Nat := 278625215063126712746201

theorem tailTrace_2441793 : CollatzResearch.WordTrace tailWord_2441793 prefixEnd_2441793 278625215063126712746201 := by
  unfold tailWord_2441793
  simp only [CollatzResearch.WordTrace]
  refine ⟨89059507242808460888450033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59373004828538973925633355 89059507242808460888450033)
  ·
    refine ⟨66794630432106345666337525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89059507242808460888450033 66794630432106345666337525)
    ·
      refine ⟨6261996603009969906219143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66794630432106345666337525 6261996603009969906219143)
      ·
        refine ⟨9392994904514954859328715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6261996603009969906219143 9392994904514954859328715)
        ·
          refine ⟨14089492356772432288993073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9392994904514954859328715 14089492356772432288993073)
          ·
            refine ⟨10567119267579324216744805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14089492356772432288993073 10567119267579324216744805)
            ·
              refine ⟨1981334862671123290639651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10567119267579324216744805 1981334862671123290639651)
              ·
                refine ⟨2972002294006684935959477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981334862671123290639651 2972002294006684935959477)
                ·
                  refine ⟨278625215063126712746201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2972002294006684935959477 278625215063126712746201)
                  ·
                    rfl

theorem cell22_2441793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_2441793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441793 prefixEnd_2441793 := by exact prefixLift 2441793
  have htrace : WordTrace (prefixWord ++ tailWord_2441793) baseStart_2441793 baseEnd_2441793 := by
    simpa [prefixWord, tailWord_2441793, baseEnd_2441793] using wordTrace_append hprefix tailTrace_2441793
  have hstable : (prefixWord ++ tailWord_2441793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441793).length < 2 ^ (prefixWord ++ tailWord_2441793).sum := by decide
  have hdescent : baseEnd_2441793 < baseStart_2441793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441804 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 8]
def baseStart_2441804 : Nat := 118140960795 + 2441804 * 2 ^ 59
def prefixEnd_2441804 : Nat := 4983230072969 + 3 ^ 40 * 2441804 * 2
def baseEnd_2441804 : Nat := 278626470238059925404523

theorem tailTrace_2441804 : CollatzResearch.WordTrace tailWord_2441804 prefixEnd_2441804 278626470238059925404523 := by
  unfold tailWord_2441804
  simp only [CollatzResearch.WordTrace]
  refine ⟨44529954222884304883550233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59373272297179073178066977 44529954222884304883550233)
  ·
    refine ⟨33397465667163228662662675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44529954222884304883550233 33397465667163228662662675)
    ·
      refine ⟨50096198500744842993994013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33397465667163228662662675 50096198500744842993994013)
      ·
        refine ⟨18786074437779316122747755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50096198500744842993994013 18786074437779316122747755)
        ·
          refine ⟨28179111656668974184121633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18786074437779316122747755 28179111656668974184121633)
          ·
            refine ⟨21134333742501730638091225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28179111656668974184121633 21134333742501730638091225)
            ·
              refine ⟨15850750306876297978568419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21134333742501730638091225 15850750306876297978568419)
              ·
                refine ⟨23776125460314446967852629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15850750306876297978568419 23776125460314446967852629)
                ·
                  refine ⟨278626470238059925404523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23776125460314446967852629 278626470238059925404523)
                  ·
                    rfl

theorem cell22_2441804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_2441804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441804 prefixEnd_2441804 := by exact prefixLift 2441804
  have htrace : WordTrace (prefixWord ++ tailWord_2441804) baseStart_2441804 baseEnd_2441804 := by
    simpa [prefixWord, tailWord_2441804, baseEnd_2441804] using wordTrace_append hprefix tailTrace_2441804
  have hstable : (prefixWord ++ tailWord_2441804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441804).length < 2 ^ (prefixWord ++ tailWord_2441804).sum := by decide
  have hdescent : baseEnd_2441804 < baseStart_2441804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441836 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_2441836 : Nat := 118140960795 + 2441836 * 2 ^ 59
def prefixEnd_2441836 : Nat := 4983230072969 + 3 ^ 40 * 2441836 * 2
def baseEnd_2441836 : Nat := 835890364968142359413471

theorem tailTrace_2441836 : CollatzResearch.WordTrace tailWord_2441836 prefixEnd_2441836 835890364968142359413471 := by
  unfold tailWord_2441836
  simp only [CollatzResearch.WordTrace]
  refine ⟨44530537790826339616132681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59374050387768452821510241 44530537790826339616132681)
  ·
    refine ⟨33397903343119754712099511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44530537790826339616132681 33397903343119754712099511)
    ·
      refine ⟨50096855014679632068149267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33397903343119754712099511 50096855014679632068149267)
      ·
        refine ⟨75145282522019448102223901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50096855014679632068149267 75145282522019448102223901)
        ·
          refine ⟨28179480945757293038333963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75145282522019448102223901 28179480945757293038333963)
          ·
            refine ⟨42269221418635939557500945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28179480945757293038333963 42269221418635939557500945)
            ·
              refine ⟨31701916063976954668125709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42269221418635939557500945 31701916063976954668125709)
              ·
                refine ⟨11888218523991358000547141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31701916063976954668125709 11888218523991358000547141)
                ·
                  refine ⟨2229040973248379625102589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11888218523991358000547141 2229040973248379625102589)
                  ·
                    refine ⟨835890364968142359413471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229040973248379625102589 835890364968142359413471)
                    ·
                      rfl

theorem cell22_2441836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_2441836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441836 prefixEnd_2441836 := by exact prefixLift 2441836
  have htrace : WordTrace (prefixWord ++ tailWord_2441836) baseStart_2441836 baseEnd_2441836 := by
    simpa [prefixWord, tailWord_2441836, baseEnd_2441836] using wordTrace_append hprefix tailTrace_2441836
  have hstable : (prefixWord ++ tailWord_2441836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441836).length < 2 ^ (prefixWord ++ tailWord_2441836).sum := by decide
  have hdescent : baseEnd_2441836 < baseStart_2441836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441853 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2441853 : Nat := 118140960795 + 2441853 * 2 ^ 59
def prefixEnd_2441853 : Nat := 4983230072969 + 3 ^ 40 * 2441853 * 2
def baseEnd_2441853 : Nat := 835896184415559981738419

theorem tailTrace_2441853 : CollatzResearch.WordTrace tailWord_2441853 prefixEnd_2441853 835896184415559981738419 := by
  unfold tailWord_2441853
  simp only [CollatzResearch.WordTrace]
  refine ⟨89061695622591091135634213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59374463748394060757089475 89061695622591091135634213)
  ·
    refine ⟨16699067929235829587931415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89061695622591091135634213 16699067929235829587931415)
    ·
      refine ⟨25048601893853744381897123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16699067929235829587931415 25048601893853744381897123)
      ·
        refine ⟨37572902840780616572845685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25048601893853744381897123 37572902840780616572845685)
        ·
          refine ⟨3522459641323182803704283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37572902840780616572845685 3522459641323182803704283)
          ·
            refine ⟨5283689461984774205556425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522459641323182803704283 5283689461984774205556425)
            ·
              refine ⟨3962767096488580654167319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5283689461984774205556425 3962767096488580654167319)
              ·
                refine ⟨5944150644732870981250979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3962767096488580654167319 5944150644732870981250979)
                ·
                  refine ⟨8916225967099306471876469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5944150644732870981250979 8916225967099306471876469)
                  ·
                    refine ⟨835896184415559981738419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8916225967099306471876469 835896184415559981738419)
                    ·
                      rfl

theorem cell22_2441853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2441853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441853 prefixEnd_2441853 := by exact prefixLift 2441853
  have htrace : WordTrace (prefixWord ++ tailWord_2441853) baseStart_2441853 baseEnd_2441853 := by
    simpa [prefixWord, tailWord_2441853, baseEnd_2441853] using wordTrace_append hprefix tailTrace_2441853
  have hstable : (prefixWord ++ tailWord_2441853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441853).length < 2 ^ (prefixWord ++ tailWord_2441853).sum := by decide
  have hdescent : baseEnd_2441853 < baseStart_2441853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441881 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 5, 3]
def baseStart_2441881 : Nat := 118140960795 + 2441881 * 2 ^ 59
def prefixEnd_2441881 : Nat := 4983230072969 + 3 ^ 40 * 2441881 * 2
def baseEnd_2441881 : Nat := 835905769387777242038333

theorem tailTrace_2441881 : CollatzResearch.WordTrace tailWord_2441881 prefixEnd_2441881 835905769387777242038333 := by
  unfold tailWord_2441881
  simp only [CollatzResearch.WordTrace]
  refine ⟨89062716866489651917653497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59375144577659767945102331 89062716866489651917653497)
  ·
    refine ⟨66797037649867238938240123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89062716866489651917653497 66797037649867238938240123)
    ·
      refine ⟨100195556474800858407360185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66797037649867238938240123 100195556474800858407360185)
      ·
        refine ⟨75146667356100643805520139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100195556474800858407360185 75146667356100643805520139)
        ·
          refine ⟨112720001034150965708280209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75146667356100643805520139 112720001034150965708280209)
          ·
            refine ⟨84540000775613224281210157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112720001034150965708280209 84540000775613224281210157)
            ·
              refine ⟨31702500290854959105453809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84540000775613224281210157 31702500290854959105453809)
              ·
                refine ⟨23776875218141219329090357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31702500290854959105453809 23776875218141219329090357)
                ·
                  refine ⟨2229082051700739312102221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23776875218141219329090357 2229082051700739312102221)
                  ·
                    refine ⟨835905769387777242038333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229082051700739312102221 835905769387777242038333)
                    ·
                      rfl

theorem cell22_2441881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_2441881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441881 prefixEnd_2441881 := by exact prefixLift 2441881
  have htrace : WordTrace (prefixWord ++ tailWord_2441881) baseStart_2441881 baseEnd_2441881 := by
    simpa [prefixWord, tailWord_2441881, baseEnd_2441881] using wordTrace_append hprefix tailTrace_2441881
  have hstable : (prefixWord ++ tailWord_2441881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441881).length < 2 ^ (prefixWord ++ tailWord_2441881).sum := by decide
  have hdescent : baseEnd_2441881 < baseStart_2441881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441932 : List Nat := [2, 2, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_2441932 : Nat := 118140960795 + 2441932 * 2 ^ 59
def prefixEnd_2441932 : Nat := 4983230072969 + 3 ^ 40 * 2441932 * 2
def baseEnd_2441932 : Nat := 835923227730030109013177

theorem tailTrace_2441932 : CollatzResearch.WordTrace tailWord_2441932 prefixEnd_2441932 835923227730030109013177 := by
  unfold tailWord_2441932
  simp only [CollatzResearch.WordTrace]
  refine ⟨44532288494652443813880025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59376384659536591751840033 44532288494652443813880025)
  ·
    refine ⟨33399216370989332860410019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44532288494652443813880025 33399216370989332860410019)
    ·
      refine ⟨50098824556483999290615029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33399216370989332860410019 50098824556483999290615029)
      ·
        refine ⟨4696764802170374933495159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50098824556483999290615029 4696764802170374933495159)
        ·
          refine ⟨7045147203255562400242739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4696764802170374933495159 7045147203255562400242739)
          ·
            refine ⟨10567720804883343600364109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045147203255562400242739 10567720804883343600364109)
            ·
              refine ⟨3962895301831253850136541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10567720804883343600364109 3962895301831253850136541)
              ·
                refine ⟨1486085738186720193801203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3962895301831253850136541 1486085738186720193801203)
                ·
                  refine ⟨2229128607280080290701805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486085738186720193801203 2229128607280080290701805)
                  ·
                    refine ⟨835923227730030109013177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229128607280080290701805 835923227730030109013177)
                    ·
                      rfl

theorem cell22_2441932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_2441932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441932 prefixEnd_2441932 := by exact prefixLift 2441932
  have htrace : WordTrace (prefixWord ++ tailWord_2441932) baseStart_2441932 baseEnd_2441932 := by
    simpa [prefixWord, tailWord_2441932, baseEnd_2441932] using wordTrace_append hprefix tailTrace_2441932
  have hstable : (prefixWord ++ tailWord_2441932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441932).length < 2 ^ (prefixWord ++ tailWord_2441932).sum := by decide
  have hdescent : baseEnd_2441932 < baseStart_2441932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441971 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 1, 5]
def baseStart_2441971 : Nat := 118140960795 + 2441971 * 2 ^ 59
def prefixEnd_2441971 : Nat := 4983230072969 + 3 ^ 40 * 2441971 * 2
def baseEnd_2441971 : Nat := 835936578227047007288057

theorem tailTrace_2441971 : CollatzResearch.WordTrace tailWord_2441971 prefixEnd_2441971 835936578227047007288057 := by
  unfold tailWord_2441971
  simp only [CollatzResearch.WordTrace]
  refine ⟨89065999436163597288429767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59377332957442398192286511 89065999436163597288429767)
  ·
    refine ⟨133598999154245395932644651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89065999436163597288429767 133598999154245395932644651)
    ·
      refine ⟨200398498731368093898966977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133598999154245395932644651 200398498731368093898966977)
      ·
        refine ⟨150298874048526070424225233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200398498731368093898966977 150298874048526070424225233)
        ·
          refine ⟨112724155536394552818168925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150298874048526070424225233 112724155536394552818168925)
          ·
            refine ⟨42271558326147957306813347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112724155536394552818168925 42271558326147957306813347)
            ·
              refine ⟨63407337489221935960220021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42271558326147957306813347 63407337489221935960220021)
              ·
                refine ⟨5944437889614556496270627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63407337489221935960220021 5944437889614556496270627)
                ·
                  refine ⟨8916656834421834744405941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5944437889614556496270627 8916656834421834744405941)
                  ·
                    refine ⟨835936578227047007288057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8916656834421834744405941 835936578227047007288057)
                    ·
                      rfl

theorem cell22_2441971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_2441971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441971 prefixEnd_2441971 := by exact prefixLift 2441971
  have htrace : WordTrace (prefixWord ++ tailWord_2441971) baseStart_2441971 baseEnd_2441971 := by
    simpa [prefixWord, tailWord_2441971, baseEnd_2441971] using wordTrace_append hprefix tailTrace_2441971
  have hstable : (prefixWord ++ tailWord_2441971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441971).length < 2 ^ (prefixWord ++ tailWord_2441971).sum := by decide
  have hdescent : baseEnd_2441971 < baseStart_2441971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2441988 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2441988 : Nat := 118140960795 + 2441988 * 2 ^ 59
def prefixEnd_2441988 : Nat := 4983230072969 + 3 ^ 40 * 2441988 * 2
def baseEnd_2441988 : Nat := 835942397674464629613005

theorem tailTrace_2441988 : CollatzResearch.WordTrace tailWord_2441988 prefixEnd_2441988 835942397674464629613005 := by
  unfold tailWord_2441988
  simp only [CollatzResearch.WordTrace]
  refine ⟨44533309738551004595899309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59377746318068006127865745 44533309738551004595899309)
  ·
    refine ⟨16699991151956626723462241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44533309738551004595899309 16699991151956626723462241)
    ·
      refine ⟨12524993363967470042596681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16699991151956626723462241 12524993363967470042596681)
      ·
        refine ⟨9393745022975602531947511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12524993363967470042596681 9393745022975602531947511)
        ·
          refine ⟨14090617534463403797921267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9393745022975602531947511 14090617534463403797921267)
          ·
            refine ⟨21135926301695105696881901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14090617534463403797921267 21135926301695105696881901)
            ·
              refine ⟨7925972363135664636330713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21135926301695105696881901 7925972363135664636330713)
              ·
                refine ⟨5944479272351748477248035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7925972363135664636330713 5944479272351748477248035)
                ·
                  refine ⟨8916718908527622715872053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5944479272351748477248035 8916718908527622715872053)
                  ·
                    refine ⟨835942397674464629613005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8916718908527622715872053 835942397674464629613005)
                    ·
                      rfl

theorem cell22_2441988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2441988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2441988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2441988 prefixEnd_2441988 := by exact prefixLift 2441988
  have htrace : WordTrace (prefixWord ++ tailWord_2441988) baseStart_2441988 baseEnd_2441988 := by
    simpa [prefixWord, tailWord_2441988, baseEnd_2441988] using wordTrace_append hprefix tailTrace_2441988
  have hstable : (prefixWord ++ tailWord_2441988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2441988).length < 2 ^ (prefixWord ++ tailWord_2441988).sum := by decide
  have hdescent : baseEnd_2441988 < baseStart_2441988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2441988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442005 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_2442005 : Nat := 118140960795 + 2442005 * 2 ^ 59
def prefixEnd_2442005 : Nat := 4983230072969 + 3 ^ 40 * 2442005 * 2
def baseEnd_2442005 : Nat := 835948217121882251937953

theorem tailTrace_2442005 : CollatzResearch.WordTrace tailWord_2442005 prefixEnd_2442005 835948217121882251937953 := by
  unfold tailWord_2442005
  simp only [CollatzResearch.WordTrace]
  refine ⟨89067239518040421095167469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59378159678693614063444979 89067239518040421095167469)
  ·
    refine ⟨33400214819265157910687801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89067239518040421095167469 33400214819265157910687801)
    ·
      refine ⟨25050161114448868433015851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33400214819265157910687801 25050161114448868433015851)
      ·
        refine ⟨37575241671673302649523777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25050161114448868433015851 37575241671673302649523777)
        ·
          refine ⟨28181431253754976987142833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37575241671673302649523777 28181431253754976987142833)
          ·
            refine ⟨21136073440316232740357125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28181431253754976987142833 21136073440316232740357125)
            ·
              refine ⟨3963013770059293638816961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21136073440316232740357125 3963013770059293638816961)
              ·
                refine ⟨2972260327544470229112721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3963013770059293638816961 2972260327544470229112721)
                ·
                  refine ⟨2229195245658352671834541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2972260327544470229112721 2229195245658352671834541)
                  ·
                    refine ⟨835948217121882251937953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229195245658352671834541 835948217121882251937953)
                    ·
                      rfl

theorem cell22_2442005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_2442005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442005 prefixEnd_2442005 := by exact prefixLift 2442005
  have htrace : WordTrace (prefixWord ++ tailWord_2442005) baseStart_2442005 baseEnd_2442005 := by
    simpa [prefixWord, tailWord_2442005, baseEnd_2442005] using wordTrace_append hprefix tailTrace_2442005
  have hstable : (prefixWord ++ tailWord_2442005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442005).length < 2 ^ (prefixWord ++ tailWord_2442005).sum := by decide
  have hdescent : baseEnd_2442005 < baseStart_2442005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442018 : List Nat := [3, 3, 1, 1, 2, 2, 3, 7]
def baseStart_2442018 : Nat := 118140960795 + 2442018 * 2 ^ 59
def prefixEnd_2442018 : Nat := 4983230072969 + 3 ^ 40 * 2442018 * 2
def baseEnd_2442018 : Nat := 92883629698617172373657

theorem tailTrace_2442018 : CollatzResearch.WordTrace tailWord_2442018 prefixEnd_2442018 92883629698617172373657 := by
  unfold tailWord_2442018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22266928416748331078847677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59378475777995549543593805 22266928416748331078847677)
  ·
    refine ⟨8350098156280624154567879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22266928416748331078847677 8350098156280624154567879)
    ·
      refine ⟨12525147234420936231851819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8350098156280624154567879 12525147234420936231851819)
      ·
        refine ⟨18787720851631404347777729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12525147234420936231851819 18787720851631404347777729)
        ·
          refine ⟨14090790638723553260833297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18787720851631404347777729 14090790638723553260833297)
          ·
            refine ⟨10568092979042664945624973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14090790638723553260833297 10568092979042664945624973)
            ·
              refine ⟨3963034867140999354609365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10568092979042664945624973 3963034867140999354609365)
              ·
                refine ⟨92883629698617172373657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3963034867140999354609365 92883629698617172373657)
                ·
                  rfl

theorem cell22_2442018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_2442018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442018 prefixEnd_2442018 := by exact prefixLift 2442018
  have htrace : WordTrace (prefixWord ++ tailWord_2442018) baseStart_2442018 baseEnd_2442018 := by
    simpa [prefixWord, tailWord_2442018, baseEnd_2442018] using wordTrace_append hprefix tailTrace_2442018
  have hstable : (prefixWord ++ tailWord_2442018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442018).length < 2 ^ (prefixWord ++ tailWord_2442018).sum := by decide
  have hdescent : baseEnd_2442018 < baseStart_2442018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442080 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 5]
def baseStart_2442080 : Nat := 118140960795 + 2442080 * 2 ^ 59
def prefixEnd_2442080 : Nat := 4983230072969 + 3 ^ 40 * 2442080 * 2
def baseEnd_2442080 : Nat := 278657963718202352104241

theorem tailTrace_2442080 : CollatzResearch.WordTrace tailWord_2442080 prefixEnd_2442080 278657963718202352104241 := by
  unfold tailWord_2442080
  simp only [CollatzResearch.WordTrace]
  refine ⟨44534987496384354452073847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59379983328512472602765129 44534987496384354452073847)
  ·
    refine ⟨66802481244576531678110771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44534987496384354452073847 66802481244576531678110771)
    ·
      refine ⟨100203721866864797517166157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66802481244576531678110771 100203721866864797517166157)
      ·
        refine ⟨37576395700074299068937309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100203721866864797517166157 37576395700074299068937309)
        ·
          refine ⟨14091148387527862150851491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37576395700074299068937309 14091148387527862150851491)
          ·
            refine ⟨21136722581291793226277237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14091148387527862150851491 21136722581291793226277237)
            ·
              refine ⟨1981567741996105614963491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21136722581291793226277237 1981567741996105614963491)
              ·
                refine ⟨2972351612994158422445237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981567741996105614963491 2972351612994158422445237)
                ·
                  refine ⟨278657963718202352104241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2972351612994158422445237 278657963718202352104241)
                  ·
                    rfl

theorem cell22_2442080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 5].length) (baseStart_2442080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442080 prefixEnd_2442080 := by exact prefixLift 2442080
  have htrace : WordTrace (prefixWord ++ tailWord_2442080) baseStart_2442080 baseEnd_2442080 := by
    simpa [prefixWord, tailWord_2442080, baseEnd_2442080] using wordTrace_append hprefix tailTrace_2442080
  have hstable : (prefixWord ++ tailWord_2442080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442080).length < 2 ^ (prefixWord ++ tailWord_2442080).sum := by decide
  have hdescent : baseEnd_2442080 < baseStart_2442080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442183 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 2, 6]
def baseStart_2442183 : Nat := 118140960795 + 2442183 * 2 ^ 59
def prefixEnd_2442183 : Nat := 4983230072969 + 3 ^ 40 * 2442183 * 2
def baseEnd_2442183 : Nat := 836009150159549120987407

theorem tailTrace_2442183 : CollatzResearch.WordTrace tailWord_2442183 prefixEnd_2442183 836009150159549120987407 := by
  unfold tailWord_2442183
  simp only [CollatzResearch.WordTrace]
  refine ⟨89073731711395557495147203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59382487807597038330098135 89073731711395557495147203)
  ·
    refine ⟨133610597567093336242720805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89073731711395557495147203 133610597567093336242720805)
    ·
      refine ⟨25051987043830000545510151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133610597567093336242720805 25051987043830000545510151)
      ·
        refine ⟨37577980565745000818265227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25051987043830000545510151 37577980565745000818265227)
        ·
          refine ⟨56366970848617501227397841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37577980565745000818265227 56366970848617501227397841)
          ·
            refine ⟨42275228136463125920548381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56366970848617501227397841 42275228136463125920548381)
            ·
              refine ⟨15853210551173672220205643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42275228136463125920548381 15853210551173672220205643)
              ·
                refine ⟨23779815826760508330308465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15853210551173672220205643 23779815826760508330308465)
                ·
                  refine ⟨17834861870070381247731349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23779815826760508330308465 17834861870070381247731349)
                  ·
                    refine ⟨836009150159549120987407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17834861870070381247731349 836009150159549120987407)
                    ·
                      rfl

theorem cell22_2442183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_2442183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442183 prefixEnd_2442183 := by exact prefixLift 2442183
  have htrace : WordTrace (prefixWord ++ tailWord_2442183) baseStart_2442183 baseEnd_2442183 := by
    simpa [prefixWord, tailWord_2442183, baseEnd_2442183] using wordTrace_append hprefix tailTrace_2442183
  have hstable : (prefixWord ++ tailWord_2442183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442183).length < 2 ^ (prefixWord ++ tailWord_2442183).sum := by decide
  have hdescent : baseEnd_2442183 < baseStart_2442183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442202 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 3, 3]
def baseStart_2442202 : Nat := 118140960795 + 2442202 * 2 ^ 59
def prefixEnd_2442202 : Nat := 4983230072969 + 3 ^ 40 * 2442202 * 2
def baseEnd_2442202 : Nat := 836015654247839404762349

theorem tailTrace_2442202 : CollatzResearch.WordTrace tailWord_2442202 prefixEnd_2442202 836015654247839404762349 := by
  unfold tailWord_2442202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22268606174581680935022215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59382949798884482493392573 22268606174581680935022215)
  ·
    refine ⟨33402909261872521402533323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22268606174581680935022215 33402909261872521402533323)
    ·
      refine ⟨50104363892808782103799985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33402909261872521402533323 50104363892808782103799985)
      ·
        refine ⟨37578272919606586577849989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50104363892808782103799985 37578272919606586577849989)
        ·
          refine ⟨7045926172426234983346873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37578272919606586577849989 7045926172426234983346873)
          ·
            refine ⟨5284444629319676237510155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7045926172426234983346873 5284444629319676237510155)
            ·
              refine ⟨7926666943979514356265233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284444629319676237510155 7926666943979514356265233)
              ·
                refine ⟨5945000207984635767198925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7926666943979514356265233 5945000207984635767198925)
                ·
                  refine ⟨2229375077994238412699597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5945000207984635767198925 2229375077994238412699597)
                  ·
                    refine ⟨836015654247839404762349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229375077994238412699597 836015654247839404762349)
                    ·
                      rfl

theorem cell22_2442202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_2442202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442202 prefixEnd_2442202 := by exact prefixLift 2442202
  have htrace : WordTrace (prefixWord ++ tailWord_2442202) baseStart_2442202 baseEnd_2442202 := by
    simpa [prefixWord, tailWord_2442202, baseEnd_2442202] using wordTrace_append hprefix tailTrace_2442202
  have hstable : (prefixWord ++ tailWord_2442202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442202).length < 2 ^ (prefixWord ++ tailWord_2442202).sum := by decide
  have hdescent : baseEnd_2442202 < baseStart_2442202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442279 : List Nat := [1, 1, 7, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2442279 : Nat := 118140960795 + 2442279 * 2 ^ 59
def prefixEnd_2442279 : Nat := 4983230072969 + 3 ^ 40 * 2442279 * 2
def baseEnd_2442279 : Nat := 836042012921436870587113

theorem tailTrace_2442279 : CollatzResearch.WordTrace tailWord_2442279 prefixEnd_2442279 836042012921436870587113 := by
  unfold tailWord_2442279
  simp only [CollatzResearch.WordTrace]
  refine ⟨89077233119047765890641891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59384822079365177260427927 89077233119047765890641891)
  ·
    refine ⟨133615849678571648835962837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89077233119047765890641891 133615849678571648835962837)
    ·
      refine ⟨3131621476841523019592879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 133615849678571648835962837 3131621476841523019592879)
      ·
        refine ⟨4697432215262284529389319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131621476841523019592879 4697432215262284529389319)
        ·
          refine ⟨7046148322893426794083979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697432215262284529389319 7046148322893426794083979)
          ·
            refine ⟨10569222484340140191125969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7046148322893426794083979 10569222484340140191125969)
            ·
              refine ⟨7926916863255105143344477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10569222484340140191125969 7926916863255105143344477)
              ·
                refine ⟨2972593823720664428754179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7926916863255105143344477 2972593823720664428754179)
                ·
                  refine ⟨4458890735580996643131269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2972593823720664428754179 4458890735580996643131269)
                  ·
                    refine ⟨836042012921436870587113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4458890735580996643131269 836042012921436870587113)
                    ·
                      rfl

theorem cell22_2442279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2442279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442279 prefixEnd_2442279 := by exact prefixLift 2442279
  have htrace : WordTrace (prefixWord ++ tailWord_2442279) baseStart_2442279 baseEnd_2442279 := by
    simpa [prefixWord, tailWord_2442279, baseEnd_2442279] using wordTrace_append hprefix tailTrace_2442279
  have hstable : (prefixWord ++ tailWord_2442279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442279).length < 2 ^ (prefixWord ++ tailWord_2442279).sum := by decide
  have hdescent : baseEnd_2442279 < baseStart_2442279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442294 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_2442294 : Nat := 118140960795 + 2442294 * 2 ^ 59
def prefixEnd_2442294 : Nat := 4983230072969 + 3 ^ 40 * 2442294 * 2
def baseEnd_2442294 : Nat := 278682382575993943820689

theorem tailTrace_2442294 : CollatzResearch.WordTrace tailWord_2442294 prefixEnd_2442294 278682382575993943820689 := by
  unfold tailWord_2442294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567361263374588965777371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59385186809328948968291957 5567361263374588965777371)
  ·
    refine ⟨8351041895061883448666057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5567361263374588965777371 8351041895061883448666057)
    ·
      refine ⟨6263281421296412586499543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8351041895061883448666057 6263281421296412586499543)
      ·
        refine ⟨9394922131944618879749315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6263281421296412586499543 9394922131944618879749315)
        ·
          refine ⟨14092383197916928319623973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9394922131944618879749315 14092383197916928319623973)
          ·
            refine ⟨2642321849609424059929495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14092383197916928319623973 2642321849609424059929495)
            ·
              refine ⟨3963482774414136089894243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642321849609424059929495 3963482774414136089894243)
              ·
                refine ⟨5945224161621204134841365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963482774414136089894243 5945224161621204134841365)
                ·
                  refine ⟨278682382575993943820689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5945224161621204134841365 278682382575993943820689)
                  ·
                    rfl

theorem cell22_2442294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_2442294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442294 prefixEnd_2442294 := by exact prefixLift 2442294
  have htrace : WordTrace (prefixWord ++ tailWord_2442294) baseStart_2442294 baseEnd_2442294 := by
    simpa [prefixWord, tailWord_2442294, baseEnd_2442294] using wordTrace_append hprefix tailTrace_2442294
  have hstable : (prefixWord ++ tailWord_2442294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442294).length < 2 ^ (prefixWord ++ tailWord_2442294).sum := by decide
  have hdescent : baseEnd_2442294 < baseStart_2442294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442309 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 2, 3]
def baseStart_2442309 : Nat := 118140960795 + 2442309 * 2 ^ 59
def prefixEnd_2442309 : Nat := 4983230072969 + 3 ^ 40 * 2442309 * 2
def baseEnd_2442309 : Nat := 836052282534526792337021

theorem tailTrace_2442309 : CollatzResearch.WordTrace tailWord_2442309 prefixEnd_2442309 836052282534526792337021 := by
  unfold tailWord_2442309
  simp only [CollatzResearch.WordTrace]
  refine ⟨89078327308939081014233981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59385551539292720676155987 89078327308939081014233981)
  ·
    refine ⟨33404372740852155380337743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89078327308939081014233981 33404372740852155380337743)
    ·
      refine ⟨50106559111278233070506615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33404372740852155380337743 50106559111278233070506615)
      ·
        refine ⟨75159838666917349605759923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50106559111278233070506615 75159838666917349605759923)
        ·
          refine ⟨112739758000376024408639885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75159838666917349605759923 112739758000376024408639885)
          ·
            refine ⟨42277409250141009153239957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112739758000376024408639885 42277409250141009153239957)
            ·
              refine ⟨1981753558600359804058123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42277409250141009153239957 1981753558600359804058123)
              ·
                refine ⟨2972630337900539706087185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1981753558600359804058123 2972630337900539706087185)
                ·
                  refine ⟨2229472753425404779565389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2972630337900539706087185 2229472753425404779565389)
                  ·
                    refine ⟨836052282534526792337021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229472753425404779565389 836052282534526792337021)
                    ·
                      rfl

theorem cell22_2442309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 2, 3].length) (baseStart_2442309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442309 prefixEnd_2442309 := by exact prefixLift 2442309
  have htrace : WordTrace (prefixWord ++ tailWord_2442309) baseStart_2442309 baseEnd_2442309 := by
    simpa [prefixWord, tailWord_2442309, baseEnd_2442309] using wordTrace_append hprefix tailTrace_2442309
  have hstable : (prefixWord ++ tailWord_2442309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442309).length < 2 ^ (prefixWord ++ tailWord_2442309).sum := by decide
  have hdescent : baseEnd_2442309 < baseStart_2442309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442326 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2442326 : Nat := 118140960795 + 2442326 * 2 ^ 59
def prefixEnd_2442326 : Nat := 4983230072969 + 3 ^ 40 * 2442326 * 2
def baseEnd_2442326 : Nat := 836058101981944414661969

theorem tailTrace_2442326 : CollatzResearch.WordTrace tailWord_2442326 prefixEnd_2442326 836058101981944414661969 := by
  unfold tailWord_2442326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567434209367343307350177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59385964899918328611735221 5567434209367343307350177)
  ·
    refine ⟨4175575657025507480512633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5567434209367343307350177 4175575657025507480512633)
    ·
      refine ⟨3131681742769130610384475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4175575657025507480512633 3131681742769130610384475)
      ·
        refine ⟨4697522614153695915576713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131681742769130610384475 4697522614153695915576713)
        ·
          refine ⟨3523141960615271936682535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4697522614153695915576713 3523141960615271936682535)
          ·
            refine ⟨5284712940922907905023803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523141960615271936682535 5284712940922907905023803)
            ·
              refine ⟨7927069411384361857535705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284712940922907905023803 7927069411384361857535705)
              ·
                refine ⟨5945302058538271393151779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7927069411384361857535705 5945302058538271393151779)
                ·
                  refine ⟨8917953087807407089727669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5945302058538271393151779 8917953087807407089727669)
                  ·
                    refine ⟨836058101981944414661969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8917953087807407089727669 836058101981944414661969)
                    ·
                      rfl

theorem cell22_2442326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2442326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442326 prefixEnd_2442326 := by exact prefixLift 2442326
  have htrace : WordTrace (prefixWord ++ tailWord_2442326) baseStart_2442326 baseEnd_2442326 := by
    simpa [prefixWord, tailWord_2442326, baseEnd_2442326] using wordTrace_append hprefix tailTrace_2442326
  have hstable : (prefixWord ++ tailWord_2442326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442326).length < 2 ^ (prefixWord ++ tailWord_2442326).sum := by decide
  have hdescent : baseEnd_2442326 < baseStart_2442326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442442 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 1, 6]
def baseStart_2442442 : Nat := 118140960795 + 2442442 * 2 ^ 59
def prefixEnd_2442442 : Nat := 4983230072969 + 3 ^ 40 * 2442442 * 2
def baseEnd_2442442 : Nat := 836097811152558778761613

theorem tailTrace_2442442 : CollatzResearch.WordTrace tailWord_2442442 prefixEnd_2442442 836097811152558778761613 := by
  unfold tailWord_2442442
  simp only [CollatzResearch.WordTrace]
  refine ⟨22270794554364311182206395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59388785478304829819217053 22270794554364311182206395)
  ·
    refine ⟨33406191831546466773309593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22270794554364311182206395 33406191831546466773309593)
    ·
      refine ⟨25054643873659850079982195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33406191831546466773309593 25054643873659850079982195)
      ·
        refine ⟨37581965810489775119973293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25054643873659850079982195 37581965810489775119973293)
        ·
          refine ⟨14093237178933665669989985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37581965810489775119973293 14093237178933665669989985)
          ·
            refine ⟨10569927884200249252492489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14093237178933665669989985 10569927884200249252492489)
            ·
              refine ⟨7927445913150186939369367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10569927884200249252492489 7927445913150186939369367)
              ·
                refine ⟨11891168869725280409054051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7927445913150186939369367 11891168869725280409054051)
                ·
                  refine ⟨17836753304587920613581077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11891168869725280409054051 17836753304587920613581077)
                  ·
                    refine ⟨836097811152558778761613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17836753304587920613581077 836097811152558778761613)
                    ·
                      rfl

theorem cell22_2442442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_2442442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442442 prefixEnd_2442442 := by exact prefixLift 2442442
  have htrace : WordTrace (prefixWord ++ tailWord_2442442) baseStart_2442442 baseEnd_2442442 := by
    simpa [prefixWord, tailWord_2442442, baseEnd_2442442] using wordTrace_append hprefix tailTrace_2442442
  have hstable : (prefixWord ++ tailWord_2442442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442442).length < 2 ^ (prefixWord ++ tailWord_2442442).sum := by decide
  have hdescent : baseEnd_2442442 < baseStart_2442442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442506 : List Nat := [3, 1, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_2442506 : Nat := 118140960795 + 2442506 * 2 ^ 59
def prefixEnd_2442506 : Nat := 4983230072969 + 3 ^ 40 * 2442506 * 2
def baseEnd_2442506 : Nat := 836119719660483945161417

theorem tailTrace_2442506 : CollatzResearch.WordTrace tailWord_2442506 prefixEnd_2442506 836119719660483945161417 := by
  unfold tailWord_2442506
  simp only [CollatzResearch.WordTrace]
  refine ⟨22271378122306345914788843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59390341659483589106103581 22271378122306345914788843)
  ·
    refine ⟨33407067183459518872183265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22271378122306345914788843 33407067183459518872183265)
    ·
      refine ⟨25055300387594639154137449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33407067183459518872183265 25055300387594639154137449)
      ·
        refine ⟨18791475290695979365603087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25055300387594639154137449 18791475290695979365603087)
        ·
          refine ⟨28187212936043969048404631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18791475290695979365603087 28187212936043969048404631)
          ·
            refine ⟨42280819404065953572606947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28187212936043969048404631 42280819404065953572606947)
            ·
              refine ⟨63421229106098930358910421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42280819404065953572606947 63421229106098930358910421)
              ·
                refine ⟨1486435057174193680286963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 63421229106098930358910421 1486435057174193680286963)
                ·
                  refine ⟨2229652585761290520430445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486435057174193680286963 2229652585761290520430445)
                  ·
                    refine ⟨836119719660483945161417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229652585761290520430445 836119719660483945161417)
                    ·
                      rfl

theorem cell22_2442506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_2442506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442506 prefixEnd_2442506 := by exact prefixLift 2442506
  have htrace : WordTrace (prefixWord ++ tailWord_2442506) baseStart_2442506 baseEnd_2442506 := by
    simpa [prefixWord, tailWord_2442506, baseEnd_2442506] using wordTrace_append hprefix tailTrace_2442506
  have hstable : (prefixWord ++ tailWord_2442506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442506).length < 2 ^ (prefixWord ++ tailWord_2442506).sum := by decide
  have hdescent : baseEnd_2442506 < baseStart_2442506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442517 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_2442517 : Nat := 118140960795 + 2442517 * 2 ^ 59
def prefixEnd_2442517 : Nat := 4983230072969 + 3 ^ 40 * 2442517 * 2
def baseEnd_2442517 : Nat := 836123485185283583136383

theorem tailTrace_2442517 : CollatzResearch.WordTrace tailWord_2442517 prefixEnd_2442517 836123485185283583136383 := by
  unfold tailWord_2442517
  simp only [CollatzResearch.WordTrace]
  refine ⟨89085913692185532537805805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59390609128123688358537203 89085913692185532537805805)
  ·
    refine ⟨33407217634569574701677177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89085913692185532537805805 33407217634569574701677177)
    ·
      refine ⟨25055413225927181026257883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33407217634569574701677177 25055413225927181026257883)
      ·
        refine ⟨37583119838890771539386825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25055413225927181026257883 37583119838890771539386825)
        ·
          refine ⟨28187339879168078654540119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37583119838890771539386825 28187339879168078654540119)
          ·
            refine ⟨42281009818752117981810179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28187339879168078654540119 42281009818752117981810179)
            ·
              refine ⟨63421514728128176972715269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42281009818752117981810179 63421514728128176972715269)
              ·
                refine ⟨11891534011524033182384113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63421514728128176972715269 11891534011524033182384113)
                ·
                  refine ⟨8918650508643024886788085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11891534011524033182384113 8918650508643024886788085)
                  ·
                    refine ⟨836123485185283583136383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8918650508643024886788085 836123485185283583136383)
                    ·
                      rfl

theorem cell22_2442517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_2442517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442517 prefixEnd_2442517 := by exact prefixLift 2442517
  have htrace : WordTrace (prefixWord ++ tailWord_2442517) baseStart_2442517 baseEnd_2442517 := by
    simpa [prefixWord, tailWord_2442517, baseEnd_2442517] using wordTrace_append hprefix tailTrace_2442517
  have hstable : (prefixWord ++ tailWord_2442517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442517).length < 2 ^ (prefixWord ++ tailWord_2442517).sum := by decide
  have hdescent : baseEnd_2442517 < baseStart_2442517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442519 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 5]
def baseStart_2442519 : Nat := 118140960795 + 2442519 * 2 ^ 59
def prefixEnd_2442519 : Nat := 4983230072969 + 3 ^ 40 * 2442519 * 2
def baseEnd_2442519 : Nat := 278708056608718748195459

theorem tailTrace_2442519 : CollatzResearch.WordTrace tailWord_2442519 prefixEnd_2442519 278708056608718748195459 := by
  unfold tailWord_2442519
  simp only [CollatzResearch.WordTrace]
  refine ⟨89085986638178286879378611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59390657758785524586252407 89085986638178286879378611)
  ·
    refine ⟨133628979957267430319067917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89085986638178286879378611 133628979957267430319067917)
    ·
      refine ⟨50110867483975286369650469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133628979957267430319067917 50110867483975286369650469)
      ·
        refine ⟨9395787653245366194309463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50110867483975286369650469 9395787653245366194309463)
        ·
          refine ⟨14093681479868049291464195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9395787653245366194309463 14093681479868049291464195)
          ·
            refine ⟨21140522219802073937196293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14093681479868049291464195 21140522219802073937196293)
            ·
              refine ⟨3963847916212888863224305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21140522219802073937196293 3963847916212888863224305)
              ·
                refine ⟨2972885937159666647418229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3963847916212888863224305 2972885937159666647418229)
                ·
                  refine ⟨278708056608718748195459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2972885937159666647418229 278708056608718748195459)
                  ·
                    rfl

theorem cell22_2442519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 5].length) (baseStart_2442519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442519 prefixEnd_2442519 := by exact prefixLift 2442519
  have htrace : WordTrace (prefixWord ++ tailWord_2442519) baseStart_2442519 baseEnd_2442519 := by
    simpa [prefixWord, tailWord_2442519, baseEnd_2442519] using wordTrace_append hprefix tailTrace_2442519
  have hstable : (prefixWord ++ tailWord_2442519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442519).length < 2 ^ (prefixWord ++ tailWord_2442519).sum := by decide
  have hdescent : baseEnd_2442519 < baseStart_2442519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442547 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 8]
def baseStart_2442547 : Nat := 118140960795 + 2442547 * 2 ^ 59
def prefixEnd_2442547 : Nat := 4983230072969 + 3 ^ 40 * 2442547 * 2
def baseEnd_2442547 : Nat := 278711251599457834962097

theorem tailTrace_2442547 : CollatzResearch.WordTrace tailWord_2442547 prefixEnd_2442547 278711251599457834962097 := by
  unfold tailWord_2442547
  simp only [CollatzResearch.WordTrace]
  refine ⟨89087007882076847661397895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59391338588051231774265263 89087007882076847661397895)
  ·
    refine ⟨133630511823115271492096843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89087007882076847661397895 133630511823115271492096843)
    ·
      refine ⟨200445767734672907238145265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133630511823115271492096843 200445767734672907238145265)
      ·
        refine ⟨150334325801004680428608949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200445767734672907238145265 150334325801004680428608949)
        ·
          refine ⟨14093843043844188790182089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150334325801004680428608949 14093843043844188790182089)
          ·
            refine ⟨10570382282883141592636567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14093843043844188790182089 10570382282883141592636567)
            ·
              refine ⟨15855573424324712388954851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10570382282883141592636567 15855573424324712388954851)
              ·
                refine ⟨23783360136487068583432277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15855573424324712388954851 23783360136487068583432277)
                ·
                  refine ⟨278711251599457834962097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23783360136487068583432277 278711251599457834962097)
                  ·
                    rfl

theorem cell22_2442547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_2442547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442547 prefixEnd_2442547 := by exact prefixLift 2442547
  have htrace : WordTrace (prefixWord ++ tailWord_2442547) baseStart_2442547 baseEnd_2442547 := by
    simpa [prefixWord, tailWord_2442547, baseEnd_2442547] using wordTrace_append hprefix tailTrace_2442547
  have hstable : (prefixWord ++ tailWord_2442547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442547).length < 2 ^ (prefixWord ++ tailWord_2442547).sum := by decide
  have hdescent : baseEnd_2442547 < baseStart_2442547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442549 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_2442549 : Nat := 118140960795 + 2442549 * 2 ^ 59
def prefixEnd_2442549 : Nat := 4983230072969 + 3 ^ 40 * 2442549 * 2
def baseEnd_2442549 : Nat := 836134439439246166336285

theorem tailTrace_2442549 : CollatzResearch.WordTrace tailWord_2442549 prefixEnd_2442549 836134439439246166336285 := by
  unfold tailWord_2442549
  simp only [CollatzResearch.WordTrace]
  refine ⟨89087080828069602002970701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59391387218713068001980467 89087080828069602002970701)
  ·
    refine ⟨33407655310526100751114013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89087080828069602002970701 33407655310526100751114013)
    ·
      refine ⟨12527870741447287781667755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33407655310526100751114013 12527870741447287781667755)
      ·
        refine ⟨18791806112170931672501633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12527870741447287781667755 18791806112170931672501633)
        ·
          refine ⟨14093854584128198754376225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18791806112170931672501633 14093854584128198754376225)
          ·
            refine ⟨10570390938096149065782169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14093854584128198754376225 10570390938096149065782169)
            ·
              refine ⟨7927793203572111799336627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10570390938096149065782169 7927793203572111799336627)
              ·
                refine ⟨11891689805358167699004941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7927793203572111799336627 11891689805358167699004941)
                ·
                  refine ⟨4459383677009312887126853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11891689805358167699004941 4459383677009312887126853)
                  ·
                    refine ⟨836134439439246166336285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4459383677009312887126853 836134439439246166336285)
                    ·
                      rfl

theorem cell22_2442549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_2442549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442549 prefixEnd_2442549 := by exact prefixLift 2442549
  have htrace : WordTrace (prefixWord ++ tailWord_2442549) baseStart_2442549 baseEnd_2442549 := by
    simpa [prefixWord, tailWord_2442549, baseEnd_2442549] using wordTrace_append hprefix tailTrace_2442549
  have hstable : (prefixWord ++ tailWord_2442549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442549).length < 2 ^ (prefixWord ++ tailWord_2442549).sum := by decide
  have hdescent : baseEnd_2442549 < baseStart_2442549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442579 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 4, 3]
def baseStart_2442579 : Nat := 118140960795 + 2442579 * 2 ^ 59
def prefixEnd_2442579 : Nat := 4983230072969 + 3 ^ 40 * 2442579 * 2
def baseEnd_2442579 : Nat := 836144709052336088086193

theorem tailTrace_2442579 : CollatzResearch.WordTrace tailWord_2442579 prefixEnd_2442579 836144709052336088086193 := by
  unfold tailWord_2442579
  simp only [CollatzResearch.WordTrace]
  refine ⟨89088175017960917126562791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59392116678640611417708527 89088175017960917126562791)
  ·
    refine ⟨133632262526941375689844187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89088175017960917126562791 133632262526941375689844187)
    ·
      refine ⟨200448393790412063534766281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133632262526941375689844187 200448393790412063534766281)
      ·
        refine ⟨150336295342809047651074711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200448393790412063534766281 150336295342809047651074711)
        ·
          refine ⟨225504443014213571476612067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150336295342809047651074711 225504443014213571476612067)
          ·
            refine ⟨338256664521320357214918101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225504443014213571476612067 338256664521320357214918101)
            ·
              refine ⟨7927890574718445872224643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 338256664521320357214918101 7927890574718445872224643)
              ·
                refine ⟨11891835862077668808336965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7927890574718445872224643 11891835862077668808336965)
                ·
                  refine ⟨2229719224139562901563181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11891835862077668808336965 2229719224139562901563181)
                  ·
                    refine ⟨836144709052336088086193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229719224139562901563181 836144709052336088086193)
                    ·
                      rfl

theorem cell22_2442579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 3].length) (baseStart_2442579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442579 prefixEnd_2442579 := by exact prefixLift 2442579
  have htrace : WordTrace (prefixWord ++ tailWord_2442579) baseStart_2442579 baseEnd_2442579 := by
    simpa [prefixWord, tailWord_2442579, baseEnd_2442579] using wordTrace_append hprefix tailTrace_2442579
  have hstable : (prefixWord ++ tailWord_2442579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442579).length < 2 ^ (prefixWord ++ tailWord_2442579).sum := by decide
  have hdescent : baseEnd_2442579 < baseStart_2442579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442581 : List Nat := [1, 3, 2, 2, 3, 1, 2, 4, 4]
def baseStart_2442581 : Nat := 118140960795 + 2442581 * 2 ^ 59
def prefixEnd_2442581 : Nat := 4983230072969 + 3 ^ 40 * 2442581 * 2
def baseEnd_2442581 : Nat := 278715131231069583178729

theorem tailTrace_2442581 : CollatzResearch.WordTrace tailWord_2442581 prefixEnd_2442581 278715131231069583178729 := by
  unfold tailWord_2442581
  simp only [CollatzResearch.WordTrace]
  refine ⟨89088247963953671468135597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59392165309302447645423731 89088247963953671468135597)
  ·
    refine ⟨33408092986482626800550849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89088247963953671468135597 33408092986482626800550849)
    ·
      refine ⟨25056069739861970100413137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33408092986482626800550849 25056069739861970100413137)
      ·
        refine ⟨18792052304896477575309853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25056069739861970100413137 18792052304896477575309853)
        ·
          refine ⟨7047019614336179090741195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18792052304896477575309853 7047019614336179090741195)
          ·
            refine ⟨10570529421504268636111793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047019614336179090741195 10570529421504268636111793)
            ·
              refine ⟨7927897066128201477083845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10570529421504268636111793 7927897066128201477083845)
              ·
                refine ⟨1486480699899037776953221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7927897066128201477083845 1486480699899037776953221)
                ·
                  refine ⟨278715131231069583178729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1486480699899037776953221 278715131231069583178729)
                  ·
                    rfl

theorem cell22_2442581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 4].length) (baseStart_2442581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442581 prefixEnd_2442581 := by exact prefixLift 2442581
  have htrace : WordTrace (prefixWord ++ tailWord_2442581) baseStart_2442581 baseEnd_2442581 := by
    simpa [prefixWord, tailWord_2442581, baseEnd_2442581] using wordTrace_append hprefix tailTrace_2442581
  have hstable : (prefixWord ++ tailWord_2442581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442581).length < 2 ^ (prefixWord ++ tailWord_2442581).sum := by decide
  have hdescent : baseEnd_2442581 < baseStart_2442581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442594 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2442594 : Nat := 118140960795 + 2442594 * 2 ^ 59
def prefixEnd_2442594 : Nat := 4983230072969 + 3 ^ 40 * 2442594 * 2
def baseEnd_2442594 : Nat := 836149843858881048961147

theorem tailTrace_2442594 : CollatzResearch.WordTrace tailWord_2442594 prefixEnd_2442594 836149843858881048961147 := by
  unfold tailWord_2442594
  simp only [CollatzResearch.WordTrace]
  refine ⟨22272180528226643672089709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59392481408604383125572557 22272180528226643672089709)
  ·
    refine ⟨8352067698084991377033641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22272180528226643672089709 8352067698084991377033641)
    ·
      refine ⟨6264050773563743532775231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8352067698084991377033641 6264050773563743532775231)
      ·
        refine ⟨9396076160345615299162847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264050773563743532775231 9396076160345615299162847)
        ·
          refine ⟨14094114240518422948744271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396076160345615299162847 14094114240518422948744271)
          ·
            refine ⟨21141171360777634423116407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14094114240518422948744271 21141171360777634423116407)
            ·
              refine ⟨31711757041166451634674611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21141171360777634423116407 31711757041166451634674611)
              ·
                refine ⟨47567635561749677452011917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31711757041166451634674611 47567635561749677452011917)
                ·
                  refine ⟨17837863335656129044504469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47567635561749677452011917 17837863335656129044504469)
                  ·
                    refine ⟨836149843858881048961147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17837863335656129044504469 836149843858881048961147)
                    ·
                      rfl

theorem cell22_2442594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2442594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442594 prefixEnd_2442594 := by exact prefixLift 2442594
  have htrace : WordTrace (prefixWord ++ tailWord_2442594) baseStart_2442594 baseEnd_2442594 := by
    simpa [prefixWord, tailWord_2442594, baseEnd_2442594] using wordTrace_append hprefix tailTrace_2442594
  have hstable : (prefixWord ++ tailWord_2442594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442594).length < 2 ^ (prefixWord ++ tailWord_2442594).sum := by decide
  have hdescent : baseEnd_2442594 < baseStart_2442594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442596 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 1, 5]
def baseStart_2442596 : Nat := 118140960795 + 2442596 * 2 ^ 59
def prefixEnd_2442596 : Nat := 4983230072969 + 3 ^ 40 * 2442596 * 2
def baseEnd_2442596 : Nat := 836150528499753710411141

theorem tailTrace_2442596 : CollatzResearch.WordTrace tailWord_2442596 prefixEnd_2442596 836150528499753710411141 := by
  unfold tailWord_2442596
  simp only [CollatzResearch.WordTrace]
  refine ⟨44544397529449664514965821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59392530039266219353287761 44544397529449664514965821)
  ·
    refine ⟨16704149073543624193112183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44544397529449664514965821 16704149073543624193112183)
    ·
      refine ⟨25056223610315436289668275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16704149073543624193112183 25056223610315436289668275)
      ·
        refine ⟨37584335415473154434502413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25056223610315436289668275 37584335415473154434502413)
        ·
          refine ⟨14094125780802432912938405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37584335415473154434502413 14094125780802432912938405)
          ·
            refine ⟨2642648583900456171175951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14094125780802432912938405 2642648583900456171175951)
            ·
              refine ⟨3963972875850684256763927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2642648583900456171175951 3963972875850684256763927)
              ·
                refine ⟨5945959313776026385145891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3963972875850684256763927 5945959313776026385145891)
                ·
                  refine ⟨8918938970664039577718837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5945959313776026385145891 8918938970664039577718837)
                  ·
                    refine ⟨836150528499753710411141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8918938970664039577718837 836150528499753710411141)
                    ·
                      rfl

theorem cell22_2442596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_2442596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442596 prefixEnd_2442596 := by exact prefixLift 2442596
  have htrace : WordTrace (prefixWord ++ tailWord_2442596) baseStart_2442596 baseEnd_2442596 := by
    simpa [prefixWord, tailWord_2442596, baseEnd_2442596] using wordTrace_append hprefix tailTrace_2442596
  have hstable : (prefixWord ++ tailWord_2442596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442596).length < 2 ^ (prefixWord ++ tailWord_2442596).sum := by decide
  have hdescent : baseEnd_2442596 < baseStart_2442596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442607 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 2, 7]
def baseStart_2442607 : Nat := 118140960795 + 2442607 * 2 ^ 59
def prefixEnd_2442607 : Nat := 4983230072969 + 3 ^ 40 * 2442607 * 2
def baseEnd_2442607 : Nat := 836154294024553348386107

theorem tailTrace_2442607 : CollatzResearch.WordTrace tailWord_2442607 prefixEnd_2442607 836154294024553348386107 := by
  unfold tailWord_2442607
  simp only [CollatzResearch.WordTrace]
  refine ⟨89089196261859477908582075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59392797507906318605721383 89089196261859477908582075)
  ·
    refine ⟨133633794392789216862873113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89089196261859477908582075 133633794392789216862873113)
    ·
      refine ⟨100225345794591912647154835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133633794392789216862873113 100225345794591912647154835)
      ·
        refine ⟨150338018691887868970732253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100225345794591912647154835 150338018691887868970732253)
        ·
          refine ⟨56376757009457950864024595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150338018691887868970732253 56376757009457950864024595)
          ·
            refine ⟨84565135514186926296036893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56376757009457950864024595 84565135514186926296036893)
            ·
              refine ⟨31711925817820097361013835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84565135514186926296036893 31711925817820097361013835)
              ·
                refine ⟨47567888726730146041520753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31711925817820097361013835 47567888726730146041520753)
                ·
                  refine ⟨35675916545047609531140565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47567888726730146041520753 35675916545047609531140565)
                  ·
                    refine ⟨836154294024553348386107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35675916545047609531140565 836154294024553348386107)
                    ·
                      rfl

theorem cell22_2442607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_2442607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442607 prefixEnd_2442607 := by exact prefixLift 2442607
  have htrace : WordTrace (prefixWord ++ tailWord_2442607) baseStart_2442607 baseEnd_2442607 := by
    simpa [prefixWord, tailWord_2442607, baseEnd_2442607] using wordTrace_append hprefix tailTrace_2442607
  have hstable : (prefixWord ++ tailWord_2442607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442607).length < 2 ^ (prefixWord ++ tailWord_2442607).sum := by decide
  have hdescent : baseEnd_2442607 < baseStart_2442607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442609 : List Nat := [1, 2, 2, 2, 1, 2, 6, 6]
def baseStart_2442609 : Nat := 118140960795 + 2442609 * 2 ^ 59
def prefixEnd_2442609 : Nat := 4983230072969 + 3 ^ 40 * 2442609 * 2
def baseEnd_2442609 : Nat := 92906108740602889981789

theorem tailTrace_2442609 : CollatzResearch.WordTrace tailWord_2442609 prefixEnd_2442609 92906108740602889981789 := by
  unfold tailWord_2442609
  simp only [CollatzResearch.WordTrace]
  refine ⟨89089269207852232250154881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59392846138568154833436587 89089269207852232250154881)
  ·
    refine ⟨66816951905889174187616161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89089269207852232250154881 66816951905889174187616161)
    ·
      refine ⟨50112713929416880640712121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66816951905889174187616161 50112713929416880640712121)
      ·
        refine ⟨37584535447062660480534091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50112713929416880640712121 37584535447062660480534091)
        ·
          refine ⟨56376803170593990720801137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37584535447062660480534091 56376803170593990720801137)
          ·
            refine ⟨42282602377945493040600853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56376803170593990720801137 42282602377945493040600853)
            ·
              refine ⟨1981996986466194986278165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42282602377945493040600853 1981996986466194986278165)
              ·
                refine ⟨92906108740602889981789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1981996986466194986278165 92906108740602889981789)
                ·
                  rfl

theorem cell22_2442609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 6].length) (baseStart_2442609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442609 prefixEnd_2442609 := by exact prefixLift 2442609
  have htrace : WordTrace (prefixWord ++ tailWord_2442609) baseStart_2442609 baseEnd_2442609 := by
    simpa [prefixWord, tailWord_2442609, baseEnd_2442609] using wordTrace_append hprefix tailTrace_2442609
  have hstable : (prefixWord ++ tailWord_2442609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442609).length < 2 ^ (prefixWord ++ tailWord_2442609).sum := by decide
  have hdescent : baseEnd_2442609 < baseStart_2442609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442624 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 5, 3]
def baseStart_2442624 : Nat := 118140960795 + 2442624 * 2 ^ 59
def prefixEnd_2442624 : Nat := 4983230072969 + 3 ^ 40 * 2442624 * 2
def baseEnd_2442624 : Nat := 836160113471970970711055

theorem tailTrace_2442624 : CollatzResearch.WordTrace tailWord_2442624 prefixEnd_2442624 836160113471970970711055 := by
  unfold tailWord_2442624
  simp only [CollatzResearch.WordTrace]
  refine ⟨44544908151398944905975463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59393210868531926541300617 44544908151398944905975463)
  ·
    refine ⟨66817362227098417358963195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44544908151398944905975463 66817362227098417358963195)
    ·
      refine ⟨100226043340647626038444793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66817362227098417358963195 100226043340647626038444793)
      ·
        refine ⟨75169532505485719528833595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100226043340647626038444793 75169532505485719528833595)
        ·
          refine ⟨112754298758228579293250393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75169532505485719528833595 112754298758228579293250393)
          ·
            refine ⟨84565724068671434469937795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112754298758228579293250393 84565724068671434469937795)
            ·
              refine ⟨126848586103007151704906693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84565724068671434469937795 126848586103007151704906693)
              ·
                refine ⟨23784109894313840944670005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126848586103007151704906693 23784109894313840944670005)
                ·
                  refine ⟨2229760302591922588562813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23784109894313840944670005 2229760302591922588562813)
                  ·
                    refine ⟨836160113471970970711055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229760302591922588562813 836160113471970970711055)
                    ·
                      rfl

theorem cell22_2442624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_2442624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442624 prefixEnd_2442624 := by exact prefixLift 2442624
  have htrace : WordTrace (prefixWord ++ tailWord_2442624) baseStart_2442624 baseEnd_2442624 := by
    simpa [prefixWord, tailWord_2442624, baseEnd_2442624] using wordTrace_append hprefix tailTrace_2442624
  have hstable : (prefixWord ++ tailWord_2442624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442624).length < 2 ^ (prefixWord ++ tailWord_2442624).sum := by decide
  have hdescent : baseEnd_2442624 < baseStart_2442624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442626 : List Nat := [3, 4, 2, 1, 1, 1, 10]
def baseStart_2442626 : Nat := 118140960795 + 2442626 * 2 ^ 59
def prefixEnd_2442626 : Nat := 4983230072969 + 3 ^ 40 * 2442626 * 2
def baseEnd_2442626 : Nat := 30968918448623838228187

theorem tailTrace_2442626 : CollatzResearch.WordTrace tailWord_2442626 prefixEnd_2442626 30968918448623838228187 := by
  unfold tailWord_2442626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22272472312197661038380933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59393259499193762769015821 22272472312197661038380933)
  ·
    refine ⟨4176088558537061444696425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22272472312197661038380933 4176088558537061444696425)
    ·
      refine ⟨3132066418902796083522319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4176088558537061444696425 3132066418902796083522319)
      ·
        refine ⟨4698099628354194125283479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3132066418902796083522319 4698099628354194125283479)
        ·
          refine ⟨7047149442531291187925219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4698099628354194125283479 7047149442531291187925219)
          ·
            refine ⟨10570724163796936781887829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047149442531291187925219 10570724163796936781887829)
            ·
              refine ⟨30968918448623838228187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10570724163796936781887829 30968918448623838228187)
              ·
                rfl

theorem cell22_2442626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 10].length) (baseStart_2442626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442626 prefixEnd_2442626 := by exact prefixLift 2442626
  have htrace : WordTrace (prefixWord ++ tailWord_2442626) baseStart_2442626 baseEnd_2442626 := by
    simpa [prefixWord, tailWord_2442626, baseEnd_2442626] using wordTrace_append hprefix tailTrace_2442626
  have hstable : (prefixWord ++ tailWord_2442626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442626).length < 2 ^ (prefixWord ++ tailWord_2442626).sum := by decide
  have hdescent : baseEnd_2442626 < baseStart_2442626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442692 : List Nat := [2, 3, 3, 2, 1, 1, 4, 2, 1, 3]
def baseStart_2442692 : Nat := 118140960795 + 2442692 * 2 ^ 59
def prefixEnd_2442692 : Nat := 4983230072969 + 3 ^ 40 * 2442692 * 2
def baseEnd_2442692 : Nat := 836183391261641460010847

theorem tailTrace_2442692 : CollatzResearch.WordTrace tailWord_2442692 prefixEnd_2442692 836183391261641460010847 := by
  unfold tailWord_2442692
  simp only [CollatzResearch.WordTrace]
  refine ⟨44546148233275768712713165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59394864311034358283617553 44546148233275768712713165)
  ·
    refine ⟨16704805587478413267267437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44546148233275768712713165 16704805587478413267267437)
    ·
      refine ⟨6264302095304404975225289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16704805587478413267267437 6264302095304404975225289)
      ·
        refine ⟨4698226571478303731418967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6264302095304404975225289 4698226571478303731418967)
        ·
          refine ⟨7047339857217455597128451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4698226571478303731418967 7047339857217455597128451)
          ·
            refine ⟨10571009785826183395692677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7047339857217455597128451 10571009785826183395692677)
            ·
              refine ⟨1982064334842409386692377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10571009785826183395692677 1982064334842409386692377)
              ·
                refine ⟨1486548251131807040019283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982064334842409386692377 1486548251131807040019283)
                ·
                  refine ⟨2229822376697710560028925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1486548251131807040019283 2229822376697710560028925)
                  ·
                    refine ⟨836183391261641460010847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229822376697710560028925 836183391261641460010847)
                    ·
                      rfl

theorem cell22_2442692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_2442692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442692 prefixEnd_2442692 := by exact prefixLift 2442692
  have htrace : WordTrace (prefixWord ++ tailWord_2442692) baseStart_2442692 baseEnd_2442692 := by
    simpa [prefixWord, tailWord_2442692, baseEnd_2442692] using wordTrace_append hprefix tailTrace_2442692
  have hstable : (prefixWord ++ tailWord_2442692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442692).length < 2 ^ (prefixWord ++ tailWord_2442692).sum := by decide
  have hdescent : baseEnd_2442692 < baseStart_2442692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442744 : List Nat := [2, 1, 2, 1, 1, 6, 9]
def baseStart_2442744 : Nat := 118140960795 + 2442744 * 2 ^ 59
def prefixEnd_2442744 : Nat := 4983230072969 + 3 ^ 40 * 2442744 * 2
def baseEnd_2442744 : Nat := 30970414515715950285581

theorem tailTrace_2442744 : CollatzResearch.WordTrace tailWord_2442744 prefixEnd_2442744 30970414515715950285581 := by
  unfold tailWord_2442744
  simp only [CollatzResearch.WordTrace]
  refine ⟨44547096531181575153159643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59396128708242100204212857 44547096531181575153159643)
  ·
    refine ⟨66820644796772362729739465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44547096531181575153159643 66820644796772362729739465)
    ·
      refine ⟨50115483597579272047304599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66820644796772362729739465 50115483597579272047304599)
      ·
        refine ⟨75173225396368908070956899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50115483597579272047304599 75173225396368908070956899)
        ·
          refine ⟨112759838094553362106435349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75173225396368908070956899 112759838094553362106435349)
          ·
            refine ⟨5285617410682188848739157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112759838094553362106435349 5285617410682188848739157)
            ·
              refine ⟨30970414515715950285581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5285617410682188848739157 30970414515715950285581)
              ·
                rfl

theorem cell22_2442744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 9].length) (baseStart_2442744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442744 prefixEnd_2442744 := by exact prefixLift 2442744
  have htrace : WordTrace (prefixWord ++ tailWord_2442744) baseStart_2442744 baseEnd_2442744 := by
    simpa [prefixWord, tailWord_2442744, baseEnd_2442744] using wordTrace_append hprefix tailTrace_2442744
  have hstable : (prefixWord ++ tailWord_2442744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442744).length < 2 ^ (prefixWord ++ tailWord_2442744).sum := by decide
  have hdescent : baseEnd_2442744 < baseStart_2442744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442748 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_2442748 : Nat := 118140960795 + 2442748 * 2 ^ 59
def prefixEnd_2442748 : Nat := 4983230072969 + 3 ^ 40 * 2442748 * 2
def baseEnd_2442748 : Nat := 836202561206075980610675

theorem tailTrace_2442748 : CollatzResearch.WordTrace tailWord_2442748 prefixEnd_2442748 836202561206075980610675 := by
  unfold tailWord_2442748
  simp only [CollatzResearch.WordTrace]
  refine ⟨44547169477174329494732449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59396225969565772659643265 44547169477174329494732449)
  ·
    refine ⟨33410377107880747121049337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44547169477174329494732449 33410377107880747121049337)
    ·
      refine ⟨25057782830910560340787003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33410377107880747121049337 25057782830910560340787003)
      ·
        refine ⟨37586674246365840511180505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25057782830910560340787003 37586674246365840511180505)
        ·
          refine ⟨28190005684774380383385379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37586674246365840511180505 28190005684774380383385379)
          ·
            refine ⟨42285008527161570575078069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28190005684774380383385379 42285008527161570575078069)
            ·
              refine ⟨3964219549421397241413569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42285008527161570575078069 3964219549421397241413569)
              ·
                refine ⟨2973164662066047931060177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3964219549421397241413569 2973164662066047931060177)
                ·
                  refine ⟨2229873496549535948295133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2973164662066047931060177 2229873496549535948295133)
                  ·
                    refine ⟨836202561206075980610675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2229873496549535948295133 836202561206075980610675)
                    ·
                      rfl

theorem cell22_2442748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_2442748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442748 prefixEnd_2442748 := by exact prefixLift 2442748
  have htrace : WordTrace (prefixWord ++ tailWord_2442748) baseStart_2442748 baseEnd_2442748 := by
    simpa [prefixWord, tailWord_2442748, baseEnd_2442748] using wordTrace_append hprefix tailTrace_2442748
  have hstable : (prefixWord ++ tailWord_2442748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442748).length < 2 ^ (prefixWord ++ tailWord_2442748).sum := by decide
  have hdescent : baseEnd_2442748 < baseStart_2442748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2442750 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 6]
def baseStart_2442750 : Nat := 118140960795 + 2442750 * 2 ^ 59
def prefixEnd_2442750 : Nat := 4983230072969 + 3 ^ 40 * 2442750 * 2
def baseEnd_2442750 : Nat := 278734415282316214020223

theorem tailTrace_2442750 : CollatzResearch.WordTrace tailWord_2442750 prefixEnd_2442750 278734415282316214020223 := by
  unfold tailWord_2442750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136801487542676666379713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59396274600227608887358469 11136801487542676666379713)
  ·
    refine ⟨8352601115657007499784785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11136801487542676666379713 8352601115657007499784785)
    ·
      refine ⟨6264450836742755624838589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8352601115657007499784785 6264450836742755624838589)
      ·
        refine ⟨2349169063778533359314471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6264450836742755624838589 2349169063778533359314471)
        ·
          refine ⟨3523753595667800038971707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349169063778533359314471 3523753595667800038971707)
          ·
            refine ⟨5285630393501700058457561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523753595667800038971707 5285630393501700058457561)
            ·
              refine ⟨3964222795126275043843171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5285630393501700058457561 3964222795126275043843171)
              ·
                refine ⟨5946334192689412565764757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964222795126275043843171 5946334192689412565764757)
                ·
                  refine ⟨278734415282316214020223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5946334192689412565764757 278734415282316214020223)
                  ·
                    rfl

theorem cell22_2442750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_2442750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2442750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2442750 prefixEnd_2442750 := by exact prefixLift 2442750
  have htrace : WordTrace (prefixWord ++ tailWord_2442750) baseStart_2442750 baseEnd_2442750 := by
    simpa [prefixWord, tailWord_2442750, baseEnd_2442750] using wordTrace_append hprefix tailTrace_2442750
  have hstable : (prefixWord ++ tailWord_2442750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2442750).length < 2 ^ (prefixWord ++ tailWord_2442750).sum := by decide
  have hdescent : baseEnd_2442750 < baseStart_2442750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2442750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
