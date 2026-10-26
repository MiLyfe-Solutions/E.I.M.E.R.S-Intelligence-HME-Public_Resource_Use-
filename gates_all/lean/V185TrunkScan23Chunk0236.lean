import V185TrunkScan23Chunk0235

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1396384 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 1, 4, 2]
def baseStart_1396384 : Nat := 118140960795 + 1396384 * 2 ^ 59
def prefixEnd_1396384 : Nat := 4983230072969 + 3 ^ 40 * 1396384 * 2
def baseEnd_1396384 : Nat := 717016170247969874878153

theorem tailTrace_1396384 : CollatzResearch.WordTrace tailWord_1396384 prefixEnd_1396384 717016170247969874878153 := by
  unfold tailWord_1396384
  simp only [CollatzResearch.WordTrace]
  refine ⟨25465154286573363122838103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33953539048764484163784137 25465154286573363122838103)
  ·
    refine ⟨38197731429860044684257155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25465154286573363122838103 38197731429860044684257155)
    ·
      refine ⟨57296597144790067026385733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38197731429860044684257155 57296597144790067026385733)
      ·
        refine ⟨10743111964648137567447325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57296597144790067026385733 10743111964648137567447325)
        ·
          refine ⟨4028666986743051587792747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10743111964648137567447325 4028666986743051587792747)
          ·
            refine ⟨6043000480114577381689121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028666986743051587792747 6043000480114577381689121)
            ·
              refine ⟨4532250360085933036266841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6043000480114577381689121 4532250360085933036266841)
              ·
                refine ⟨3399187770064449777200131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4532250360085933036266841 3399187770064449777200131)
                ·
                  refine ⟨5098781655096674665800197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399187770064449777200131 5098781655096674665800197)
                  ·
                    refine ⟨956021560330626499837537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5098781655096674665800197 956021560330626499837537)
                    ·
                      refine ⟨717016170247969874878153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956021560330626499837537 717016170247969874878153)
                      ·
                        rfl

theorem cell23_1396384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_1396384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396384 prefixEnd_1396384 := by exact prefixLift 1396384
  have htrace : WordTrace (prefixWord ++ tailWord_1396384) baseStart_1396384 baseEnd_1396384 := by
    simpa [prefixWord, tailWord_1396384, baseEnd_1396384] using wordTrace_append hprefix tailTrace_1396384
  have hstable : (prefixWord ++ tailWord_1396384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396384).length < 2 ^ (prefixWord ++ tailWord_1396384).sum := by decide
  have hdescent : baseEnd_1396384 < baseStart_1396384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396388 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 1, 3, 2]
def baseStart_1396388 : Nat := 118140960795 + 1396388 * 2 ^ 59
def prefixEnd_1396388 : Nat := 4983230072969 + 3 ^ 40 * 1396388 * 2
def baseEnd_1396388 : Nat := 717018224170587859228135

theorem tailTrace_1396388 : CollatzResearch.WordTrace tailWord_1396388 prefixEnd_1396388 717018224170587859228135 := by
  unfold tailWord_1396388
  simp only [CollatzResearch.WordTrace]
  refine ⟨25465227232566117464410909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33953636310088156619214545 25465227232566117464410909)
  ·
    refine ⟨9549460212212294049154091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25465227232566117464410909 9549460212212294049154091)
    ·
      refine ⟨14324190318318441073731137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9549460212212294049154091 14324190318318441073731137)
      ·
        refine ⟨10743142738738830805298353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14324190318318441073731137 10743142738738830805298353)
        ·
          refine ⟨8057357054054123103973765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10743142738738830805298353 8057357054054123103973765)
          ·
            refine ⟨1510754447635148081995081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8057357054054123103973765 1510754447635148081995081)
            ·
              refine ⟨1133065835726361061496311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510754447635148081995081 1133065835726361061496311)
              ·
                refine ⟨1699598753589541592244467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133065835726361061496311 1699598753589541592244467)
                ·
                  refine ⟨2549398130384312388366701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699598753589541592244467 2549398130384312388366701)
                  ·
                    refine ⟨956024298894117145637513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549398130384312388366701 956024298894117145637513)
                    ·
                      refine ⟨717018224170587859228135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956024298894117145637513 717018224170587859228135)
                      ·
                        rfl

theorem cell23_1396388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_1396388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396388 prefixEnd_1396388 := by exact prefixLift 1396388
  have htrace : WordTrace (prefixWord ++ tailWord_1396388) baseStart_1396388 baseEnd_1396388 := by
    simpa [prefixWord, tailWord_1396388, baseEnd_1396388] using wordTrace_append hprefix tailTrace_1396388
  have hstable : (prefixWord ++ tailWord_1396388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396388).length < 2 ^ (prefixWord ++ tailWord_1396388).sum := by decide
  have hdescent : baseEnd_1396388 < baseStart_1396388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396397 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1396397 : Nat := 118140960795 + 1396397 * 2 ^ 59
def prefixEnd_1396397 : Nat := 4983230072969 + 3 ^ 40 * 1396397 * 2
def baseEnd_1396397 : Nat := 717022845496478324015593

theorem tailTrace_1396397 : CollatzResearch.WordTrace tailWord_1396397 prefixEnd_1396397 717022845496478324015593 := by
  unfold tailWord_1396397
  simp only [CollatzResearch.WordTrace]
  refine ⟨50930782722099629465899445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33953855148066419643932963 50930782722099629465899445)
  ·
    refine ⟨4774760880196840262428073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50930782722099629465899445 4774760880196840262428073)
    ·
      refine ⟨3581070660147630196821055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4774760880196840262428073 3581070660147630196821055)
      ·
        refine ⟨5371605990221445295231583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3581070660147630196821055 5371605990221445295231583)
        ·
          refine ⟨8057408985332167942847375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371605990221445295231583 8057408985332167942847375)
          ·
            refine ⟨12086113477998251914271063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8057408985332167942847375 12086113477998251914271063)
            ·
              refine ⟨18129170216997377871406595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12086113477998251914271063 18129170216997377871406595)
              ·
                refine ⟨27193755325496066807109893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18129170216997377871406595 27193755325496066807109893)
                ·
                  refine ⟨5098829123530512526333105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27193755325496066807109893 5098829123530512526333105)
                  ·
                    refine ⟨3824121842647884394749829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5098829123530512526333105 3824121842647884394749829)
                    ·
                      refine ⟨717022845496478324015593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3824121842647884394749829 717022845496478324015593)
                      ·
                        rfl

theorem cell23_1396397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1396397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396397 prefixEnd_1396397 := by exact prefixLift 1396397
  have htrace : WordTrace (prefixWord ++ tailWord_1396397) baseStart_1396397 baseEnd_1396397 := by
    simpa [prefixWord, tailWord_1396397, baseEnd_1396397] using wordTrace_append hprefix tailTrace_1396397
  have hstable : (prefixWord ++ tailWord_1396397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396397).length < 2 ^ (prefixWord ++ tailWord_1396397).sum := by decide
  have hdescent : baseEnd_1396397 < baseStart_1396397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396407 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 7]
def baseStart_1396407 : Nat := 118140960795 + 1396407 * 2 ^ 59
def prefixEnd_1396407 : Nat := 4983230072969 + 3 ^ 40 * 1396407 * 2
def baseEnd_1396407 : Nat := 79669775589224809432283

theorem tailTrace_1396407 : CollatzResearch.WordTrace tailWord_1396407 prefixEnd_1396407 79669775589224809432283 := by
  unfold tailWord_1396407
  simp only [CollatzResearch.WordTrace]
  refine ⟨50931147452063401173763475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33954098301375600782508983 50931147452063401173763475)
  ·
    refine ⟨76396721178095101760645213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50931147452063401173763475 76396721178095101760645213)
    ·
      refine ⟨28648770441785663160241955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76396721178095101760645213 28648770441785663160241955)
      ·
        refine ⟨42973155662678494740362933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28648770441785663160241955 42973155662678494740362933)
        ·
          refine ⟨4028733343376108881909025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42973155662678494740362933 4028733343376108881909025)
          ·
            refine ⟨3021550007532081661431769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4028733343376108881909025 3021550007532081661431769)
            ·
              refine ⟨2266162505649061246073827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3021550007532081661431769 2266162505649061246073827)
              ·
                refine ⟨3399243758473591869110741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266162505649061246073827 3399243758473591869110741)
                ·
                  refine ⟨79669775589224809432283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3399243758473591869110741 79669775589224809432283)
                  ·
                    rfl

theorem cell23_1396407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 7].length) (baseStart_1396407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396407 prefixEnd_1396407 := by exact prefixLift 1396407
  have htrace : WordTrace (prefixWord ++ tailWord_1396407) baseStart_1396407 baseEnd_1396407 := by
    simpa [prefixWord, tailWord_1396407, baseEnd_1396407] using wordTrace_append hprefix tailTrace_1396407
  have hstable : (prefixWord ++ tailWord_1396407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396407).length < 2 ^ (prefixWord ++ tailWord_1396407).sum := by decide
  have hdescent : baseEnd_1396407 < baseStart_1396407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396427 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 2, 5, 2]
def baseStart_1396427 : Nat := 118140960795 + 1396427 * 2 ^ 59
def prefixEnd_1396427 : Nat := 4983230072969 + 3 ^ 40 * 1396427 * 2
def baseEnd_1396427 : Nat := 717038249916113206640455

theorem tailTrace_1396427 : CollatzResearch.WordTrace tailWord_1396427 prefixEnd_1396427 717038249916113206640455 := by
  unfold tailWord_1396427
  simp only [CollatzResearch.WordTrace]
  refine ⟨50931876911990944589491535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33954584607993963059661023 50931876911990944589491535)
  ·
    refine ⟨76397815367986416884237303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50931876911990944589491535 76397815367986416884237303)
    ·
      refine ⟨114596723051979625326355955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76397815367986416884237303 114596723051979625326355955)
      ·
        refine ⟨171895084577969437989533933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114596723051979625326355955 171895084577969437989533933)
        ·
          refine ⟨64460656716738539246075225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171895084577969437989533933 64460656716738539246075225)
          ·
            refine ⟨48345492537553904434556419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64460656716738539246075225 48345492537553904434556419)
            ·
              refine ⟨72518238806330856651834629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48345492537553904434556419 72518238806330856651834629)
              ·
                refine ⟨13597169776187035622218993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72518238806330856651834629 13597169776187035622218993)
                ·
                  refine ⟨10197877332140276716664245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13597169776187035622218993 10197877332140276716664245)
                  ·
                    refine ⟨956050999888150942187273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10197877332140276716664245 956050999888150942187273)
                    ·
                      refine ⟨717038249916113206640455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956050999888150942187273 717038249916113206640455)
                      ·
                        rfl

theorem cell23_1396427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 5, 2].length) (baseStart_1396427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396427 prefixEnd_1396427 := by exact prefixLift 1396427
  have htrace : WordTrace (prefixWord ++ tailWord_1396427) baseStart_1396427 baseEnd_1396427 := by
    simpa [prefixWord, tailWord_1396427, baseEnd_1396427] using wordTrace_append hprefix tailTrace_1396427
  have hstable : (prefixWord ++ tailWord_1396427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396427).length < 2 ^ (prefixWord ++ tailWord_1396427).sum := by decide
  have hdescent : baseEnd_1396427 < baseStart_1396427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396477 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1396477 : Nat := 118140960795 + 1396477 * 2 ^ 59
def prefixEnd_1396477 : Nat := 4983230072969 + 3 ^ 40 * 1396477 * 2
def baseEnd_1396477 : Nat := 717063923948838011015225

theorem tailTrace_1396477 : CollatzResearch.WordTrace tailWord_1396477 prefixEnd_1396477 717063923948838011015225 := by
  unfold tailWord_1396477
  simp only [CollatzResearch.WordTrace]
  refine ⟨50933700561809803128811685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33955800374539868752541123 50933700561809803128811685)
  ·
    refine ⟨9550068855339338086652191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50933700561809803128811685 9550068855339338086652191)
    ·
      refine ⟨14325103283009007129978287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9550068855339338086652191 14325103283009007129978287)
      ·
        refine ⟨21487654924513510694967431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14325103283009007129978287 21487654924513510694967431)
        ·
          refine ⟨32231482386770266042451147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21487654924513510694967431 32231482386770266042451147)
          ·
            refine ⟨48347223580155399063676721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32231482386770266042451147 48347223580155399063676721)
            ·
              refine ⟨36260417685116549297757541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48347223580155399063676721 36260417685116549297757541)
              ·
                refine ⟨6798828315959352993329539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36260417685116549297757541 6798828315959352993329539)
                ·
                  refine ⟨10198242473939029489994309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6798828315959352993329539 10198242473939029489994309)
                  ·
                    refine ⟨1912170463863568029373933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10198242473939029489994309 1912170463863568029373933)
                    ·
                      refine ⟨717063923948838011015225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1912170463863568029373933 717063923948838011015225)
                      ·
                        rfl

theorem cell23_1396477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1396477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396477 prefixEnd_1396477 := by exact prefixLift 1396477
  have htrace : WordTrace (prefixWord ++ tailWord_1396477) baseStart_1396477 baseEnd_1396477 := by
    simpa [prefixWord, tailWord_1396477, baseEnd_1396477] using wordTrace_append hprefix tailTrace_1396477
  have hstable : (prefixWord ++ tailWord_1396477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396477).length < 2 ^ (prefixWord ++ tailWord_1396477).sum := by decide
  have hdescent : baseEnd_1396477 < baseStart_1396477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396494 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1396494 : Nat := 118140960795 + 1396494 * 2 ^ 59
def prefixEnd_1396494 : Nat := 4983230072969 + 3 ^ 40 * 1396494 * 2
def baseEnd_1396494 : Nat := 717072653119964444502647

theorem tailTrace_1396494 : CollatzResearch.WordTrace tailWord_1396494 prefixEnd_1396494 717072653119964444502647 := by
  unfold tailWord_1396494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6366790075343526879022567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33956213735165476688120357 6366790075343526879022567)
  ·
    refine ⟨9550185113015290318533851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6366790075343526879022567 9550185113015290318533851)
    ·
      refine ⟨14325277669522935477800777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9550185113015290318533851 14325277669522935477800777)
      ·
        refine ⟨10743958252142201608350583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14325277669522935477800777 10743958252142201608350583)
        ·
          refine ⟨16115937378213302412525875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10743958252142201608350583 16115937378213302412525875)
          ·
            refine ⟨24173906067319953618788813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16115937378213302412525875 24173906067319953618788813)
            ·
              refine ⟨9065214775244982607045805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24173906067319953618788813 9065214775244982607045805)
              ·
                refine ⟨3399455540716868477642177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9065214775244982607045805 3399455540716868477642177)
                ·
                  refine ⟨2549591655537651358231633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3399455540716868477642177 2549591655537651358231633)
                  ·
                    refine ⟨1912193741653238518673725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2549591655537651358231633 1912193741653238518673725)
                    ·
                      refine ⟨717072653119964444502647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1912193741653238518673725 717072653119964444502647)
                      ·
                        rfl

theorem cell23_1396494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1396494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396494 prefixEnd_1396494 := by exact prefixLift 1396494
  have htrace : WordTrace (prefixWord ++ tailWord_1396494) baseStart_1396494 baseEnd_1396494 := by
    simpa [prefixWord, tailWord_1396494, baseEnd_1396494] using wordTrace_append hprefix tailTrace_1396494
  have hstable : (prefixWord ++ tailWord_1396494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396494).length < 2 ^ (prefixWord ++ tailWord_1396494).sum := by decide
  have hdescent : baseEnd_1396494 < baseStart_1396494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396514 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 6]
def baseStart_1396514 : Nat := 118140960795 + 1396514 * 2 ^ 59
def prefixEnd_1396514 : Nat := 4983230072969 + 3 ^ 40 * 1396514 * 2
def baseEnd_1396514 : Nat := 79675880303672707361395

theorem tailTrace_1396514 : CollatzResearch.WordTrace tailWord_1396514 prefixEnd_1396514 79675880303672707361395 := by
  unfold tailWord_1396514
  simp only [CollatzResearch.WordTrace]
  refine ⟨12733762515668939611977149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33956700041783838965272397 12733762515668939611977149)
  ·
    refine ⟨4775160943375852354491431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12733762515668939611977149 4775160943375852354491431)
    ·
      refine ⟨7162741415063778531737147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4775160943375852354491431 7162741415063778531737147)
      ·
        refine ⟨10744112122595667797605721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7162741415063778531737147 10744112122595667797605721)
        ·
          refine ⟨8058084091946750848204291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10744112122595667797605721 8058084091946750848204291)
          ·
            refine ⟨12087126137920126272306437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8058084091946750848204291 12087126137920126272306437)
            ·
              refine ⟨2266336150860023676057457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12087126137920126272306437 2266336150860023676057457)
              ·
                refine ⟨1699752113145017757043093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266336150860023676057457 1699752113145017757043093)
                ·
                  refine ⟨79675880303672707361395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1699752113145017757043093 79675880303672707361395)
                  ·
                    rfl

theorem cell23_1396514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_1396514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396514 prefixEnd_1396514 := by exact prefixLift 1396514
  have htrace : WordTrace (prefixWord ++ tailWord_1396514) baseStart_1396514 baseEnd_1396514 := by
    simpa [prefixWord, tailWord_1396514, baseEnd_1396514] using wordTrace_append hprefix tailTrace_1396514
  have hstable : (prefixWord ++ tailWord_1396514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396514).length < 2 ^ (prefixWord ++ tailWord_1396514).sum := by decide
  have hdescent : baseEnd_1396514 < baseStart_1396514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396541 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1396541 : Nat := 118140960795 + 1396541 * 2 ^ 59
def prefixEnd_1396541 : Nat := 4983230072969 + 3 ^ 40 * 1396541 * 2
def baseEnd_1396541 : Nat := 717096786710725760614931

theorem tailTrace_1396541 : CollatzResearch.WordTrace tailWord_1396541 prefixEnd_1396541 717096786710725760614931 := by
  unfold tailWord_1396541
  simp only [CollatzResearch.WordTrace]
  refine ⟨50936034833577942059141477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33957356555718628039427651 50936034833577942059141477)
  ·
    refine ⟨9550506531295864136089027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50936034833577942059141477 9550506531295864136089027)
    ·
      refine ⟨14325759796943796204133541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9550506531295864136089027 14325759796943796204133541)
      ·
        refine ⟨2686079961926961788275039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14325759796943796204133541 2686079961926961788275039)
        ·
          refine ⟨4029119942890442682412559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2686079961926961788275039 4029119942890442682412559)
          ·
            refine ⟨6043679914335664023618839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029119942890442682412559 6043679914335664023618839)
            ·
              refine ⟨9065519871503496035428259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6043679914335664023618839 9065519871503496035428259)
              ·
                refine ⟨13598279807255244053142389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9065519871503496035428259 13598279807255244053142389)
                ·
                  refine ⟨1274838731930179129982099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13598279807255244053142389 1274838731930179129982099)
                  ·
                    refine ⟨1912258097895268694973149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274838731930179129982099 1912258097895268694973149)
                    ·
                      refine ⟨717096786710725760614931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1912258097895268694973149 717096786710725760614931)
                      ·
                        rfl

theorem cell23_1396541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1396541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396541 prefixEnd_1396541 := by exact prefixLift 1396541
  have htrace : WordTrace (prefixWord ++ tailWord_1396541) baseStart_1396541 baseEnd_1396541 := by
    simpa [prefixWord, tailWord_1396541, baseEnd_1396541] using wordTrace_append hprefix tailTrace_1396541
  have hstable : (prefixWord ++ tailWord_1396541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396541).length < 2 ^ (prefixWord ++ tailWord_1396541).sum := by decide
  have hdescent : baseEnd_1396541 < baseStart_1396541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396551 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 2, 3, 2]
def baseStart_1396551 : Nat := 118140960795 + 1396551 * 2 ^ 59
def prefixEnd_1396551 : Nat := 4983230072969 + 3 ^ 40 * 1396551 * 2
def baseEnd_1396551 : Nat := 717101921517270721489885

theorem tailTrace_1396551 : CollatzResearch.WordTrace tailWord_1396551 prefixEnd_1396551 717101921517270721489885 := by
  unfold tailWord_1396551
  simp only [CollatzResearch.WordTrace]
  refine ⟨50936399563541713767005507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33957599709027809178003671 50936399563541713767005507)
  ·
    refine ⟨76404599345312570650508261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50936399563541713767005507 76404599345312570650508261)
    ·
      refine ⟨14325862377246106996970299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76404599345312570650508261 14325862377246106996970299)
      ·
        refine ⟨21488793565869160495455449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14325862377246106996970299 21488793565869160495455449)
        ·
          refine ⟨16116595174401870371591587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21488793565869160495455449 16116595174401870371591587)
          ·
            refine ⟨24174892761602805557387381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16116595174401870371591587 24174892761602805557387381)
            ·
              refine ⟨2266396196400263021005067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24174892761602805557387381 2266396196400263021005067)
              ·
                refine ⟨3399594294600394531507601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266396196400263021005067 3399594294600394531507601)
                ·
                  refine ⟨2549695720950295898630701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3399594294600394531507601 2549695720950295898630701)
                  ·
                    refine ⟨956135895356360961986513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2549695720950295898630701 956135895356360961986513)
                    ·
                      refine ⟨717101921517270721489885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956135895356360961986513 717101921517270721489885)
                      ·
                        rfl

theorem cell23_1396551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_1396551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396551 prefixEnd_1396551 := by exact prefixLift 1396551
  have htrace : WordTrace (prefixWord ++ tailWord_1396551) baseStart_1396551 baseEnd_1396551 := by
    simpa [prefixWord, tailWord_1396551, baseEnd_1396551] using wordTrace_append hprefix tailTrace_1396551
  have hstable : (prefixWord ++ tailWord_1396551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396551).length < 2 ^ (prefixWord ++ tailWord_1396551).sum := by decide
  have hdescent : baseEnd_1396551 < baseStart_1396551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396561 : List Nat := [1, 2, 2, 1, 5, 1, 4, 1, 1, 5]
def baseStart_1396561 : Nat := 118140960795 + 1396561 * 2 ^ 59
def prefixEnd_1396561 : Nat := 4983230072969 + 3 ^ 40 * 1396561 * 2
def baseEnd_1396561 : Nat := 239035685441271894121613

theorem tailTrace_1396561 : CollatzResearch.WordTrace tailWord_1396561 prefixEnd_1396561 239035685441271894121613 := by
  unfold tailWord_1396561
  simp only [CollatzResearch.WordTrace]
  refine ⟨50936764293505485474869537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33957842862336990316579691 50936764293505485474869537)
  ·
    refine ⟨38202573220129114106152153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50936764293505485474869537 38202573220129114106152153)
    ·
      refine ⟨28651929915096835579614115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38202573220129114106152153 28651929915096835579614115)
      ·
        refine ⟨42977894872645253369421173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28651929915096835579614115 42977894872645253369421173)
        ·
          refine ⟨4029177644310492503383235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42977894872645253369421173 4029177644310492503383235)
          ·
            refine ⟨6043766466465738755074853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029177644310492503383235 6043766466465738755074853)
            ·
              refine ⟨1133206212462326016576535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6043766466465738755074853 1133206212462326016576535)
              ·
                refine ⟨1699809318693489024864803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133206212462326016576535 1699809318693489024864803)
                ·
                  refine ⟨2549713978040233537297205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699809318693489024864803 2549713978040233537297205)
                  ·
                    refine ⟨239035685441271894121613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2549713978040233537297205 239035685441271894121613)
                    ·
                      rfl

theorem cell23_1396561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_1396561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396561 prefixEnd_1396561 := by exact prefixLift 1396561
  have htrace : WordTrace (prefixWord ++ tailWord_1396561) baseStart_1396561 baseEnd_1396561 := by
    simpa [prefixWord, tailWord_1396561, baseEnd_1396561] using wordTrace_append hprefix tailTrace_1396561
  have hstable : (prefixWord ++ tailWord_1396561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396561).length < 2 ^ (prefixWord ++ tailWord_1396561).sum := by decide
  have hdescent : baseEnd_1396561 < baseStart_1396561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396577 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_1396577 : Nat := 118140960795 + 1396577 * 2 ^ 59
def prefixEnd_1396577 : Nat := 4983230072969 + 3 ^ 40 * 1396577 * 2
def baseEnd_1396577 : Nat := 717115272014287619764765

theorem tailTrace_1396577 : CollatzResearch.WordTrace tailWord_1396577 prefixEnd_1396577 717115272014287619764765 := by
  unfold tailWord_1396577
  simp only [CollatzResearch.WordTrace]
  refine ⟨50937347861447520207451985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33958231907631680138301323 50937347861447520207451985)
  ·
    refine ⟨38203010896085640155588989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50937347861447520207451985 38203010896085640155588989)
    ·
      refine ⟨14326129086032115058345871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38203010896085640155588989 14326129086032115058345871)
      ·
        refine ⟨21489193629048172587518807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14326129086032115058345871 21489193629048172587518807)
        ·
          refine ⟨32233790443572258881278211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21489193629048172587518807 32233790443572258881278211)
          ·
            refine ⟨48350685665358388321917317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32233790443572258881278211 48350685665358388321917317)
            ·
              refine ⟨9065753562254697810359497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48350685665358388321917317 9065753562254697810359497)
              ·
                refine ⟨6799315171691023357769623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9065753562254697810359497 6799315171691023357769623)
                ·
                  refine ⟨10198972757536535036654435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6799315171691023357769623 10198972757536535036654435)
                  ·
                    refine ⟨15298459136304802554981653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10198972757536535036654435 15298459136304802554981653)
                    ·
                      refine ⟨717115272014287619764765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15298459136304802554981653 717115272014287619764765)
                      ·
                        rfl

theorem cell23_1396577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_1396577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396577 prefixEnd_1396577 := by exact prefixLift 1396577
  have htrace : WordTrace (prefixWord ++ tailWord_1396577) baseStart_1396577 baseEnd_1396577 := by
    simpa [prefixWord, tailWord_1396577, baseEnd_1396577] using wordTrace_append hprefix tailTrace_1396577
  have hstable : (prefixWord ++ tailWord_1396577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396577).length < 2 ^ (prefixWord ++ tailWord_1396577).sum := by decide
  have hdescent : baseEnd_1396577 < baseStart_1396577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396584 : List Nat := [2, 1, 4, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1396584 : Nat := 118140960795 + 1396584 * 2 ^ 59
def prefixEnd_1396584 : Nat := 4983230072969 + 3 ^ 40 * 1396584 * 2
def baseEnd_1396584 : Nat := 717118866378869092377233

theorem tailTrace_1396584 : CollatzResearch.WordTrace tailWord_1396584 prefixEnd_1396584 717118866378869092377233 := by
  unfold tailWord_1396584
  simp only [CollatzResearch.WordTrace]
  refine ⟨25468801586211080201478403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33958402114948106935304537 25468801586211080201478403)
  ·
    refine ⟨38203202379316620302217605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25468801586211080201478403 38203202379316620302217605)
    ·
      refine ⟨7163100446121866306665801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38203202379316620302217605 7163100446121866306665801)
      ·
        refine ⟨5372325334591399729999351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7163100446121866306665801 5372325334591399729999351)
        ·
          refine ⟨8058488001887099594999027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5372325334591399729999351 8058488001887099594999027)
          ·
            refine ⟨12087732002830649392498541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8058488001887099594999027 12087732002830649392498541)
            ·
              refine ⟨4532899501061493522186953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12087732002830649392498541 4532899501061493522186953)
              ·
                refine ⟨3399674625796120141640215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4532899501061493522186953 3399674625796120141640215)
                ·
                  refine ⟨5099511938694180212460323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399674625796120141640215 5099511938694180212460323)
                  ·
                    refine ⟨7649267908041270318690485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5099511938694180212460323 7649267908041270318690485)
                    ·
                      refine ⟨717118866378869092377233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7649267908041270318690485 717118866378869092377233)
                      ·
                        rfl

theorem cell23_1396584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1396584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396584 prefixEnd_1396584 := by exact prefixLift 1396584
  have htrace : WordTrace (prefixWord ++ tailWord_1396584) baseStart_1396584 baseEnd_1396584 := by
    simpa [prefixWord, tailWord_1396584, baseEnd_1396584] using wordTrace_append hprefix tailTrace_1396584
  have hstable : (prefixWord ++ tailWord_1396584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396584).length < 2 ^ (prefixWord ++ tailWord_1396584).sum := by decide
  have hdescent : baseEnd_1396584 < baseStart_1396584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396601 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 3]
def baseStart_1396601 : Nat := 118140960795 + 1396601 * 2 ^ 59
def prefixEnd_1396601 : Nat := 4983230072969 + 3 ^ 40 * 1396601 * 2
def baseEnd_1396601 : Nat := 717127595549995525864655

theorem tailTrace_1396601 : CollatzResearch.WordTrace tailWord_1396601 prefixEnd_1396601 717127595549995525864655 := by
  unfold tailWord_1396601
  simp only [CollatzResearch.WordTrace]
  refine ⟨50938223213360572306325657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33958815475573714870883771 50938223213360572306325657)
  ·
    refine ⟨38203667410020429229744243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50938223213360572306325657 38203667410020429229744243)
    ·
      refine ⟨57305501115030643844616365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38203667410020429229744243 57305501115030643844616365)
      ·
        refine ⟨21489562918136491441731137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57305501115030643844616365 21489562918136491441731137)
        ·
          refine ⟨16117172188602368581298353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21489562918136491441731137 16117172188602368581298353)
          ·
            refine ⟨12087879141451776435973765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16117172188602368581298353 12087879141451776435973765)
            ·
              refine ⟨2266477339022208081745081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12087879141451776435973765 2266477339022208081745081)
              ·
                refine ⟨1699858004266656061308811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2266477339022208081745081 1699858004266656061308811)
                ·
                  refine ⟨2549787006399984091963217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1699858004266656061308811 2549787006399984091963217)
                  ·
                    refine ⟨1912340254799988068972413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2549787006399984091963217 1912340254799988068972413)
                    ·
                      refine ⟨717127595549995525864655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1912340254799988068972413 717127595549995525864655)
                      ·
                        rfl

theorem cell23_1396601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_1396601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396601 prefixEnd_1396601 := by exact prefixLift 1396601
  have htrace : WordTrace (prefixWord ++ tailWord_1396601) baseStart_1396601 baseEnd_1396601 := by
    simpa [prefixWord, tailWord_1396601, baseEnd_1396601] using wordTrace_append hprefix tailTrace_1396601
  have hstable : (prefixWord ++ tailWord_1396601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396601).length < 2 ^ (prefixWord ++ tailWord_1396601).sum := by decide
  have hdescent : baseEnd_1396601 < baseStart_1396601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396609 : List Nat := [1, 2, 4, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1396609 : Nat := 118140960795 + 1396609 * 2 ^ 59
def prefixEnd_1396609 : Nat := 4983230072969 + 3 ^ 40 * 1396609 * 2
def baseEnd_1396609 : Nat := 717131703395231494564619

theorem tailTrace_1396609 : CollatzResearch.WordTrace tailWord_1396609 prefixEnd_1396609 717131703395231494564619 := by
  unfold tailWord_1396609
  simp only [CollatzResearch.WordTrace]
  refine ⟨50938514997331589672616881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33959009998221059781744587 50938514997331589672616881)
  ·
    refine ⟨38203886247998692254462661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50938514997331589672616881 38203886247998692254462661)
    ·
      refine ⟨7163228671499754797711749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38203886247998692254462661 7163228671499754797711749)
      ·
        refine ⟨1343105375906204024570953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7163228671499754797711749 1343105375906204024570953)
        ·
          refine ⟨1007329031929653018428215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343105375906204024570953 1007329031929653018428215)
          ·
            refine ⟨1510993547894479527642323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007329031929653018428215 1510993547894479527642323)
            ·
              refine ⟨2266490321841719291463485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510993547894479527642323 2266490321841719291463485)
              ·
                refine ⟨849933870690644734298807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2266490321841719291463485 849933870690644734298807)
                ·
                  refine ⟨1274900806035967101448211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 849933870690644734298807 1274900806035967101448211)
                  ·
                    refine ⟨1912351209053950652172317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274900806035967101448211 1912351209053950652172317)
                    ·
                      refine ⟨717131703395231494564619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1912351209053950652172317 717131703395231494564619)
                      ·
                        rfl

theorem cell23_1396609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1396609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396609 prefixEnd_1396609 := by exact prefixLift 1396609
  have htrace : WordTrace (prefixWord ++ tailWord_1396609) baseStart_1396609 baseEnd_1396609 := by
    simpa [prefixWord, tailWord_1396609, baseEnd_1396609] using wordTrace_append hprefix tailTrace_1396609
  have hstable : (prefixWord ++ tailWord_1396609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396609).length < 2 ^ (prefixWord ++ tailWord_1396609).sum := by decide
  have hdescent : baseEnd_1396609 < baseStart_1396609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396631 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 3]
def baseStart_1396631 : Nat := 118140960795 + 1396631 * 2 ^ 59
def prefixEnd_1396631 : Nat := 4983230072969 + 3 ^ 40 * 1396631 * 2
def baseEnd_1396631 : Nat := 717142999969630408489517

theorem tailTrace_1396631 : CollatzResearch.WordTrace tailWord_1396631 prefixEnd_1396631 717142999969630408489517 := by
  unfold tailWord_1396631
  simp only [CollatzResearch.WordTrace]
  refine ⟨50939317403251887429917747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33959544935501258286611831 50939317403251887429917747)
  ·
    refine ⟨76408976104877831144876621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50939317403251887429917747 76408976104877831144876621)
    ·
      refine ⟨28653366039329186679328733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76408976104877831144876621 28653366039329186679328733)
      ·
        refine ⟨10745012264748445004748275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28653366039329186679328733 10745012264748445004748275)
        ·
          refine ⟨16117518397122667507122413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10745012264748445004748275 16117518397122667507122413)
          ·
            refine ⟨6044069398921000315170905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16117518397122667507122413 6044069398921000315170905)
            ·
              refine ⟨4533052049190750236378179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044069398921000315170905 4533052049190750236378179)
              ·
                refine ⟨6799578073786125354567269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4533052049190750236378179 6799578073786125354567269)
                ·
                  refine ⟨1274920888834898503981363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6799578073786125354567269 1274920888834898503981363)
                  ·
                    refine ⟨1912381333252347755972045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1274920888834898503981363 1912381333252347755972045)
                    ·
                      refine ⟨717142999969630408489517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1912381333252347755972045 717142999969630408489517)
                      ·
                        rfl

theorem cell23_1396631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_1396631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396631 prefixEnd_1396631 := by exact prefixLift 1396631
  have htrace : WordTrace (prefixWord ++ tailWord_1396631) baseStart_1396631 baseEnd_1396631 := by
    simpa [prefixWord, tailWord_1396631, baseEnd_1396631] using wordTrace_append hprefix tailTrace_1396631
  have hstable : (prefixWord ++ tailWord_1396631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396631).length < 2 ^ (prefixWord ++ tailWord_1396631).sum := by decide
  have hdescent : baseEnd_1396631 < baseStart_1396631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396632 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1396632 : Nat := 118140960795 + 1396632 * 2 ^ 59
def prefixEnd_1396632 : Nat := 4983230072969 + 3 ^ 40 * 1396632 * 2
def baseEnd_1396632 : Nat := 717143513450284904577013

theorem tailTrace_1396632 : CollatzResearch.WordTrace tailWord_1396632 prefixEnd_1396632 717143513450284904577013 := by
  unfold tailWord_1396632
  simp only [CollatzResearch.WordTrace]
  refine ⟨25469676938124132300352075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33959569250832176400469433 25469676938124132300352075)
  ·
    refine ⟨38204515407186198450528113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25469676938124132300352075 38204515407186198450528113)
    ·
      refine ⟨28653386555389648837896085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38204515407186198450528113 28653386555389648837896085)
      ·
        refine ⟨1343127494783889789276379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28653386555389648837896085 1343127494783889789276379)
        ·
          refine ⟨2014691242175834683914569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343127494783889789276379 2014691242175834683914569)
          ·
            refine ⟨1511018431631876012935927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2014691242175834683914569 1511018431631876012935927)
            ·
              refine ⟨2266527647447814019403891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511018431631876012935927 2266527647447814019403891)
              ·
                refine ⟨3399791471171721029105837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266527647447814019403891 3399791471171721029105837)
                ·
                  refine ⟨1274921801689395385914689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3399791471171721029105837 1274921801689395385914689)
                  ·
                    refine ⟨956191351267046539436017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1274921801689395385914689 956191351267046539436017)
                    ·
                      refine ⟨717143513450284904577013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956191351267046539436017 717143513450284904577013)
                      ·
                        rfl

theorem cell23_1396632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1396632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396632 prefixEnd_1396632 := by exact prefixLift 1396632
  have htrace : WordTrace (prefixWord ++ tailWord_1396632) baseStart_1396632 baseEnd_1396632 := by
    simpa [prefixWord, tailWord_1396632, baseEnd_1396632] using wordTrace_append hprefix tailTrace_1396632
  have hstable : (prefixWord ++ tailWord_1396632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396632).length < 2 ^ (prefixWord ++ tailWord_1396632).sum := by decide
  have hdescent : baseEnd_1396632 < baseStart_1396632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396638 : List Nat := [4, 3, 1, 3, 1, 1, 2, 8]
def baseStart_1396638 : Nat := 118140960795 + 1396638 * 2 ^ 59
def prefixEnd_1396638 : Nat := 4983230072969 + 3 ^ 40 * 1396638 * 2
def baseEnd_1396638 : Nat := 26560984975341180781555

theorem tailTrace_1396638 : CollatzResearch.WordTrace tailWord_1396638 prefixEnd_1396638 26560984975341180781555 := by
  unfold tailWord_1396638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6367446589278315953177821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33959715142817685083615045 6367446589278315953177821)
  ·
    refine ⟨2387792470979368482441683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6367446589278315953177821 2387792470979368482441683)
    ·
      refine ⟨3581688706469052723662525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2387792470979368482441683 3581688706469052723662525)
      ·
        refine ⟨1343133264925894771373447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3581688706469052723662525 1343133264925894771373447)
        ·
          refine ⟨2014699897388842157060171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343133264925894771373447 2014699897388842157060171)
          ·
            refine ⟨3022049846083263235590257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014699897388842157060171 3022049846083263235590257)
            ·
              refine ⟨2266537384562447426692693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022049846083263235590257 2266537384562447426692693)
              ·
                refine ⟨26560984975341180781555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2266537384562447426692693 26560984975341180781555)
                ·
                  rfl

theorem cell23_1396638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_1396638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396638 prefixEnd_1396638 := by exact prefixLift 1396638
  have htrace : WordTrace (prefixWord ++ tailWord_1396638) baseStart_1396638 baseEnd_1396638 := by
    simpa [prefixWord, tailWord_1396638, baseEnd_1396638] using wordTrace_append hprefix tailTrace_1396638
  have hstable : (prefixWord ++ tailWord_1396638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396638).length < 2 ^ (prefixWord ++ tailWord_1396638).sum := by decide
  have hdescent : baseEnd_1396638 < baseStart_1396638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396642 : List Nat := [3, 3, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_1396642 : Nat := 118140960795 + 1396642 * 2 ^ 59
def prefixEnd_1396642 : Nat := 4983230072969 + 3 ^ 40 * 1396642 * 2
def baseEnd_1396642 : Nat := 239049549418943288483989

theorem tailTrace_1396642 : CollatzResearch.WordTrace tailWord_1396642 prefixEnd_1396642 239049549418943288483989 := by
  unfold tailWord_1396642
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734929651553009077142045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33959812404141357539045453 12734929651553009077142045)
  ·
    refine ⟨4775598619332378403928267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12734929651553009077142045 4775598619332378403928267)
    ·
      refine ⟨7163397928998567605892401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4775598619332378403928267 7163397928998567605892401)
      ·
        refine ⟨5372548446748925704419301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7163397928998567605892401 5372548446748925704419301)
        ·
          refine ⟨1007352833765423569578619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5372548446748925704419301 1007352833765423569578619)
          ·
            refine ⟨1511029250648135354367929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007352833765423569578619 1511029250648135354367929)
            ·
              refine ⟨1133271937986101515775947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511029250648135354367929 1133271937986101515775947)
              ·
                refine ⟨1699907906979152273663921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133271937986101515775947 1699907906979152273663921)
                ·
                  refine ⟨1274930930234364205247941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1699907906979152273663921 1274930930234364205247941)
                  ·
                    refine ⟨239049549418943288483989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1274930930234364205247941 239049549418943288483989)
                    ·
                      rfl

theorem cell23_1396642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_1396642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396642 prefixEnd_1396642 := by exact prefixLift 1396642
  have htrace : WordTrace (prefixWord ++ tailWord_1396642) baseStart_1396642 baseEnd_1396642 := by
    simpa [prefixWord, tailWord_1396642, baseEnd_1396642] using wordTrace_append hprefix tailTrace_1396642
  have hstable : (prefixWord ++ tailWord_1396642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396642).length < 2 ^ (prefixWord ++ tailWord_1396642).sum := by decide
  have hdescent : baseEnd_1396642 < baseStart_1396642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396671 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 1, 4, 2]
def baseStart_1396671 : Nat := 118140960795 + 1396671 * 2 ^ 59
def prefixEnd_1396671 : Nat := 4983230072969 + 3 ^ 40 * 1396671 * 2
def baseEnd_1396671 : Nat := 717163539195810251989333

theorem tailTrace_1396671 : CollatzResearch.WordTrace tailWord_1396671 prefixEnd_1396671 717163539195810251989333 := by
  unfold tailWord_1396671
  simp only [CollatzResearch.WordTrace]
  refine ⟨50940776323106974261373867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33960517548737982840915911 50940776323106974261373867)
  ·
    refine ⟨76411164484660461392060801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50940776323106974261373867 76411164484660461392060801)
    ·
      refine ⟨57308373363495346044045601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76411164484660461392060801 57308373363495346044045601)
      ·
        refine ⟨42981280022621509533034201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57308373363495346044045601 42981280022621509533034201)
        ·
          refine ⟨32235960016966132149775651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42981280022621509533034201 32235960016966132149775651)
          ·
            refine ⟨48353940025449198224663477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32235960016966132149775651 48353940025449198224663477)
            ·
              refine ⟨4533181877385862333562201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48353940025449198224663477 4533181877385862333562201)
              ·
                refine ⟨3399886408039396750171651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533181877385862333562201 3399886408039396750171651)
                ·
                  refine ⟨5099829612059095125257477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3399886408039396750171651 5099829612059095125257477)
                  ·
                    refine ⟨956218052261080335985777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5099829612059095125257477 956218052261080335985777)
                    ·
                      refine ⟨717163539195810251989333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956218052261080335985777 717163539195810251989333)
                      ·
                        rfl

theorem cell23_1396671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 4, 2].length) (baseStart_1396671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396671 prefixEnd_1396671 := by exact prefixLift 1396671
  have htrace : WordTrace (prefixWord ++ tailWord_1396671) baseStart_1396671 baseEnd_1396671 := by
    simpa [prefixWord, tailWord_1396671, baseEnd_1396671] using wordTrace_append hprefix tailTrace_1396671
  have hstable : (prefixWord ++ tailWord_1396671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396671).length < 2 ^ (prefixWord ++ tailWord_1396671).sum := by decide
  have hdescent : baseEnd_1396671 < baseStart_1396671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396677 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 11]
def baseStart_1396677 : Nat := 118140960795 + 1396677 * 2 ^ 59
def prefixEnd_1396677 : Nat := 4983230072969 + 3 ^ 40 * 1396677 * 2
def baseEnd_1396677 : Nat := 79685180008859692057145

theorem tailTrace_1396677 : CollatzResearch.WordTrace tailWord_1396677 prefixEnd_1396677 79685180008859692057145 := by
  unfold tailWord_1396677
  simp only [CollatzResearch.WordTrace]
  refine ⟨50940995161085237286092285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33960663440723491524061523 50940995161085237286092285)
  ·
    refine ⟨19102873185406963982284607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50940995161085237286092285 19102873185406963982284607)
    ·
      refine ⟨28654309778110445973426911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19102873185406963982284607 28654309778110445973426911)
      ·
        refine ⟨42981464667165668960140367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28654309778110445973426911 42981464667165668960140367)
        ·
          refine ⟨64472197000748503440210551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42981464667165668960140367 64472197000748503440210551)
          ·
            refine ⟨96708295501122755160315827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64472197000748503440210551 96708295501122755160315827)
            ·
              refine ⟨145062443251684132740473741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96708295501122755160315827 145062443251684132740473741)
              ·
                refine ⟨54398416219381549777677653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 145062443251684132740473741 54398416219381549777677653)
                ·
                  refine ⟨79685180008859692057145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 54398416219381549777677653 79685180008859692057145)
                  ·
                    rfl

theorem cell23_1396677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_1396677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396677 prefixEnd_1396677 := by exact prefixLift 1396677
  have htrace : WordTrace (prefixWord ++ tailWord_1396677) baseStart_1396677 baseEnd_1396677 := by
    simpa [prefixWord, tailWord_1396677, baseEnd_1396677] using wordTrace_append hprefix tailTrace_1396677
  have hstable : (prefixWord ++ tailWord_1396677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396677).length < 2 ^ (prefixWord ++ tailWord_1396677).sum := by decide
  have hdescent : baseEnd_1396677 < baseStart_1396677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396688 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 2, 2, 2]
def baseStart_1396688 : Nat := 118140960795 + 1396688 * 2 ^ 59
def prefixEnd_1396688 : Nat := 4983230072969 + 3 ^ 40 * 1396688 * 2
def baseEnd_1396688 : Nat := 717172268366936685476755

theorem tailTrace_1396688 : CollatzResearch.WordTrace tailWord_1396688 prefixEnd_1396688 717172268366936685476755 := by
  unfold tailWord_1396688
  simp only [CollatzResearch.WordTrace]
  refine ⟨25470698182022693082371359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33960930909363590776495145 25470698182022693082371359)
  ·
    refine ⟨38206047273034039623557039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25470698182022693082371359 38206047273034039623557039)
    ·
      refine ⟨57309070909551059435335559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38206047273034039623557039 57309070909551059435335559)
      ·
        refine ⟨85963606364326589153003339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57309070909551059435335559 85963606364326589153003339)
        ·
          refine ⟨128945409546489883729505009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85963606364326589153003339 128945409546489883729505009)
          ·
            refine ⟨96709057159867412797128757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128945409546489883729505009 96709057159867412797128757)
            ·
              refine ⟨9066474108737569949730821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96709057159867412797128757 9066474108737569949730821)
              ·
                refine ⟨1699963895388294365574529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9066474108737569949730821 1699963895388294365574529)
                ·
                  refine ⟨1274972921541220774180897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1699963895388294365574529 1274972921541220774180897)
                  ·
                    refine ⟨956229691155915580635673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1274972921541220774180897 956229691155915580635673)
                    ·
                      refine ⟨717172268366936685476755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956229691155915580635673 717172268366936685476755)
                      ·
                        rfl

theorem cell23_1396688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 2, 2].length) (baseStart_1396688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396688 prefixEnd_1396688 := by exact prefixLift 1396688
  have htrace : WordTrace (prefixWord ++ tailWord_1396688) baseStart_1396688 baseEnd_1396688 := by
    simpa [prefixWord, tailWord_1396688, baseEnd_1396688] using wordTrace_append hprefix tailTrace_1396688
  have hstable : (prefixWord ++ tailWord_1396688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396688).length < 2 ^ (prefixWord ++ tailWord_1396688).sum := by decide
  have hdescent : baseEnd_1396688 < baseStart_1396688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396711 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 7]
def baseStart_1396711 : Nat := 118140960795 + 1396711 * 2 ^ 59
def prefixEnd_1396711 : Nat := 4983230072969 + 3 ^ 40 * 1396711 * 2
def baseEnd_1396711 : Nat := 79687119824665566165461

theorem tailTrace_1396711 : CollatzResearch.WordTrace tailWord_1396711 prefixEnd_1396711 79687119824665566165461 := by
  unfold tailWord_1396711
  simp only [CollatzResearch.WordTrace]
  refine ⟨50942235242962061092829987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33961490161974707395219991 50942235242962061092829987)
  ·
    refine ⟨76413352864443091639244981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50942235242962061092829987 76413352864443091639244981)
    ·
      refine ⟨7163751831041539841179217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76413352864443091639244981 7163751831041539841179217)
      ·
        refine ⟨5372813873281154880884413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7163751831041539841179217 5372813873281154880884413)
        ·
          refine ⟨2014805202480433080331655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5372813873281154880884413 2014805202480433080331655)
          ·
            refine ⟨3022207803720649620497483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014805202480433080331655 3022207803720649620497483)
            ·
              refine ⟨4533311705580974430746225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022207803720649620497483 4533311705580974430746225)
              ·
                refine ⟨3399983779185730823059669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533311705580974430746225 3399983779185730823059669)
                ·
                  refine ⟨79687119824665566165461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3399983779185730823059669 79687119824665566165461)
                  ·
                    rfl

theorem cell23_1396711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 7].length) (baseStart_1396711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396711 prefixEnd_1396711 := by exact prefixLift 1396711
  have htrace : WordTrace (prefixWord ++ tailWord_1396711) baseStart_1396711 baseEnd_1396711 := by
    simpa [prefixWord, tailWord_1396711, baseEnd_1396711] using wordTrace_append hprefix tailTrace_1396711
  have hstable : (prefixWord ++ tailWord_1396711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396711).length < 2 ^ (prefixWord ++ tailWord_1396711).sum := by decide
  have hdescent : baseEnd_1396711 < baseStart_1396711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396756 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1396756 : Nat := 118140960795 + 1396756 * 2 ^ 59
def prefixEnd_1396756 : Nat := 4983230072969 + 3 ^ 40 * 1396756 * 2
def baseEnd_1396756 : Nat := 717207185051442419426443

theorem tailTrace_1396756 : CollatzResearch.WordTrace tailWord_1396756 prefixEnd_1396756 717207185051442419426443 := by
  unfold tailWord_1396756
  simp only [CollatzResearch.WordTrace]
  refine ⟨25471938263899516889109061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33962584351866022518812081 25471938263899516889109061)
  ·
    refine ⟨4775988424481159416707949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25471938263899516889109061 4775988424481159416707949)
    ·
      refine ⟨1790995659180434781265481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4775988424481159416707949 1790995659180434781265481)
      ·
        refine ⟨1343246744385326085949111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1790995659180434781265481 1343246744385326085949111)
        ·
          refine ⟨2014870116577989128923667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343246744385326085949111 2014870116577989128923667)
          ·
            refine ⟨3022305174866983693385501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014870116577989128923667 3022305174866983693385501)
            ·
              refine ⟨1133364440575118885019563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3022305174866983693385501 1133364440575118885019563)
              ·
                refine ⟨1700046660862678327529345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133364440575118885019563 1700046660862678327529345)
                ·
                  refine ⟨1275034995647008745647009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1700046660862678327529345 1275034995647008745647009)
                  ·
                    refine ⟨956276246735256559235257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1275034995647008745647009 956276246735256559235257)
                    ·
                      refine ⟨717207185051442419426443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956276246735256559235257 717207185051442419426443)
                      ·
                        rfl

theorem cell23_1396756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1396756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396756 prefixEnd_1396756 := by exact prefixLift 1396756
  have htrace : WordTrace (prefixWord ++ tailWord_1396756) baseStart_1396756 baseEnd_1396756 := by
    simpa [prefixWord, tailWord_1396756, baseEnd_1396756] using wordTrace_append hprefix tailTrace_1396756
  have hstable : (prefixWord ++ tailWord_1396756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396756).length < 2 ^ (prefixWord ++ tailWord_1396756).sum := by decide
  have hdescent : baseEnd_1396756 < baseStart_1396756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396771 : List Nat := [1, 1, 1, 4, 3, 1, 1, 4, 3, 4]
def baseStart_1396771 : Nat := 118140960795 + 1396771 * 2 ^ 59
def prefixEnd_1396771 : Nat := 4983230072969 + 3 ^ 40 * 1396771 * 2
def baseEnd_1396771 : Nat := 239071629087086620246291

theorem tailTrace_1396771 : CollatzResearch.WordTrace tailWord_1396771 prefixEnd_1396771 239071629087086620246291 := by
  unfold tailWord_1396771
  simp only [CollatzResearch.WordTrace]
  refine ⟨50944423622744691340014167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33962949081829794226676111 50944423622744691340014167)
  ·
    refine ⟨76416635434117037010021251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50944423622744691340014167 76416635434117037010021251)
    ·
      refine ⟨114624953151175555515031877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76416635434117037010021251 114624953151175555515031877)
      ·
        refine ⟨21492178715845416659068477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114624953151175555515031877 21492178715845416659068477)
        ·
          refine ⟨8059567018442031247150679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21492178715845416659068477 8059567018442031247150679)
          ·
            refine ⟨12089350527663046870726019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8059567018442031247150679 12089350527663046870726019)
            ·
              refine ⟨18134025791494570306089029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12089350527663046870726019 18134025791494570306089029)
              ·
                refine ⟨3400129835905231932391693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18134025791494570306089029 3400129835905231932391693)
                ·
                  refine ⟨1275048688464461974646885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3400129835905231932391693 1275048688464461974646885)
                  ·
                    refine ⟨239071629087086620246291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275048688464461974646885 239071629087086620246291)
                    ·
                      rfl

theorem cell23_1396771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 4].length) (baseStart_1396771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396771 prefixEnd_1396771 := by exact prefixLift 1396771
  have htrace : WordTrace (prefixWord ++ tailWord_1396771) baseStart_1396771 baseEnd_1396771 := by
    simpa [prefixWord, tailWord_1396771, baseEnd_1396771] using wordTrace_append hprefix tailTrace_1396771
  have hstable : (prefixWord ++ tailWord_1396771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396771).length < 2 ^ (prefixWord ++ tailWord_1396771).sum := by decide
  have hdescent : baseEnd_1396771 < baseStart_1396771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396784 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 8]
def baseStart_1396784 : Nat := 118140960795 + 1396784 * 2 ^ 59
def prefixEnd_1396784 : Nat := 4983230072969 + 3 ^ 40 * 1396784 * 2
def baseEnd_1396784 : Nat := 79691284723307589986257

theorem tailTrace_1396784 : CollatzResearch.WordTrace tailWord_1396784 prefixEnd_1396784 79691284723307589986257 := by
  unfold tailWord_1396784
  simp only [CollatzResearch.WordTrace]
  refine ⟨25472448885848797280118703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33963265181131729706824937 25472448885848797280118703)
  ·
    refine ⟨38208673328773195920178055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25472448885848797280118703 38208673328773195920178055)
    ·
      refine ⟨57313009993159793880267083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38208673328773195920178055 57313009993159793880267083)
      ·
        refine ⟨85969514989739690820400625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57313009993159793880267083 85969514989739690820400625)
        ·
          refine ⟨64477136242304768115300469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85969514989739690820400625 64477136242304768115300469)
          ·
            refine ⟨6044731522716072010809419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64477136242304768115300469 6044731522716072010809419)
            ·
              refine ⟨9067097284074108016214129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6044731522716072010809419 9067097284074108016214129)
              ·
                refine ⟨6800322963055581012160597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9067097284074108016214129 6800322963055581012160597)
                ·
                  refine ⟨79691284723307589986257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6800322963055581012160597 79691284723307589986257)
                  ·
                    rfl

theorem cell23_1396784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 8].length) (baseStart_1396784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396784 prefixEnd_1396784 := by exact prefixLift 1396784
  have htrace : WordTrace (prefixWord ++ tailWord_1396784) baseStart_1396784 baseEnd_1396784 := by
    simpa [prefixWord, tailWord_1396784, baseEnd_1396784] using wordTrace_append hprefix tailTrace_1396784
  have hstable : (prefixWord ++ tailWord_1396784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396784).length < 2 ^ (prefixWord ++ tailWord_1396784).sum := by decide
  have hdescent : baseEnd_1396784 < baseStart_1396784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396801 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 8]
def baseStart_1396801 : Nat := 118140960795 + 1396801 * 2 ^ 59
def prefixEnd_1396801 : Nat := 4983230072969 + 3 ^ 40 * 1396801 * 2
def baseEnd_1396801 : Nat := 79692254631210527040415

theorem tailTrace_1396801 : CollatzResearch.WordTrace tailWord_1396801 prefixEnd_1396801 79692254631210527040415 := by
  unfold tailWord_1396801
  simp only [CollatzResearch.WordTrace]
  refine ⟨50945517812636006463606257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33963678541757337642404171 50945517812636006463606257)
  ·
    refine ⟨38209138359477004847704693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50945517812636006463606257 38209138359477004847704693)
    ·
      refine ⟨3582106721200969204472315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38209138359477004847704693 3582106721200969204472315)
      ·
        refine ⟨5373160081801453806708473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582106721200969204472315 5373160081801453806708473)
        ·
          refine ⟨4029870061351090355031355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5373160081801453806708473 4029870061351090355031355)
          ·
            refine ⟨6044805092026635532547033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4029870061351090355031355 6044805092026635532547033)
            ·
              refine ⟨4533603819019976649410275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6044805092026635532547033 4533603819019976649410275)
              ·
                refine ⟨6800405728529964974115413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4533603819019976649410275 6800405728529964974115413)
                ·
                  refine ⟨79692254631210527040415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6800405728529964974115413 79692254631210527040415)
                  ·
                    rfl

theorem cell23_1396801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 8].length) (baseStart_1396801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396801 prefixEnd_1396801 := by exact prefixLift 1396801
  have htrace : WordTrace (prefixWord ++ tailWord_1396801) baseStart_1396801 baseEnd_1396801 := by
    simpa [prefixWord, tailWord_1396801, baseEnd_1396801] using wordTrace_append hprefix tailTrace_1396801
  have hstable : (prefixWord ++ tailWord_1396801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396801).length < 2 ^ (prefixWord ++ tailWord_1396801).sum := by decide
  have hdescent : baseEnd_1396801 < baseStart_1396801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396818 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 6]
def baseStart_1396818 : Nat := 118140960795 + 1396818 * 2 ^ 59
def prefixEnd_1396818 : Nat := 4983230072969 + 3 ^ 40 * 1396818 * 2
def baseEnd_1396818 : Nat := 79693224539113464094573

theorem tailTrace_1396818 : CollatzResearch.WordTrace tailWord_1396818 prefixEnd_1396818 79693224539113464094573 := by
  unfold tailWord_1396818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12736534463393604591743777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33964091902382945577983405 12736534463393604591743777)
  ·
    refine ⟨9552400847545203443807833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12736534463393604591743777 9552400847545203443807833)
    ·
      refine ⟨7164300635658902582855875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9552400847545203443807833 7164300635658902582855875)
      ·
        refine ⟨10746450953488353874283813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7164300635658902582855875 10746450953488353874283813)
        ·
          refine ⟨2014959553779066351428215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10746450953488353874283813 2014959553779066351428215)
          ·
            refine ⟨3022439330668599527142323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2014959553779066351428215 3022439330668599527142323)
            ·
              refine ⟨4533658996002899290713485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022439330668599527142323 4533658996002899290713485)
              ·
                refine ⟨1700122123501087234017557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4533658996002899290713485 1700122123501087234017557)
                ·
                  refine ⟨79693224539113464094573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1700122123501087234017557 79693224539113464094573)
                  ·
                    rfl

theorem cell23_1396818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_1396818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396818 prefixEnd_1396818 := by exact prefixLift 1396818
  have htrace : WordTrace (prefixWord ++ tailWord_1396818) baseStart_1396818 baseEnd_1396818 := by
    simpa [prefixWord, tailWord_1396818, baseEnd_1396818] using wordTrace_append hprefix tailTrace_1396818
  have hstable : (prefixWord ++ tailWord_1396818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396818).length < 2 ^ (prefixWord ++ tailWord_1396818).sum := by decide
  have hdescent : baseEnd_1396818 < baseStart_1396818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396831 : List Nat := [1, 1, 2, 3, 1, 1, 2, 6, 1, 5]
def baseStart_1396831 : Nat := 118140960795 + 1396831 * 2 ^ 59
def prefixEnd_1396831 : Nat := 4983230072969 + 3 ^ 40 * 1396831 * 2
def baseEnd_1396831 : Nat := 239081898700176541996199

theorem tailTrace_1396831 : CollatzResearch.WordTrace tailWord_1396831 prefixEnd_1396831 239081898700176541996199 := by
  unfold tailWord_1396831
  simp only [CollatzResearch.WordTrace]
  refine ⟨50946612002527321587198347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33964408001684881058132231 50946612002527321587198347)
  ·
    refine ⟨76419918003790982380797521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50946612002527321587198347 76419918003790982380797521)
    ·
      refine ⟨57314938502843236785598141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76419918003790982380797521 57314938502843236785598141)
      ·
        refine ⟨21493101938566213794599303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57314938502843236785598141 21493101938566213794599303)
        ·
          refine ⟨32239652907849320691898955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21493101938566213794599303 32239652907849320691898955)
          ·
            refine ⟨48359479361773981037848433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32239652907849320691898955 48359479361773981037848433)
            ·
              refine ⟨36269609521330485778386325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48359479361773981037848433 36269609521330485778386325)
              ·
                refine ⟨1700137946312366520861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36269609521330485778386325 1700137946312366520861859)
                ·
                  refine ⟨2550206919468549781292789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700137946312366520861859 2550206919468549781292789)
                  ·
                    refine ⟨239081898700176541996199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2550206919468549781292789 239081898700176541996199)
                    ·
                      rfl

theorem cell23_1396831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_1396831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396831 prefixEnd_1396831 := by exact prefixLift 1396831
  have htrace : WordTrace (prefixWord ++ tailWord_1396831) baseStart_1396831 baseEnd_1396831 := by
    simpa [prefixWord, tailWord_1396831, baseEnd_1396831] using wordTrace_append hprefix tailTrace_1396831
  have hstable : (prefixWord ++ tailWord_1396831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396831).length < 2 ^ (prefixWord ++ tailWord_1396831).sum := by decide
  have hdescent : baseEnd_1396831 < baseStart_1396831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396871 : List Nat := [1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_1396871 : Nat := 118140960795 + 1396871 * 2 ^ 59
def prefixEnd_1396871 : Nat := 4983230072969 + 3 ^ 40 * 1396871 * 2
def baseEnd_1396871 : Nat := 717266235326709469488413

theorem tailTrace_1396871 : CollatzResearch.WordTrace tailWord_1396871 prefixEnd_1396871 717266235326709469488413 := by
  unfold tailWord_1396871
  simp only [CollatzResearch.WordTrace]
  refine ⟨50948070922382408418654467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33965380614921605612436311 50948070922382408418654467)
  ·
    refine ⟨76422106383573612627981701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50948070922382408418654467 76422106383573612627981701)
    ·
      refine ⟨14329144946920052367746569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76422106383573612627981701 14329144946920052367746569)
      ·
        refine ⟨10746858710190039275809927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14329144946920052367746569 10746858710190039275809927)
        ·
          refine ⟨16120288065285058913714891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746858710190039275809927 16120288065285058913714891)
          ·
            refine ⟨24180432097927588370572337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16120288065285058913714891 24180432097927588370572337)
            ·
              refine ⟨18135324073445691277929253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24180432097927588370572337 18135324073445691277929253)
              ·
                refine ⟨3400373263771067114611735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18135324073445691277929253 3400373263771067114611735)
                ·
                  refine ⟨5100559895656600671917603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3400373263771067114611735 5100559895656600671917603)
                  ·
                    refine ⟨7650839843484901007876405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5100559895656600671917603 7650839843484901007876405)
                    ·
                      refine ⟨717266235326709469488413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7650839843484901007876405 717266235326709469488413)
                      ·
                        rfl

theorem cell23_1396871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_1396871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396871 prefixEnd_1396871 := by exact prefixLift 1396871
  have htrace : WordTrace (prefixWord ++ tailWord_1396871) baseStart_1396871 baseEnd_1396871 := by
    simpa [prefixWord, tailWord_1396871, baseEnd_1396871] using wordTrace_append hprefix tailTrace_1396871
  have hstable : (prefixWord ++ tailWord_1396871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396871).length < 2 ^ (prefixWord ++ tailWord_1396871).sum := by decide
  have hdescent : baseEnd_1396871 < baseStart_1396871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396885 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_1396885 : Nat := 118140960795 + 1396885 * 2 ^ 59
def prefixEnd_1396885 : Nat := 4983230072969 + 3 ^ 40 * 1396885 * 2
def baseEnd_1396885 : Nat := 717273424055872414713349

theorem tailTrace_1396885 : CollatzResearch.WordTrace tailWord_1396885 prefixEnd_1396885 717273424055872414713349 := by
  unfold tailWord_1396885
  simp only [CollatzResearch.WordTrace]
  refine ⟨50948581544331688809664109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33965721029554459206442739 50948581544331688809664109)
  ·
    refine ⟨19105718079124383303624041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50948581544331688809664109 19105718079124383303624041)
    ·
      refine ⟨14329288559343287477718031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19105718079124383303624041 14329288559343287477718031)
      ·
        refine ⟨21493932839014931216577047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14329288559343287477718031 21493932839014931216577047)
        ·
          refine ⟨32240899258522396824865571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21493932839014931216577047 32240899258522396824865571)
          ·
            refine ⟨48361348887783595237298357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32240899258522396824865571 48361348887783595237298357)
            ·
              refine ⟨4533876458229712053496721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48361348887783595237298357 4533876458229712053496721)
              ·
                refine ⟨3400407343672284040122541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4533876458229712053496721 3400407343672284040122541)
                ·
                  refine ⟨1275152753877106515045953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3400407343672284040122541 1275152753877106515045953)
                  ·
                    refine ⟨956364565407829886284465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1275152753877106515045953 956364565407829886284465)
                    ·
                      refine ⟨717273424055872414713349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956364565407829886284465 717273424055872414713349)
                      ·
                        rfl

theorem cell23_1396885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_1396885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396885 prefixEnd_1396885 := by exact prefixLift 1396885
  have htrace : WordTrace (prefixWord ++ tailWord_1396885) baseStart_1396885 baseEnd_1396885 := by
    simpa [prefixWord, tailWord_1396885, baseEnd_1396885] using wordTrace_append hprefix tailTrace_1396885
  have hstable : (prefixWord ++ tailWord_1396885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396885).length < 2 ^ (prefixWord ++ tailWord_1396885).sum := by decide
  have hdescent : baseEnd_1396885 < baseStart_1396885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396929 : List Nat := [1, 2, 6, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1396929 : Nat := 118140960795 + 1396929 * 2 ^ 59
def prefixEnd_1396929 : Nat := 4983230072969 + 3 ^ 40 * 1396929 * 2
def baseEnd_1396929 : Nat := 239098672401556747521049

theorem tailTrace_1396929 : CollatzResearch.WordTrace tailWord_1396929 prefixEnd_1396929 239098672401556747521049 := by
  unfold tailWord_1396929
  simp only [CollatzResearch.WordTrace]
  refine ⟨50950186356172284324265841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33966790904114856216177227 50950186356172284324265841)
  ·
    refine ⟨38212639767129213243199381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50950186356172284324265841 38212639767129213243199381)
    ·
      refine ⟨1791217489084181870774971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 38212639767129213243199381 1791217489084181870774971)
      ·
        refine ⟨2686826233626272806162457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791217489084181870774971 2686826233626272806162457)
        ·
          refine ⟨2015119675219704604621843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2686826233626272806162457 2015119675219704604621843)
          ·
            refine ⟨3022679512829556906932765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015119675219704604621843 3022679512829556906932765)
            ·
              refine ⟨1133504817311083840099787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3022679512829556906932765 1133504817311083840099787)
              ·
                refine ⟨1700257225966625760149681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133504817311083840099787 1700257225966625760149681)
                ·
                  refine ⟨1275192919474969320112261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1700257225966625760149681 1275192919474969320112261)
                  ·
                    refine ⟨239098672401556747521049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275192919474969320112261 239098672401556747521049)
                    ·
                      rfl

theorem cell23_1396929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1396929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396929 prefixEnd_1396929 := by exact prefixLift 1396929
  have htrace : WordTrace (prefixWord ++ tailWord_1396929) baseStart_1396929 baseEnd_1396929 := by
    simpa [prefixWord, tailWord_1396929, baseEnd_1396929] using wordTrace_append hprefix tailTrace_1396929
  have hstable : (prefixWord ++ tailWord_1396929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396929).length < 2 ^ (prefixWord ++ tailWord_1396929).sum := by decide
  have hdescent : baseEnd_1396929 < baseStart_1396929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396945 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 1, 3, 2]
def baseStart_1396945 : Nat := 118140960795 + 1396945 * 2 ^ 59
def prefixEnd_1396945 : Nat := 4983230072969 + 3 ^ 40 * 1396945 * 2
def baseEnd_1396945 : Nat := 717304232895142179963073

theorem tailTrace_1396945 : CollatzResearch.WordTrace tailWord_1396945 prefixEnd_1396945 717304232895142179963073 := by
  unfold tailWord_1396945
  simp only [CollatzResearch.WordTrace]
  refine ⟨50950769924114319056848289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33967179949409546037898859 50950769924114319056848289)
  ·
    refine ⟨38213077443085739292636217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50950769924114319056848289 38213077443085739292636217)
    ·
      refine ⟨28659808082314304469477163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38213077443085739292636217 28659808082314304469477163)
      ·
        refine ⟨42989712123471456704215745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28659808082314304469477163 42989712123471456704215745)
        ·
          refine ⟨32242284092603592528161809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42989712123471456704215745 32242284092603592528161809)
          ·
            refine ⟨24181713069452694396121357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32242284092603592528161809 24181713069452694396121357)
            ·
              refine ⟨9068142401044760398545509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24181713069452694396121357 9068142401044760398545509)
              ·
                refine ⟨1700276700195892574727283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9068142401044760398545509 1700276700195892574727283)
                ·
                  refine ⟨2550415050293838862090925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700276700195892574727283 2550415050293838862090925)
                  ·
                    refine ⟨956405643860189573284097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2550415050293838862090925 956405643860189573284097)
                    ·
                      refine ⟨717304232895142179963073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956405643860189573284097 717304232895142179963073)
                      ·
                        rfl

theorem cell23_1396945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_1396945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396945 prefixEnd_1396945 := by exact prefixLift 1396945
  have htrace : WordTrace (prefixWord ++ tailWord_1396945) baseStart_1396945 baseEnd_1396945 := by
    simpa [prefixWord, tailWord_1396945, baseEnd_1396945] using wordTrace_append hprefix tailTrace_1396945
  have hstable : (prefixWord ++ tailWord_1396945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396945).length < 2 ^ (prefixWord ++ tailWord_1396945).sum := by decide
  have hdescent : baseEnd_1396945 < baseStart_1396945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1396996 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_1396996 : Nat := 118140960795 + 1396996 * 2 ^ 59
def prefixEnd_1396996 : Nat := 4983230072969 + 3 ^ 40 * 1396996 * 2
def baseEnd_1396996 : Nat := 717330420408521480425339

theorem tailTrace_1396996 : CollatzResearch.WordTrace tailWord_1396996 prefixEnd_1396996 717330420408521480425339 := by
  unfold tailWord_1396996
  simp only [CollatzResearch.WordTrace]
  refine ⟨25476315023464777383477421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33968420031286369844636561 25476315023464777383477421)
  ·
    refine ⟨9553618133799291518804033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25476315023464777383477421 9553618133799291518804033)
    ·
      refine ⟨7165213600349468639103025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9553618133799291518804033 7165213600349468639103025)
      ·
        refine ⟨5373910200262101479327269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7165213600349468639103025 5373910200262101479327269)
        ·
          refine ⟨1007608162549144027373863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5373910200262101479327269 1007608162549144027373863)
          ·
            refine ⟨1511412243823716041060795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007608162549144027373863 1511412243823716041060795)
            ·
              refine ⟨2267118365735574061591193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511412243823716041060795 2267118365735574061591193)
              ·
                refine ⟨1700338774301680546193395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267118365735574061591193 1700338774301680546193395)
                ·
                  refine ⟨2550508161452520819290093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1700338774301680546193395 2550508161452520819290093)
                  ·
                    refine ⟨956440560544695307233785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2550508161452520819290093 956440560544695307233785)
                    ·
                      refine ⟨717330420408521480425339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956440560544695307233785 717330420408521480425339)
                      ·
                        rfl

theorem cell23_1396996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_1396996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1396996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1396996 prefixEnd_1396996 := by exact prefixLift 1396996
  have htrace : WordTrace (prefixWord ++ tailWord_1396996) baseStart_1396996 baseEnd_1396996 := by
    simpa [prefixWord, tailWord_1396996, baseEnd_1396996] using wordTrace_append hprefix tailTrace_1396996
  have hstable : (prefixWord ++ tailWord_1396996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1396996).length < 2 ^ (prefixWord ++ tailWord_1396996).sum := by decide
  have hdescent : baseEnd_1396996 < baseStart_1396996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1396996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397011 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 1, 7]
def baseStart_1397011 : Nat := 118140960795 + 1397011 * 2 ^ 59
def prefixEnd_1397011 : Nat := 4983230072969 + 3 ^ 40 * 1397011 * 2
def baseEnd_1397011 : Nat := 239112707539446307245923

theorem tailTrace_1397011 : CollatzResearch.WordTrace tailWord_1397011 prefixEnd_1397011 239112707539446307245923 := by
  unfold tailWord_1397011
  simp only [CollatzResearch.WordTrace]
  refine ⟨50953177141875212328750887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33968784761250141552500591 50953177141875212328750887)
  ·
    refine ⟨76429765712812818493126331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50953177141875212328750887 76429765712812818493126331)
    ·
      refine ⟨114644648569219227739689497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76429765712812818493126331 114644648569219227739689497)
      ·
        refine ⟨85983486426914420804767123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114644648569219227739689497 85983486426914420804767123)
        ·
          refine ⟨128975229640371631207150685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85983486426914420804767123 128975229640371631207150685)
          ·
            refine ⟨48365711115139361702681507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128975229640371631207150685 48365711115139361702681507)
            ·
              refine ⟨72548566672709042554022261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48365711115139361702681507 72548566672709042554022261)
              ·
                refine ⟨6801428125566472739439587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72548566672709042554022261 6801428125566472739439587)
                ·
                  refine ⟨10202142188349709109159381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6801428125566472739439587 10202142188349709109159381)
                  ·
                    refine ⟨239112707539446307245923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10202142188349709109159381 239112707539446307245923)
                    ·
                      rfl

theorem cell23_1397011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 7].length) (baseStart_1397011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397011 prefixEnd_1397011 := by exact prefixLift 1397011
  have htrace : WordTrace (prefixWord ++ tailWord_1397011) baseStart_1397011 baseEnd_1397011 := by
    simpa [prefixWord, tailWord_1397011, baseEnd_1397011] using wordTrace_append hprefix tailTrace_1397011
  have hstable : (prefixWord ++ tailWord_1397011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397011).length < 2 ^ (prefixWord ++ tailWord_1397011).sum := by decide
  have hdescent : baseEnd_1397011 < baseStart_1397011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397032 : List Nat := [2, 1, 5, 1, 3, 1, 1, 4, 5]
def baseStart_1397032 : Nat := 118140960795 + 1397032 * 2 ^ 59
def prefixEnd_1397032 : Nat := 4983230072969 + 3 ^ 40 * 1397032 * 2
def baseEnd_1397032 : Nat := 79705433968009259952797

theorem tailTrace_1397032 : CollatzResearch.WordTrace tailWord_1397032 prefixEnd_1397032 79705433968009259952797 := by
  unfold tailWord_1397032
  simp only [CollatzResearch.WordTrace]
  refine ⟨25476971537399566457632675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33969295383199421943510233 25476971537399566457632675)
  ·
    refine ⟨38215457306099349686449013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25476971537399566457632675 38215457306099349686449013)
    ·
      refine ⟨3582699122446814033104595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38215457306099349686449013 3582699122446814033104595)
      ·
        refine ⟨5374048683670221049656893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582699122446814033104595 5374048683670221049656893)
        ·
          refine ⟨2015268256376332893621335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5374048683670221049656893 2015268256376332893621335)
          ·
            refine ⟨3022902384564499340432003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015268256376332893621335 3022902384564499340432003)
            ·
              refine ⟨4534353576846749010648005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3022902384564499340432003 4534353576846749010648005)
              ·
                refine ⟨850191295658765439496501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4534353576846749010648005 850191295658765439496501)
                ·
                  refine ⟨79705433968009259952797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 850191295658765439496501 79705433968009259952797)
                  ·
                    rfl

theorem cell23_1397032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 5].length) (baseStart_1397032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397032 prefixEnd_1397032 := by exact prefixLift 1397032
  have htrace : WordTrace (prefixWord ++ tailWord_1397032) baseStart_1397032 baseEnd_1397032 := by
    simpa [prefixWord, tailWord_1397032, baseEnd_1397032] using wordTrace_append hprefix tailTrace_1397032
  have hstable : (prefixWord ++ tailWord_1397032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397032).length < 2 ^ (prefixWord ++ tailWord_1397032).sum := by decide
  have hdescent : baseEnd_1397032 < baseStart_1397032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397048 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_1397048 : Nat := 118140960795 + 1397048 * 2 ^ 59
def prefixEnd_1397048 : Nat := 4983230072969 + 3 ^ 40 * 1397048 * 2
def baseEnd_1397048 : Nat := 717357121402555276975099

theorem tailTrace_1397048 : CollatzResearch.WordTrace tailWord_1397048 prefixEnd_1397048 717357121402555276975099 := by
  unfold tailWord_1397048
  simp only [CollatzResearch.WordTrace]
  refine ⟨25477263321370583823923899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33969684428494111765231865 25477263321370583823923899)
  ·
    refine ⟨38215894982055875735885849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25477263321370583823923899 38215894982055875735885849)
    ·
      refine ⟨28661921236541906801914387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38215894982055875735885849 28661921236541906801914387)
      ·
        refine ⟨42992881854812860202871581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28661921236541906801914387 42992881854812860202871581)
        ·
          refine ⟨16122330695554822576076843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42992881854812860202871581 16122330695554822576076843)
          ·
            refine ⟨24183496043332233864115265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16122330695554822576076843 24183496043332233864115265)
            ·
              refine ⟨18137622032499175398086449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24183496043332233864115265 18137622032499175398086449)
              ·
                refine ⟨13603216524374381548564837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18137622032499175398086449 13603216524374381548564837)
                ·
                  refine ⟨2550603098320196540355907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13603216524374381548564837 2550603098320196540355907)
                  ·
                    refine ⟨3825904647480294810533861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2550603098320196540355907 3825904647480294810533861)
                    ·
                      refine ⟨717357121402555276975099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3825904647480294810533861 717357121402555276975099)
                      ·
                        rfl

theorem cell23_1397048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_1397048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397048 prefixEnd_1397048 := by exact prefixLift 1397048
  have htrace : WordTrace (prefixWord ++ tailWord_1397048) baseStart_1397048 baseEnd_1397048 := by
    simpa [prefixWord, tailWord_1397048, baseEnd_1397048] using wordTrace_append hprefix tailTrace_1397048
  have hstable : (prefixWord ++ tailWord_1397048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397048).length < 2 ^ (prefixWord ++ tailWord_1397048).sum := by decide
  have hdescent : baseEnd_1397048 < baseStart_1397048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397092 : List Nat := [2, 3, 1, 1, 3, 1, 1, 6, 1, 4]
def baseStart_1397092 : Nat := 118140960795 + 1397092 * 2 ^ 59
def prefixEnd_1397092 : Nat := 4983230072969 + 3 ^ 40 * 1397092 * 2
def baseEnd_1397092 : Nat := 239126571517117701608299

theorem tailTrace_1397092 : CollatzResearch.WordTrace tailWord_1397092 prefixEnd_1397092 239126571517117701608299 := by
  unfold tailWord_1397092
  simp only [CollatzResearch.WordTrace]
  refine ⟨25478065727290881581224765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33970754303054508774966353 25478065727290881581224765)
  ·
    refine ⟨9554274647734080592959287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25478065727290881581224765 9554274647734080592959287)
    ·
      refine ⟨14331411971601120889438931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9554274647734080592959287 14331411971601120889438931)
      ·
        refine ⟨21497117957401681334158397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14331411971601120889438931 21497117957401681334158397)
        ·
          refine ⟨8061419234025630500309399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21497117957401681334158397 8061419234025630500309399)
          ·
            refine ⟨12092128851038445750464099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8061419234025630500309399 12092128851038445750464099)
            ·
              refine ⟨18138193276557668625696149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12092128851038445750464099 18138193276557668625696149)
              ·
                refine ⟨850227809838640716829507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18138193276557668625696149 850227809838640716829507)
                ·
                  refine ⟨1275341714757961075244261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850227809838640716829507 1275341714757961075244261)
                  ·
                    refine ⟨239126571517117701608299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275341714757961075244261 239126571517117701608299)
                    ·
                      rfl

theorem cell23_1397092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_1397092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397092 prefixEnd_1397092 := by exact prefixLift 1397092
  have htrace : WordTrace (prefixWord ++ tailWord_1397092) baseStart_1397092 baseEnd_1397092 := by
    simpa [prefixWord, tailWord_1397092, baseEnd_1397092] using wordTrace_append hprefix tailTrace_1397092
  have hstable : (prefixWord ++ tailWord_1397092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397092).length < 2 ^ (prefixWord ++ tailWord_1397092).sum := by decide
  have hdescent : baseEnd_1397092 < baseStart_1397092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397192 : List Nat := [2, 1, 3, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_1397192 : Nat := 118140960795 + 1397192 * 2 ^ 59
def prefixEnd_1397192 : Nat := 4983230072969 + 3 ^ 40 * 1397192 * 2
def baseEnd_1397192 : Nat := 717431062616802713574437

theorem tailTrace_1397192 : CollatzResearch.WordTrace tailWord_1397192 prefixEnd_1397192 717431062616802713574437 := by
  unfold tailWord_1397192
  simp only [CollatzResearch.WordTrace]
  refine ⟨25479889377109740120544915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33973185836146320160726553 25479889377109740120544915)
  ·
    refine ⟨38219834065664610180817373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25479889377109740120544915 38219834065664610180817373)
    ·
      refine ⟨14332437774624228817806515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38219834065664610180817373 14332437774624228817806515)
      ·
        refine ⟨21498656661936343226709773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14332437774624228817806515 21498656661936343226709773)
        ·
          refine ⟨8061996248226128710016165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21498656661936343226709773 8061996248226128710016165)
          ·
            refine ⟨1511624296542399133128031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8061996248226128710016165 1511624296542399133128031)
            ·
              refine ⟨2267436444813598699692047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511624296542399133128031 2267436444813598699692047)
              ·
                refine ⟨3401154667220398049538071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267436444813598699692047 3401154667220398049538071)
                ·
                  refine ⟨5101732000830597074307107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3401154667220398049538071 5101732000830597074307107)
                  ·
                    refine ⟨7652598001245895611460661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5101732000830597074307107 7652598001245895611460661)
                    ·
                      refine ⟨717431062616802713574437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7652598001245895611460661 717431062616802713574437)
                      ·
                        rfl

theorem cell23_1397192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_1397192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397192 prefixEnd_1397192 := by exact prefixLift 1397192
  have htrace : WordTrace (prefixWord ++ tailWord_1397192) baseStart_1397192 baseEnd_1397192 := by
    simpa [prefixWord, tailWord_1397192, baseEnd_1397192] using wordTrace_append hprefix tailTrace_1397192
  have hstable : (prefixWord ++ tailWord_1397192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397192).length < 2 ^ (prefixWord ++ tailWord_1397192).sum := by decide
  have hdescent : baseEnd_1397192 < baseStart_1397192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397206 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_1397206 : Nat := 118140960795 + 1397206 * 2 ^ 59
def prefixEnd_1397206 : Nat := 4983230072969 + 3 ^ 40 * 1397206 * 2
def baseEnd_1397206 : Nat := 717438251345965658799373

theorem tailTrace_1397206 : CollatzResearch.WordTrace tailWord_1397206 prefixEnd_1397206 717438251345965658799373 := by
  unfold tailWord_1397206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3185018086010547539506217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33973526250779173754732981 3185018086010547539506217)
  ·
    refine ⟨2388763564507910654629663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3185018086010547539506217 2388763564507910654629663)
    ·
      refine ⟨3583145346761865981944495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388763564507910654629663 3583145346761865981944495)
      ·
        refine ⟨5374718020142798972916743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583145346761865981944495 5374718020142798972916743)
        ·
          refine ⟨8062077030214198459375115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374718020142798972916743 8062077030214198459375115)
          ·
            refine ⟨12093115545321297689062673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062077030214198459375115 12093115545321297689062673)
            ·
              refine ⟨9069836658990973266797005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12093115545321297689062673 9069836658990973266797005)
              ·
                refine ⟨3401188747121614975048877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9069836658990973266797005 3401188747121614975048877)
                ·
                  refine ⟨1275445780170605615643329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3401188747121614975048877 1275445780170605615643329)
                  ·
                    refine ⟨956584335127954211732497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1275445780170605615643329 956584335127954211732497)
                    ·
                      refine ⟨717438251345965658799373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956584335127954211732497 717438251345965658799373)
                      ·
                        rfl

theorem cell23_1397206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_1397206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397206 prefixEnd_1397206 := by exact prefixLift 1397206
  have htrace : WordTrace (prefixWord ++ tailWord_1397206) baseStart_1397206 baseEnd_1397206 := by
    simpa [prefixWord, tailWord_1397206, baseEnd_1397206] using wordTrace_append hprefix tailTrace_1397206
  have hstable : (prefixWord ++ tailWord_1397206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397206).length < 2 ^ (prefixWord ++ tailWord_1397206).sum := by decide
  have hdescent : baseEnd_1397206 < baseStart_1397206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397232 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 3, 3, 2]
def baseStart_1397232 : Nat := 118140960795 + 1397232 * 2 ^ 59
def prefixEnd_1397232 : Nat := 4983230072969 + 3 ^ 40 * 1397232 * 2
def baseEnd_1397232 : Nat := 717451601842982557074253

theorem tailTrace_1397232 : CollatzResearch.WordTrace tailWord_1397232 prefixEnd_1397232 717451601842982557074253 := by
  unfold tailWord_1397232
  simp only [CollatzResearch.WordTrace]
  refine ⟨25480618837037283536272975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33974158449383044715030633 25480618837037283536272975)
  ·
    refine ⟨38220928255555925304409463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25480618837037283536272975 38220928255555925304409463)
    ·
      refine ⟨57331392383333887956614195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38220928255555925304409463 57331392383333887956614195)
      ·
        refine ⟨85997088575000831934921293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57331392383333887956614195 85997088575000831934921293)
        ·
          refine ⟨32248908215625311975595485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85997088575000831934921293 32248908215625311975595485)
          ·
            refine ⟨12093340580859491990848307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32248908215625311975595485 12093340580859491990848307)
            ·
              refine ⟨18140010871289237986272461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12093340580859491990848307 18140010871289237986272461)
              ·
                refine ⟨6802504076733464244852173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18140010871289237986272461 6802504076733464244852173)
                ·
                  refine ⟨2550939028775049091819565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6802504076733464244852173 2550939028775049091819565)
                  ·
                    refine ⟨956602135790643409432337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2550939028775049091819565 956602135790643409432337)
                    ·
                      refine ⟨717451601842982557074253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956602135790643409432337 717451601842982557074253)
                      ·
                        rfl

theorem cell23_1397232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 3, 2].length) (baseStart_1397232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397232 prefixEnd_1397232 := by exact prefixLift 1397232
  have htrace : WordTrace (prefixWord ++ tailWord_1397232) baseStart_1397232 baseEnd_1397232 := by
    simpa [prefixWord, tailWord_1397232, baseEnd_1397232] using wordTrace_append hprefix tailTrace_1397232
  have hstable : (prefixWord ++ tailWord_1397232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397232).length < 2 ^ (prefixWord ++ tailWord_1397232).sum := by decide
  have hdescent : baseEnd_1397232 < baseStart_1397232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397265 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_1397265 : Nat := 118140960795 + 1397265 * 2 ^ 59
def prefixEnd_1397265 : Nat := 4983230072969 + 3 ^ 40 * 1397265 * 2
def baseEnd_1397265 : Nat := 717468546704580927961601

theorem tailTrace_1397265 : CollatzResearch.WordTrace tailWord_1397265 prefixEnd_1397265 717468546704580927961601 := by
  unfold tailWord_1397265
  simp only [CollatzResearch.WordTrace]
  refine ⟨50962441282955013708497249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33974960855303342472331499 50962441282955013708497249)
  ·
    refine ⟨38221830962216260281372937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50962441282955013708497249 38221830962216260281372937)
    ·
      refine ⟨28666373221662195211029703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38221830962216260281372937 28666373221662195211029703)
      ·
        refine ⟨42999559832493292816544555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28666373221662195211029703 42999559832493292816544555)
        ·
          refine ⟨64499339748739939224816833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42999559832493292816544555 64499339748739939224816833)
          ·
            refine ⟨48374504811554954418612625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64499339748739939224816833 48374504811554954418612625)
            ·
              refine ⟨36280878608666215813959469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48374504811554954418612625 36280878608666215813959469)
              ·
                refine ⟨13605329478249830930234801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36280878608666215813959469 13605329478249830930234801)
                ·
                  refine ⟨10203997108687373197676101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13605329478249830930234801 10203997108687373197676101)
                  ·
                    refine ⟨1913249457878882474564269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10203997108687373197676101 1913249457878882474564269)
                    ·
                      refine ⟨717468546704580927961601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1913249457878882474564269 717468546704580927961601)
                      ·
                        rfl

theorem cell23_1397265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_1397265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397265 prefixEnd_1397265 := by exact prefixLift 1397265
  have htrace : WordTrace (prefixWord ++ tailWord_1397265) baseStart_1397265 baseEnd_1397265 := by
    simpa [prefixWord, tailWord_1397265, baseEnd_1397265] using wordTrace_append hprefix tailTrace_1397265
  have hstable : (prefixWord ++ tailWord_1397265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397265).length < 2 ^ (prefixWord ++ tailWord_1397265).sum := by decide
  have hdescent : baseEnd_1397265 < baseStart_1397265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397285 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 7]
def baseStart_1397285 : Nat := 118140960795 + 1397285 * 2 ^ 59
def prefixEnd_1397285 : Nat := 4983230072969 + 3 ^ 40 * 1397285 * 2
def baseEnd_1397285 : Nat := 79719868479741205523501

theorem tailTrace_1397285 : CollatzResearch.WordTrace tailWord_1397285 prefixEnd_1397285 79719868479741205523501 := by
  unfold tailWord_1397285
  simp only [CollatzResearch.WordTrace]
  refine ⟨50963170742882557124225309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33975447161921704749483539 50963170742882557124225309)
  ·
    refine ⟨19111189028580958921584491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50963170742882557124225309 19111189028580958921584491)
    ·
      refine ⟨28666783542871438382376737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19111189028580958921584491 28666783542871438382376737)
      ·
        refine ⟨21500087657153578786782553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28666783542871438382376737 21500087657153578786782553)
        ·
          refine ⟨16125065742865184090086915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21500087657153578786782553 16125065742865184090086915)
          ·
            refine ⟨24187598614297776135130373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16125065742865184090086915 24187598614297776135130373)
            ·
              refine ⟨4535174740180833025336945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24187598614297776135130373 4535174740180833025336945)
              ·
                refine ⟨3401381055135624769002709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4535174740180833025336945 3401381055135624769002709)
                ·
                  refine ⟨79719868479741205523501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3401381055135624769002709 79719868479741205523501)
                  ·
                    rfl

theorem cell23_1397285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_1397285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397285 prefixEnd_1397285 := by exact prefixLift 1397285
  have htrace : WordTrace (prefixWord ++ tailWord_1397285) baseStart_1397285 baseEnd_1397285 := by
    simpa [prefixWord, tailWord_1397285, baseEnd_1397285] using wordTrace_append hprefix tailTrace_1397285
  have hstable : (prefixWord ++ tailWord_1397285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397285).length < 2 ^ (prefixWord ++ tailWord_1397285).sum := by decide
  have hdescent : baseEnd_1397285 < baseStart_1397285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397349 : List Nat := [1, 3, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_1397349 : Nat := 118140960795 + 1397349 * 2 ^ 59
def prefixEnd_1397349 : Nat := 4983230072969 + 3 ^ 40 * 1397349 * 2
def baseEnd_1397349 : Nat := 239170559693186199770405

theorem tailTrace_1397349 : CollatzResearch.WordTrace tailWord_1397349 prefixEnd_1397349 239170559693186199770405 := by
  unfold tailWord_1397349
  simp only [CollatzResearch.WordTrace]
  refine ⟨50965505014650696054555101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33977003343100464036370067 50965505014650696054555101)
  ·
    refine ⟨19112064380494011020458163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50965505014650696054555101 19112064380494011020458163)
    ·
      refine ⟨28668096570741016530687245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19112064380494011020458163 28668096570741016530687245)
      ·
        refine ⟨10750536214027881199007717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28668096570741016530687245 10750536214027881199007717)
        ·
          refine ⟨2015725540130227724813947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10750536214027881199007717 2015725540130227724813947)
          ·
            refine ⟨3023588310195341587220921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015725540130227724813947 3023588310195341587220921)
            ·
              refine ⟨2267691232646506190415691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3023588310195341587220921 2267691232646506190415691)
              ·
                refine ⟨3401536848969759285623537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267691232646506190415691 3401536848969759285623537)
                ·
                  refine ⟨2551152636727319464217653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3401536848969759285623537 2551152636727319464217653)
                  ·
                    refine ⟨239170559693186199770405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2551152636727319464217653 239170559693186199770405)
                    ·
                      rfl

theorem cell23_1397349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_1397349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397349 prefixEnd_1397349 := by exact prefixLift 1397349
  have htrace : WordTrace (prefixWord ++ tailWord_1397349) baseStart_1397349 baseEnd_1397349 := by
    simpa [prefixWord, tailWord_1397349, baseEnd_1397349] using wordTrace_append hprefix tailTrace_1397349
  have hstable : (prefixWord ++ tailWord_1397349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397349).length < 2 ^ (prefixWord ++ tailWord_1397349).sum := by decide
  have hdescent : baseEnd_1397349 < baseStart_1397349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397386 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_1397386 : Nat := 118140960795 + 1397386 * 2 ^ 59
def prefixEnd_1397386 : Nat := 4983230072969 + 3 ^ 40 * 1397386 * 2
def baseEnd_1397386 : Nat := 717530677863774954548545

theorem tailTrace_1397386 : CollatzResearch.WordTrace tailWord_1397386 prefixEnd_1397386 717530677863774954548545 := by
  unfold tailWord_1397386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12741713628879162843413003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33977903010344434249101341 12741713628879162843413003)
  ·
    refine ⟨19112570443318744265119505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12741713628879162843413003 19112570443318744265119505)
    ·
      refine ⟨14334427832489058198839629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19112570443318744265119505 14334427832489058198839629)
      ·
        refine ⟨5375410437183396824564861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14334427832489058198839629 5375410437183396824564861)
        ·
          refine ⟨2015778913943773809211823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5375410437183396824564861 2015778913943773809211823)
          ·
            refine ⟨3023668370915660713817735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2015778913943773809211823 3023668370915660713817735)
            ·
              refine ⟨4535502556373491070726603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023668370915660713817735 4535502556373491070726603)
              ·
                refine ⟨6803253834560236606089905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4535502556373491070726603 6803253834560236606089905)
                ·
                  refine ⟨5102440375920177454567429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6803253834560236606089905 5102440375920177454567429)
                  ·
                    refine ⟨956707570485033272731393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5102440375920177454567429 956707570485033272731393)
                    ·
                      refine ⟨717530677863774954548545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956707570485033272731393 717530677863774954548545)
                      ·
                        rfl

theorem cell23_1397386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_1397386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397386 prefixEnd_1397386 := by exact prefixLift 1397386
  have htrace : WordTrace (prefixWord ++ tailWord_1397386) baseStart_1397386 baseEnd_1397386 := by
    simpa [prefixWord, tailWord_1397386, baseEnd_1397386] using wordTrace_append hprefix tailTrace_1397386
  have hstable : (prefixWord ++ tailWord_1397386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397386).length < 2 ^ (prefixWord ++ tailWord_1397386).sum := by decide
  have hdescent : baseEnd_1397386 < baseStart_1397386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397395 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6]
def baseStart_1397395 : Nat := 118140960795 + 1397395 * 2 ^ 59
def prefixEnd_1397395 : Nat := 4983230072969 + 3 ^ 40 * 1397395 * 2
def baseEnd_1397395 : Nat := 717535299189665419336003

theorem tailTrace_1397395 : CollatzResearch.WordTrace tailWord_1397395 prefixEnd_1397395 717535299189665419336003 := by
  unfold tailWord_1397395
  simp only [CollatzResearch.WordTrace]
  refine ⟨50967182772484045910729639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33978121848322697273819759 50967182772484045910729639)
  ·
    refine ⟨76450774158726068866094459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50967182772484045910729639 76450774158726068866094459)
    ·
      refine ⟨114676161238089103299141689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76450774158726068866094459 114676161238089103299141689)
      ·
        refine ⟨86007120928566827474356267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114676161238089103299141689 86007120928566827474356267)
        ·
          refine ⟨129010681392850241211534401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86007120928566827474356267 129010681392850241211534401)
          ·
            refine ⟨96758011044637680908650801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129010681392850241211534401 96758011044637680908650801)
            ·
              refine ⟨72568508283478260681488101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96758011044637680908650801 72568508283478260681488101)
              ·
                refine ⟨13606595303152173877779019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72568508283478260681488101 13606595303152173877779019)
                ·
                  refine ⟨20409892954728260816668529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13606595303152173877779019 20409892954728260816668529)
                  ·
                    refine ⟨15307419716046195612501397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20409892954728260816668529 15307419716046195612501397)
                    ·
                      refine ⟨717535299189665419336003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15307419716046195612501397 717535299189665419336003)
                      ·
                        rfl

theorem cell23_1397395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_1397395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397395 prefixEnd_1397395 := by exact prefixLift 1397395
  have htrace : WordTrace (prefixWord ++ tailWord_1397395) baseStart_1397395 baseEnd_1397395 := by
    simpa [prefixWord, tailWord_1397395, baseEnd_1397395] using wordTrace_append hprefix tailTrace_1397395
  have hstable : (prefixWord ++ tailWord_1397395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397395).length < 2 ^ (prefixWord ++ tailWord_1397395).sum := by decide
  have hdescent : baseEnd_1397395 < baseStart_1397395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397396 : List Nat := [2, 4, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1397396 : Nat := 118140960795 + 1397396 * 2 ^ 59
def prefixEnd_1397396 : Nat := 4983230072969 + 3 ^ 40 * 1397396 * 2
def baseEnd_1397396 : Nat := 239178604223439971807833

theorem tailTrace_1397396 : CollatzResearch.WordTrace tailWord_1397396 prefixEnd_1397396 239178604223439971807833 := by
  unfold tailWord_1397396
  simp only [CollatzResearch.WordTrace]
  refine ⟨25483609622740211540758021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33978146163653615387677361 25483609622740211540758021)
  ·
    refine ⟨4778176804263789663892129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25483609622740211540758021 4778176804263789663892129)
    ·
      refine ⟨3583632603197842247919097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4778176804263789663892129 3583632603197842247919097)
      ·
        refine ⟨2687724452398381685939323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3583632603197842247919097 2687724452398381685939323)
        ·
          refine ⟨4031586678597572528908985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687724452398381685939323 4031586678597572528908985)
          ·
            refine ⟨3023690008948179396681739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4031586678597572528908985 3023690008948179396681739)
            ·
              refine ⟨4535535013422269095022609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3023690008948179396681739 4535535013422269095022609)
              ·
                refine ⟨3401651260066701821266957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4535535013422269095022609 3401651260066701821266957)
                ·
                  refine ⟨1275619222525013182975109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3401651260066701821266957 1275619222525013182975109)
                  ·
                    refine ⟨239178604223439971807833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1275619222525013182975109 239178604223439971807833)
                    ·
                      rfl

theorem cell23_1397396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1397396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397396 prefixEnd_1397396 := by exact prefixLift 1397396
  have htrace : WordTrace (prefixWord ++ tailWord_1397396) baseStart_1397396 baseEnd_1397396 := by
    simpa [prefixWord, tailWord_1397396, baseEnd_1397396] using wordTrace_append hprefix tailTrace_1397396
  have hstable : (prefixWord ++ tailWord_1397396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397396).length < 2 ^ (prefixWord ++ tailWord_1397396).sum := by decide
  have hdescent : baseEnd_1397396 < baseStart_1397396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397435 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 2, 10]
def baseStart_1397435 : Nat := 118140960795 + 1397435 * 2 ^ 59
def prefixEnd_1397435 : Nat := 4983230072969 + 3 ^ 40 * 1397435 * 2
def baseEnd_1397435 : Nat := 239185279471948420945273

theorem tailTrace_1397435 : CollatzResearch.WordTrace tailWord_1397435 prefixEnd_1397435 239185279471948420945273 := by
  unfold tailWord_1397435
  simp only [CollatzResearch.WordTrace]
  refine ⟨50968641692339132742185759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33979094461559421828123839 50968641692339132742185759)
  ·
    refine ⟨76452962538508699113278639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50968641692339132742185759 76452962538508699113278639)
    ·
      refine ⟨114679443807763048669917959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76452962538508699113278639 114679443807763048669917959)
      ·
        refine ⟨172019165711644573004876939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114679443807763048669917959 172019165711644573004876939)
        ·
          refine ⟨258028748567466859507315409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172019165711644573004876939 258028748567466859507315409)
          ·
            refine ⟨193521561425600144630486557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 258028748567466859507315409 193521561425600144630486557)
            ·
              refine ⟨72570585534600054236432459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 193521561425600144630486557 72570585534600054236432459)
              ·
                refine ⟨108855878301900081354648689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72570585534600054236432459 108855878301900081354648689)
                ·
                  refine ⟨81641908726425061015986517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108855878301900081354648689 81641908726425061015986517)
                  ·
                    refine ⟨239185279471948420945273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 81641908726425061015986517 239185279471948420945273)
                    ·
                      rfl

theorem cell23_1397435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_1397435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397435 prefixEnd_1397435 := by exact prefixLift 1397435
  have htrace : WordTrace (prefixWord ++ tailWord_1397435) baseStart_1397435 baseEnd_1397435 := by
    simpa [prefixWord, tailWord_1397435, baseEnd_1397435] using wordTrace_append hprefix tailTrace_1397435
  have hstable : (prefixWord ++ tailWord_1397435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397435).length < 2 ^ (prefixWord ++ tailWord_1397435).sum := by decide
  have hdescent : baseEnd_1397435 < baseStart_1397435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397436 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_1397436 : Nat := 118140960795 + 1397436 * 2 ^ 59
def prefixEnd_1397436 : Nat := 4983230072969 + 3 ^ 40 * 1397436 * 2
def baseEnd_1397436 : Nat := 717556351896499758923315

theorem tailTrace_1397436 : CollatzResearch.WordTrace tailWord_1397436 prefixEnd_1397436 717556351896499758923315 := by
  unfold tailWord_1397436
  simp only [CollatzResearch.WordTrace]
  refine ⟨25484339082667754956486081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33979118776890339941981441 25484339082667754956486081)
  ·
    refine ⟨19113254312000816217364561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25484339082667754956486081 19113254312000816217364561)
    ·
      refine ⟨14334940734000612163023421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19113254312000816217364561 14334940734000612163023421)
      ·
        refine ⟨5375602775250229561133783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14334940734000612163023421 5375602775250229561133783)
        ·
          refine ⟨8063404162875344341700675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375602775250229561133783 8063404162875344341700675)
          ·
            refine ⟨12095106244313016512551013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8063404162875344341700675 12095106244313016512551013)
            ·
              refine ⟨2267832420808690596103315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12095106244313016512551013 2267832420808690596103315)
              ·
                refine ⟨3401748631213035894154973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267832420808690596103315 3401748631213035894154973)
                ·
                  refine ⟨1275655736704888460308115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3401748631213035894154973 1275655736704888460308115)
                  ·
                    refine ⟨1913483605057332690462173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1275655736704888460308115 1913483605057332690462173)
                    ·
                      refine ⟨717556351896499758923315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1913483605057332690462173 717556351896499758923315)
                      ·
                        rfl

theorem cell23_1397436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_1397436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397436 prefixEnd_1397436 := by exact prefixLift 1397436
  have htrace : WordTrace (prefixWord ++ tailWord_1397436) baseStart_1397436 baseEnd_1397436 := by
    simpa [prefixWord, tailWord_1397436, baseEnd_1397436] using wordTrace_append hprefix tailTrace_1397436
  have hstable : (prefixWord ++ tailWord_1397436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397436).length < 2 ^ (prefixWord ++ tailWord_1397436).sum := by decide
  have hdescent : baseEnd_1397436 < baseStart_1397436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397472 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1397472 : Nat := 118140960795 + 1397472 * 2 ^ 59
def prefixEnd_1397472 : Nat := 4983230072969 + 3 ^ 40 * 1397472 * 2
def baseEnd_1397472 : Nat := 717574837200061618073149

theorem tailTrace_1397472 : CollatzResearch.WordTrace tailWord_1397472 prefixEnd_1397472 717574837200061618073149 := by
  unfold tailWord_1397472
  simp only [CollatzResearch.WordTrace]
  refine ⟨25484995596602544030641335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33979994128803392040855113 25484995596602544030641335)
  ·
    refine ⟨38227493394903816045962003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25484995596602544030641335 38227493394903816045962003)
    ·
      refine ⟨57341240092355724068943005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38227493394903816045962003 57341240092355724068943005)
      ·
        refine ⟨21502965034633396525853627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57341240092355724068943005 21502965034633396525853627)
        ·
          refine ⟨32254447551950094788780441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21502965034633396525853627 32254447551950094788780441)
          ·
            refine ⟨24190835663962571091585331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32254447551950094788780441 24190835663962571091585331)
            ·
              refine ⟨36286253495943856637377997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24190835663962571091585331 36286253495943856637377997)
              ·
                refine ⟨13607345060978946239016749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36286253495943856637377997 13607345060978946239016749)
                ·
                  refine ⟨5102754397867104839631281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13607345060978946239016749 5102754397867104839631281)
                  ·
                    refine ⟨3827065798400328629723461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5102754397867104839631281 3827065798400328629723461)
                    ·
                      refine ⟨717574837200061618073149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3827065798400328629723461 717574837200061618073149)
                      ·
                        rfl

theorem cell23_1397472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1397472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397472 prefixEnd_1397472 := by exact prefixLift 1397472
  have htrace : WordTrace (prefixWord ++ tailWord_1397472) baseStart_1397472 baseEnd_1397472 := by
    simpa [prefixWord, tailWord_1397472, baseEnd_1397472] using wordTrace_append hprefix tailTrace_1397472
  have hstable : (prefixWord ++ tailWord_1397472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397472).length < 2 ^ (prefixWord ++ tailWord_1397472).sum := by decide
  have hdescent : baseEnd_1397472 < baseStart_1397472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397552 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_1397552 : Nat := 118140960795 + 1397552 * 2 ^ 59
def prefixEnd_1397552 : Nat := 4983230072969 + 3 ^ 40 * 1397552 * 2
def baseEnd_1397552 : Nat := 717615915652421305072781

theorem tailTrace_1397552 : CollatzResearch.WordTrace tailWord_1397552 prefixEnd_1397552 717615915652421305072781 := by
  unfold tailWord_1397552
  simp only [CollatzResearch.WordTrace]
  refine ⟨25486454516457630862097455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33981939355276841149463273 25486454516457630862097455)
  ·
    refine ⟨38229681774686446293146183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25486454516457630862097455 38229681774686446293146183)
    ·
      refine ⟨57344522662029669439719275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38229681774686446293146183 57344522662029669439719275)
      ·
        refine ⟨86016783993044504159578913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57344522662029669439719275 86016783993044504159578913)
        ·
          refine ⟨64512587994783378119684185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86016783993044504159578913 64512587994783378119684185)
          ·
            refine ⟨48384440996087533589763139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64512587994783378119684185 48384440996087533589763139)
            ·
              refine ⟨72576661494131300384644709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48384440996087533589763139 72576661494131300384644709)
              ·
                refine ⟨13608124030149618822120883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72576661494131300384644709 13608124030149618822120883)
                ·
                  refine ⟨20412186045224428233181325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13608124030149618822120883 20412186045224428233181325)
                  ·
                    refine ⟨7654569766959160587442997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20412186045224428233181325 7654569766959160587442997)
                    ·
                      refine ⟨717615915652421305072781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7654569766959160587442997 717615915652421305072781)
                      ·
                        rfl

theorem cell23_1397552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_1397552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397552 prefixEnd_1397552 := by exact prefixLift 1397552
  have htrace : WordTrace (prefixWord ++ tailWord_1397552) baseStart_1397552 baseEnd_1397552 := by
    simpa [prefixWord, tailWord_1397552, baseEnd_1397552] using wordTrace_append hprefix tailTrace_1397552
  have hstable : (prefixWord ++ tailWord_1397552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397552).length < 2 ^ (prefixWord ++ tailWord_1397552).sum := by decide
  have hdescent : baseEnd_1397552 < baseStart_1397552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397596 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1397596 : Nat := 118140960795 + 1397596 * 2 ^ 59
def prefixEnd_1397596 : Nat := 4983230072969 + 3 ^ 40 * 1397596 * 2
def baseEnd_1397596 : Nat := 717638508801219132922579

theorem tailTrace_1397596 : CollatzResearch.WordTrace tailWord_1397596 prefixEnd_1397596 717638508801219132922579 := by
  unfold tailWord_1397596
  simp only [CollatzResearch.WordTrace]
  refine ⟨25487256922377928619398321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33983009229837238159197761 25487256922377928619398321)
  ·
    refine ⟨19115442691783446464548741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25487256922377928619398321 19115442691783446464548741)
    ·
      refine ⟨3584145504709396212102889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19115442691783446464548741 3584145504709396212102889)
      ·
        refine ⟨2688109128532047159077167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3584145504709396212102889 2688109128532047159077167)
        ·
          refine ⟨4032163692798070738615751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688109128532047159077167 4032163692798070738615751)
          ·
            refine ⟨6048245539197106107923627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032163692798070738615751 6048245539197106107923627)
            ·
              refine ⟨9072368308795659161885441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6048245539197106107923627 9072368308795659161885441)
              ·
                refine ⟨6804276231596744371414081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9072368308795659161885441 6804276231596744371414081)
                ·
                  refine ⟨5103207173697558278560561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6804276231596744371414081 5103207173697558278560561)
                  ·
                    refine ⟨3827405380273168708920421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5103207173697558278560561 3827405380273168708920421)
                    ·
                      refine ⟨717638508801219132922579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3827405380273168708920421 717638508801219132922579)
                      ·
                        rfl

theorem cell23_1397596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1397596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397596 prefixEnd_1397596 := by exact prefixLift 1397596
  have htrace : WordTrace (prefixWord ++ tailWord_1397596) baseStart_1397596 baseEnd_1397596 := by
    simpa [prefixWord, tailWord_1397596, baseEnd_1397596] using wordTrace_append hprefix tailTrace_1397596
  have hstable : (prefixWord ++ tailWord_1397596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397596).length < 2 ^ (prefixWord ++ tailWord_1397596).sum := by decide
  have hdescent : baseEnd_1397596 < baseStart_1397596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397599 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 3]
def baseStart_1397599 : Nat := 118140960795 + 1397599 * 2 ^ 59
def prefixEnd_1397599 : Nat := 4983230072969 + 3 ^ 40 * 1397599 * 2
def baseEnd_1397599 : Nat := 717640049243182621185065

theorem tailTrace_1397599 : CollatzResearch.WordTrace tailWord_1397599 prefixEnd_1397599 717640049243182621185065 := by
  unfold tailWord_1397599
  simp only [CollatzResearch.WordTrace]
  refine ⟨50974623263744988751155851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33983082175829992500770567 50974623263744988751155851)
  ·
    refine ⟨76461934895617483126733777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50974623263744988751155851 76461934895617483126733777)
    ·
      refine ⟨57346451171713112345050333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76461934895617483126733777 57346451171713112345050333)
      ·
        refine ⟨21504919189392417129393875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57346451171713112345050333 21504919189392417129393875)
        ·
          refine ⟨32257378784088625694090813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21504919189392417129393875 32257378784088625694090813)
          ·
            refine ⟨12096517044033234635284055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32257378784088625694090813 12096517044033234635284055)
            ·
              refine ⟨18144775566049851952926083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12096517044033234635284055 18144775566049851952926083)
              ·
                refine ⟨27217163349074777929389125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18144775566049851952926083 27217163349074777929389125)
                ·
                  refine ⟨5103218127951520861760461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27217163349074777929389125 5103218127951520861760461)
                  ·
                    refine ⟨1913706797981820323160173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5103218127951520861760461 1913706797981820323160173)
                    ·
                      refine ⟨717640049243182621185065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1913706797981820323160173 717640049243182621185065)
                      ·
                        rfl

theorem cell23_1397599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_1397599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397599 prefixEnd_1397599 := by exact prefixLift 1397599
  have htrace : WordTrace (prefixWord ++ tailWord_1397599) baseStart_1397599 baseEnd_1397599 := by
    simpa [prefixWord, tailWord_1397599, baseEnd_1397599] using wordTrace_append hprefix tailTrace_1397599
  have hstable : (prefixWord ++ tailWord_1397599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397599).length < 2 ^ (prefixWord ++ tailWord_1397599).sum := by decide
  have hdescent : baseEnd_1397599 < baseStart_1397599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397750 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2]
def baseStart_1397750 : Nat := 118140960795 + 1397750 * 2 ^ 59
def prefixEnd_1397750 : Nat := 4983230072969 + 3 ^ 40 * 1397750 * 2
def baseEnd_1397750 : Nat := 717717584822011530396871

theorem tailTrace_1397750 : CollatzResearch.WordTrace tailWord_1397750 prefixEnd_1397750 717717584822011530396871 := by
  unfold tailWord_1397750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3186258167887371346243919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33986753790798627693268469 3186258167887371346243919)
  ·
    refine ⟨4779387251831057019365879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3186258167887371346243919 4779387251831057019365879)
    ·
      refine ⟨7169080877746585529048819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4779387251831057019365879 7169080877746585529048819)
      ·
        refine ⟨10753621316619878293573229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7169080877746585529048819 10753621316619878293573229)
        ·
          refine ⟨4032607993732454360089961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10753621316619878293573229 4032607993732454360089961)
          ·
            refine ⟨3024455995299340770067471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4032607993732454360089961 3024455995299340770067471)
            ·
              refine ⟨4536683992949011155101207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024455995299340770067471 4536683992949011155101207)
              ·
                refine ⟨6805025989423516732651811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4536683992949011155101207 6805025989423516732651811)
                ·
                  refine ⟨10207538984135275098977717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6805025989423516732651811 10207538984135275098977717)
                  ·
                    refine ⟨956956779762682040529161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10207538984135275098977717 956956779762682040529161)
                    ·
                      refine ⟨717717584822011530396871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 956956779762682040529161 717717584822011530396871)
                      ·
                        rfl

theorem cell23_1397750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_1397750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397750 prefixEnd_1397750 := by exact prefixLift 1397750
  have htrace : WordTrace (prefixWord ++ tailWord_1397750) baseStart_1397750 baseEnd_1397750 := by
    simpa [prefixWord, tailWord_1397750, baseEnd_1397750] using wordTrace_append hprefix tailTrace_1397750
  have hstable : (prefixWord ++ tailWord_1397750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397750).length < 2 ^ (prefixWord ++ tailWord_1397750).sum := by decide
  have hdescent : baseEnd_1397750 < baseStart_1397750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397756 : List Nat := [2, 2, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1397756 : Nat := 118140960795 + 1397756 * 2 ^ 59
def prefixEnd_1397756 : Nat := 4983230072969 + 3 ^ 40 * 1397756 * 2
def baseEnd_1397756 : Nat := 239240221901979502307281

theorem tailTrace_1397756 : CollatzResearch.WordTrace tailWord_1397756 prefixEnd_1397756 239240221901979502307281 := by
  unfold tailWord_1397756
  simp only [CollatzResearch.WordTrace]
  refine ⟨25490174762088102282310561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33986899682784136376414081 25490174762088102282310561)
  ·
    refine ⟨19117631071566076711732921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25490174762088102282310561 19117631071566076711732921)
    ·
      refine ⟨14338223303674557533799691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19117631071566076711732921 14338223303674557533799691)
      ·
        refine ⟨21507334955511836300699537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14338223303674557533799691 21507334955511836300699537)
        ·
          refine ⟨16130501216633877225524653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21507334955511836300699537 16130501216633877225524653)
          ·
            refine ⟨6048937956237703959571745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16130501216633877225524653 6048937956237703959571745)
            ·
              refine ⟨4536703467178277969678809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6048937956237703959571745 4536703467178277969678809)
              ·
                refine ⟨3402527600383708477259107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4536703467178277969678809 3402527600383708477259107)
                ·
                  refine ⟨5103791400575562715888661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402527600383708477259107 5103791400575562715888661)
                  ·
                    refine ⟨239240221901979502307281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5103791400575562715888661 239240221901979502307281)
                    ·
                      rfl

theorem cell23_1397756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1397756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397756 prefixEnd_1397756 := by exact prefixLift 1397756
  have htrace : WordTrace (prefixWord ++ tailWord_1397756) baseStart_1397756 baseEnd_1397756 := by
    simpa [prefixWord, tailWord_1397756, baseEnd_1397756] using wordTrace_append hprefix tailTrace_1397756
  have hstable : (prefixWord ++ tailWord_1397756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397756).length < 2 ^ (prefixWord ++ tailWord_1397756).sum := by decide
  have hdescent : baseEnd_1397756 < baseStart_1397756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397759 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_1397759 : Nat := 118140960795 + 1397759 * 2 ^ 59
def prefixEnd_1397759 : Nat := 4983230072969 + 3 ^ 40 * 1397759 * 2
def baseEnd_1397759 : Nat := 717722206147901995184329

theorem tailTrace_1397759 : CollatzResearch.WordTrace tailWord_1397759 prefixEnd_1397759 717722206147901995184329 := by
  unfold tailWord_1397759
  simp only [CollatzResearch.WordTrace]
  refine ⟨50980458943165336076980331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33986972628776890717986887 50980458943165336076980331)
  ·
    refine ⟨76470688414748004115470497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50980458943165336076980331 76470688414748004115470497)
    ·
      refine ⟨57353016311061003086602873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76470688414748004115470497 57353016311061003086602873)
      ·
        refine ⟨43014762233295752314952155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57353016311061003086602873 43014762233295752314952155)
        ·
          refine ⟨64522143349943628472428233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43014762233295752314952155 64522143349943628472428233)
          ·
            refine ⟨48391607512457721354321175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64522143349943628472428233 48391607512457721354321175)
            ·
              refine ⟨72587411268686582031481763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48391607512457721354321175 72587411268686582031481763)
              ·
                refine ⟨108881116903029873047222645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72587411268686582031481763 108881116903029873047222645)
                ·
                  refine ⟨10207604709659050598177123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108881116903029873047222645 10207604709659050598177123)
                  ·
                    refine ⟨15311407064488575897265685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10207604709659050598177123 15311407064488575897265685)
                    ·
                      refine ⟨717722206147901995184329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15311407064488575897265685 717722206147901995184329)
                      ·
                        rfl

theorem cell23_1397759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_1397759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397759 prefixEnd_1397759 := by exact prefixLift 1397759
  have htrace : WordTrace (prefixWord ++ tailWord_1397759) baseStart_1397759 baseEnd_1397759 := by
    simpa [prefixWord, tailWord_1397759, baseEnd_1397759] using wordTrace_append hprefix tailTrace_1397759
  have hstable : (prefixWord ++ tailWord_1397759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397759).length < 2 ^ (prefixWord ++ tailWord_1397759).sum := by decide
  have hdescent : baseEnd_1397759 < baseStart_1397759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397779 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7]
def baseStart_1397779 : Nat := 118140960795 + 1397779 * 2 ^ 59
def prefixEnd_1397779 : Nat := 4983230072969 + 3 ^ 40 * 1397779 * 2
def baseEnd_1397779 : Nat := 717732475760991916934237

theorem tailTrace_1397779 : CollatzResearch.WordTrace tailWord_1397779 prefixEnd_1397779 717732475760991916934237 := by
  unfold tailWord_1397779
  simp only [CollatzResearch.WordTrace]
  refine ⟨50981188403092879492708391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33987458935395252995138927 50981188403092879492708391)
  ·
    refine ⟨76471782604639319239062587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50981188403092879492708391 76471782604639319239062587)
    ·
      refine ⟨114707673906958978858593881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76471782604639319239062587 114707673906958978858593881)
      ·
        refine ⟨86030755430219234143945411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114707673906958978858593881 86030755430219234143945411)
        ·
          refine ⟨129046133145328851215918117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86030755430219234143945411 129046133145328851215918117)
          ·
            refine ⟨24196149964749159602984647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129046133145328851215918117 24196149964749159602984647)
            ·
              refine ⟨36294224947123739404476971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24196149964749159602984647 36294224947123739404476971)
              ·
                refine ⟨54441337420685609106715457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36294224947123739404476971 54441337420685609106715457)
                ·
                  refine ⟨40831003065514206830036593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54441337420685609106715457 40831003065514206830036593)
                  ·
                    refine ⟨30623252299135655122527445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40831003065514206830036593 30623252299135655122527445)
                    ·
                      refine ⟨717732475760991916934237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30623252299135655122527445 717732475760991916934237)
                      ·
                        rfl

theorem cell23_1397779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_1397779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397779 prefixEnd_1397779 := by exact prefixLift 1397779
  have htrace : WordTrace (prefixWord ++ tailWord_1397779) baseStart_1397779 baseEnd_1397779 := by
    simpa [prefixWord, tailWord_1397779, baseEnd_1397779] using wordTrace_append hprefix tailTrace_1397779
  have hstable : (prefixWord ++ tailWord_1397779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397779).length < 2 ^ (prefixWord ++ tailWord_1397779).sum := by decide
  have hdescent : baseEnd_1397779 < baseStart_1397779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397783 : List Nat := [1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1397783 : Nat := 118140960795 + 1397783 * 2 ^ 59
def prefixEnd_1397783 : Nat := 4983230072969 + 3 ^ 40 * 1397783 * 2
def baseEnd_1397783 : Nat := 717734529683609901284219

theorem tailTrace_1397783 : CollatzResearch.WordTrace tailWord_1397783 prefixEnd_1397783 717734529683609901284219 := by
  unfold tailWord_1397783
  simp only [CollatzResearch.WordTrace]
  refine ⟨50981334295078388175854003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33987556196718925450569335 50981334295078388175854003)
  ·
    refine ⟨76472001442617582263781005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50981334295078388175854003 76472001442617582263781005)
    ·
      refine ⟨28677000540981593348917877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76472001442617582263781005 28677000540981593348917877)
      ·
        refine ⟨2688468800717024376461051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28677000540981593348917877 2688468800717024376461051)
        ·
          refine ⟨4032703201075536564691577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688468800717024376461051 4032703201075536564691577)
          ·
            refine ⟨3024527400806652423518683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4032703201075536564691577 3024527400806652423518683)
            ·
              refine ⟨4536791101209978635278025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024527400806652423518683 4536791101209978635278025)
              ·
                refine ⟨3402593325907483976458519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4536791101209978635278025 3402593325907483976458519)
                ·
                  refine ⟨5103889988861225964687779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402593325907483976458519 5103889988861225964687779)
                  ·
                    refine ⟨7655834983291838947031669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5103889988861225964687779 7655834983291838947031669)
                    ·
                      refine ⟨717734529683609901284219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7655834983291838947031669 717734529683609901284219)
                      ·
                        rfl

theorem cell23_1397783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1397783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397783 prefixEnd_1397783 := by exact prefixLift 1397783
  have htrace : WordTrace (prefixWord ++ tailWord_1397783) baseStart_1397783 baseEnd_1397783 := by
    simpa [prefixWord, tailWord_1397783, baseEnd_1397783] using wordTrace_append hprefix tailTrace_1397783
  have hstable : (prefixWord ++ tailWord_1397783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397783).length < 2 ^ (prefixWord ++ tailWord_1397783).sum := by decide
  have hdescent : baseEnd_1397783 < baseStart_1397783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397793 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_1397793 : Nat := 118140960795 + 1397793 * 2 ^ 59
def prefixEnd_1397793 : Nat := 4983230072969 + 3 ^ 40 * 1397793 * 2
def baseEnd_1397793 : Nat := 717739664490154862159173

theorem tailTrace_1397793 : CollatzResearch.WordTrace tailWord_1397793 prefixEnd_1397793 717739664490154862159173 := by
  unfold tailWord_1397793
  simp only [CollatzResearch.WordTrace]
  refine ⟨50981699025042159883718033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33987799350028106589145355 50981699025042159883718033)
  ·
    refine ⟨38236274268781619912788525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50981699025042159883718033 38236274268781619912788525)
    ·
      refine ⟨14338602850793107467295697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38236274268781619912788525 14338602850793107467295697)
      ·
        refine ⟨10753952138094830600471773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14338602850793107467295697 10753952138094830600471773)
        ·
          refine ⟨4032732051785561475176915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10753952138094830600471773 4032732051785561475176915)
          ·
            refine ⟨6049098077678342212765373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4032732051785561475176915 6049098077678342212765373)
            ·
              refine ⟨2268411779129378329787015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6049098077678342212765373 2268411779129378329787015)
              ·
                refine ⟨3402617668694067494680523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268411779129378329787015 3402617668694067494680523)
                ·
                  refine ⟨5103926503041101242020785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3402617668694067494680523 5103926503041101242020785)
                  ·
                    refine ⟨3827944877280825931515589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5103926503041101242020785 3827944877280825931515589)
                    ·
                      refine ⟨717739664490154862159173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3827944877280825931515589 717739664490154862159173)
                      ·
                        rfl

theorem cell23_1397793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_1397793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397793 prefixEnd_1397793 := by exact prefixLift 1397793
  have htrace : WordTrace (prefixWord ++ tailWord_1397793) baseStart_1397793 baseEnd_1397793 := by
    simpa [prefixWord, tailWord_1397793, baseEnd_1397793] using wordTrace_append hprefix tailTrace_1397793
  have hstable : (prefixWord ++ tailWord_1397793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397793).length < 2 ^ (prefixWord ++ tailWord_1397793).sum := by decide
  have hdescent : baseEnd_1397793 < baseStart_1397793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397823 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 5, 3, 2]
def baseStart_1397823 : Nat := 118140960795 + 1397823 * 2 ^ 59
def prefixEnd_1397823 : Nat := 4983230072969 + 3 ^ 40 * 1397823 * 2
def baseEnd_1397823 : Nat := 717755068909789744784035

theorem tailTrace_1397823 : CollatzResearch.WordTrace tailWord_1397823 prefixEnd_1397823 717755068909789744784035 := by
  unfold tailWord_1397823
  simp only [CollatzResearch.WordTrace]
  refine ⟨50982793214933475007310123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33988528809955650004873415 50982793214933475007310123)
  ·
    refine ⟨76474189822400212510965185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50982793214933475007310123 76474189822400212510965185)
    ·
      refine ⟨57355642366800159383223889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76474189822400212510965185 57355642366800159383223889)
      ·
        refine ⟨43016731775100119537417917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57355642366800159383223889 43016731775100119537417917)
        ·
          refine ⟨16131274415662544826531719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43016731775100119537417917 16131274415662544826531719)
          ·
            refine ⟨24196911623493817239797579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16131274415662544826531719 24196911623493817239797579)
            ·
              refine ⟨36295367435240725859696369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24196911623493817239797579 36295367435240725859696369)
              ·
                refine ⟨27221525576430544394772277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36295367435240725859696369 27221525576430544394772277)
                ·
                  refine ⟨2552018022790363537009901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27221525576430544394772277 2552018022790363537009901)
                  ·
                    refine ⟨957006758546386326378713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2552018022790363537009901 957006758546386326378713)
                    ·
                      refine ⟨717755068909789744784035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957006758546386326378713 717755068909789744784035)
                      ·
                        rfl

theorem cell23_1397823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_1397823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397823 prefixEnd_1397823 := by exact prefixLift 1397823
  have htrace : WordTrace (prefixWord ++ tailWord_1397823) baseStart_1397823 baseEnd_1397823 := by
    simpa [prefixWord, tailWord_1397823, baseEnd_1397823] using wordTrace_append hprefix tailTrace_1397823
  have hstable : (prefixWord ++ tailWord_1397823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397823).length < 2 ^ (prefixWord ++ tailWord_1397823).sum := by decide
  have hdescent : baseEnd_1397823 < baseStart_1397823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397836 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1397836 : Nat := 118140960795 + 1397836 * 2 ^ 59
def prefixEnd_1397836 : Nat := 4983230072969 + 3 ^ 40 * 1397836 * 2
def baseEnd_1397836 : Nat := 717761744158298193921475

theorem tailTrace_1397836 : CollatzResearch.WordTrace tailWord_1397836 prefixEnd_1397836 717761744158298193921475 := by
  unfold tailWord_1397836
  simp only [CollatzResearch.WordTrace]
  refine ⟨25491633681943189113766681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33988844909257585485022241 25491633681943189113766681)
  ·
    refine ⟨19118725261457391835325011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25491633681943189113766681 19118725261457391835325011)
    ·
      refine ⟨28678087892186087752987517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19118725261457391835325011 28678087892186087752987517)
      ·
        refine ⟨10754282959569782907370319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28678087892186087752987517 10754282959569782907370319)
        ·
          refine ⟨16131424439354674361055479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10754282959569782907370319 16131424439354674361055479)
          ·
            refine ⟨24197136659032011541583219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16131424439354674361055479 24197136659032011541583219)
            ·
              refine ⟨36295704988548017312374829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24197136659032011541583219 36295704988548017312374829)
              ·
                refine ⟨13610889370705506492140561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36295704988548017312374829 13610889370705506492140561)
                ·
                  refine ⟨10208167028029129869105421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13610889370705506492140561 10208167028029129869105421)
                  ·
                    refine ⟨3828062635510923700914533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10208167028029129869105421 3828062635510923700914533)
                    ·
                      refine ⟨717761744158298193921475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3828062635510923700914533 717761744158298193921475)
                      ·
                        rfl

theorem cell23_1397836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1397836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397836 prefixEnd_1397836 := by exact prefixLift 1397836
  have htrace : WordTrace (prefixWord ++ tailWord_1397836) baseStart_1397836 baseEnd_1397836 := by
    simpa [prefixWord, tailWord_1397836, baseEnd_1397836] using wordTrace_append hprefix tailTrace_1397836
  have hstable : (prefixWord ++ tailWord_1397836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397836).length < 2 ^ (prefixWord ++ tailWord_1397836).sum := by decide
  have hdescent : baseEnd_1397836 < baseStart_1397836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397856 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1397856 : Nat := 118140960795 + 1397856 * 2 ^ 59
def prefixEnd_1397856 : Nat := 4983230072969 + 3 ^ 40 * 1397856 * 2
def baseEnd_1397856 : Nat := 717772013771388115671383

theorem tailTrace_1397856 : CollatzResearch.WordTrace tailWord_1397856 prefixEnd_1397856 717772013771388115671383 := by
  unfold tailWord_1397856
  simp only [CollatzResearch.WordTrace]
  refine ⟨25491998411906960821630711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33989331215875947762174281 25491998411906960821630711)
  ·
    refine ⟨38237997617860441232446067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25491998411906960821630711 38237997617860441232446067)
    ·
      refine ⟨57356996426790661848669101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38237997617860441232446067 57356996426790661848669101)
      ·
        refine ⟨21508873660046498193250913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57356996426790661848669101 21508873660046498193250913)
        ·
          refine ⟨16131655245034873644938185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21508873660046498193250913 16131655245034873644938185)
          ·
            refine ⟨12098741433776155233703639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16131655245034873644938185 12098741433776155233703639)
            ·
              refine ⟨18148112150664232850555459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12098741433776155233703639 18148112150664232850555459)
              ·
                refine ⟨27222168225996349275833189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18148112150664232850555459 27222168225996349275833189)
                ·
                  refine ⟨5104156542374315489218723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27222168225996349275833189 5104156542374315489218723)
                  ·
                    refine ⟨7656234813561473233828085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5104156542374315489218723 7656234813561473233828085)
                    ·
                      refine ⟨717772013771388115671383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7656234813561473233828085 717772013771388115671383)
                      ·
                        rfl

theorem cell23_1397856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1397856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397856 prefixEnd_1397856 := by exact prefixLift 1397856
  have htrace : WordTrace (prefixWord ++ tailWord_1397856) baseStart_1397856 baseEnd_1397856 := by
    simpa [prefixWord, tailWord_1397856, baseEnd_1397856] using wordTrace_append hprefix tailTrace_1397856
  have hstable : (prefixWord ++ tailWord_1397856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397856).length < 2 ^ (prefixWord ++ tailWord_1397856).sum := by decide
  have hdescent : baseEnd_1397856 < baseStart_1397856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397870 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_1397870 : Nat := 118140960795 + 1397870 * 2 ^ 59
def prefixEnd_1397870 : Nat := 4983230072969 + 3 ^ 40 * 1397870 * 2
def baseEnd_1397870 : Nat := 717779202500551060896319

theorem tailTrace_1397870 : CollatzResearch.WordTrace tailWord_1397870 prefixEnd_1397870 717779202500551060896319 := by
  unfold tailWord_1397870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373063430720400254283883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33989671630508801356180709 6373063430720400254283883)
  ·
    refine ⟨9559595146080600381425825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6373063430720400254283883 9559595146080600381425825)
    ·
      refine ⟨7169696359560450286069369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9559595146080600381425825 7169696359560450286069369)
      ·
        refine ⟨5377272269670337714552027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7169696359560450286069369 5377272269670337714552027)
        ·
          refine ⟨8065908404505506571828041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5377272269670337714552027 8065908404505506571828041)
          ·
            refine ⟨6049431303379129928871031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8065908404505506571828041 6049431303379129928871031)
            ·
              refine ⟨9074146955068694893306547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6049431303379129928871031 9074146955068694893306547)
              ·
                refine ⟨13611220432603042339959821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074146955068694893306547 13611220432603042339959821)
                ·
                  refine ⟨5104207662226140877484933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13611220432603042339959821 5104207662226140877484933)
                  ·
                    refine ⟨957038936667401414528425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104207662226140877484933 957038936667401414528425)
                    ·
                      refine ⟨717779202500551060896319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957038936667401414528425 717779202500551060896319)
                      ·
                        rfl

theorem cell23_1397870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_1397870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397870 prefixEnd_1397870 := by exact prefixLift 1397870
  have htrace : WordTrace (prefixWord ++ tailWord_1397870) baseStart_1397870 baseEnd_1397870 := by
    simpa [prefixWord, tailWord_1397870, baseEnd_1397870] using wordTrace_append hprefix tailTrace_1397870
  have hstable : (prefixWord ++ tailWord_1397870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397870).length < 2 ^ (prefixWord ++ tailWord_1397870).sum := by decide
  have hdescent : baseEnd_1397870 < baseStart_1397870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397927 : List Nat := [1, 1, 6, 2, 1, 2, 2, 3, 5]
def baseStart_1397927 : Nat := 118140960795 + 1397927 * 2 ^ 59
def prefixEnd_1397927 : Nat := 4983230072969 + 3 ^ 40 * 1397927 * 2
def baseEnd_1397927 : Nat := 79756496766428593098173

theorem tailTrace_1397927 : CollatzResearch.WordTrace tailWord_1397927 prefixEnd_1397927 79756496766428593098173 := by
  unfold tailWord_1397927
  simp only [CollatzResearch.WordTrace]
  refine ⟨50986586406556700769096035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33991057604371133846064023 50986586406556700769096035)
  ·
    refine ⟨76479879609835051153644053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50986586406556700769096035 76479879609835051153644053)
    ·
      refine ⟨3584994356711018022827065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76479879609835051153644053 3584994356711018022827065)
      ·
        refine ⟨2688745767533263517120299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3584994356711018022827065 2688745767533263517120299)
        ·
          refine ⟨4033118651299895275680449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688745767533263517120299 4033118651299895275680449)
          ·
            refine ⟨3024838988474921456760337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4033118651299895275680449 3024838988474921456760337)
            ·
              refine ⟨2268629241356191092570253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3024838988474921456760337 2268629241356191092570253)
              ·
                refine ⟨850735965508571659713845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2268629241356191092570253 850735965508571659713845)
                ·
                  refine ⟨79756496766428593098173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 850735965508571659713845 79756496766428593098173)
                  ·
                    rfl

theorem cell23_1397927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 5].length) (baseStart_1397927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397927 prefixEnd_1397927 := by exact prefixLift 1397927
  have htrace : WordTrace (prefixWord ++ tailWord_1397927) baseStart_1397927 baseEnd_1397927 := by
    simpa [prefixWord, tailWord_1397927, baseEnd_1397927] using wordTrace_append hprefix tailTrace_1397927
  have hstable : (prefixWord ++ tailWord_1397927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397927).length < 2 ^ (prefixWord ++ tailWord_1397927).sum := by decide
  have hdescent : baseEnd_1397927 < baseStart_1397927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397943 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_1397943 : Nat := 118140960795 + 1397943 * 2 ^ 59
def prefixEnd_1397943 : Nat := 4983230072969 + 3 ^ 40 * 1397943 * 2
def baseEnd_1397943 : Nat := 717816686588329275283483

theorem tailTrace_1397943 : CollatzResearch.WordTrace tailWord_1397943 prefixEnd_1397943 717816686588329275283483 := by
  unfold tailWord_1397943
  simp only [CollatzResearch.WordTrace]
  refine ⟨50987169974498735501678483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33991446649665823667785655 50987169974498735501678483)
  ·
    refine ⟨76480754961748103252517725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50987169974498735501678483 76480754961748103252517725)
    ·
      refine ⟨28680283110655538719694147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76480754961748103252517725 28680283110655538719694147)
      ·
        refine ⟨43020424665983308079541221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28680283110655538719694147 43020424665983308079541221)
        ·
          refine ⟨8066329624871870264913979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43020424665983308079541221 8066329624871870264913979)
          ·
            refine ⟨12099494437307805397370969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8066329624871870264913979 12099494437307805397370969)
            ·
              refine ⟨9074620827980854048028227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12099494437307805397370969 9074620827980854048028227)
              ·
                refine ⟨13611931241971281072042341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9074620827980854048028227 13611931241971281072042341)
                ·
                  refine ⟨2552237107869615201007939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13611931241971281072042341 2552237107869615201007939)
                  ·
                    refine ⟨3828355661804422801511909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2552237107869615201007939 3828355661804422801511909)
                    ·
                      refine ⟨717816686588329275283483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3828355661804422801511909 717816686588329275283483)
                      ·
                        rfl

theorem cell23_1397943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_1397943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397943 prefixEnd_1397943 := by exact prefixLift 1397943
  have htrace : WordTrace (prefixWord ++ tailWord_1397943) baseStart_1397943 baseEnd_1397943 := by
    simpa [prefixWord, tailWord_1397943, baseEnd_1397943] using wordTrace_append hprefix tailTrace_1397943
  have hstable : (prefixWord ++ tailWord_1397943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397943).length < 2 ^ (prefixWord ++ tailWord_1397943).sum := by decide
  have hdescent : baseEnd_1397943 < baseStart_1397943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397960 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 2, 4, 2]
def baseStart_1397960 : Nat := 118140960795 + 1397960 * 2 ^ 59
def prefixEnd_1397960 : Nat := 4983230072969 + 3 ^ 40 * 1397960 * 2
def baseEnd_1397960 : Nat := 717825415759455708770905

theorem tailTrace_1397960 : CollatzResearch.WordTrace tailWord_1397960 prefixEnd_1397960 717825415759455708770905 := by
  unfold tailWord_1397960
  simp only [CollatzResearch.WordTrace]
  refine ⟨25493895007718573702523667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33991860010291431603364889 25493895007718573702523667)
  ·
    refine ⟨38240842511577860553785501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25493895007718573702523667 38240842511577860553785501)
    ·
      refine ⟨14340315941841697707669563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38240842511577860553785501 14340315941841697707669563)
      ·
        refine ⟨21510473912762546561504345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14340315941841697707669563 21510473912762546561504345)
        ·
          refine ⟨16132855434571909921128259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21510473912762546561504345 16132855434571909921128259)
          ·
            refine ⟨24199283151857864881692389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16132855434571909921128259 24199283151857864881692389)
            ·
              refine ⟨4537365590973349665317323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24199283151857864881692389 4537365590973349665317323)
              ·
                refine ⟨6806048386460024497975985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537365590973349665317323 6806048386460024497975985)
                ·
                  refine ⟨5104536289845018373481989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6806048386460024497975985 5104536289845018373481989)
                  ·
                    refine ⟨957100554345940945027873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5104536289845018373481989 957100554345940945027873)
                    ·
                      refine ⟨717825415759455708770905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957100554345940945027873 717825415759455708770905)
                      ·
                        rfl

theorem cell23_1397960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_1397960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397960 prefixEnd_1397960 := by exact prefixLift 1397960
  have htrace : WordTrace (prefixWord ++ tailWord_1397960) baseStart_1397960 baseEnd_1397960 := by
    simpa [prefixWord, tailWord_1397960, baseEnd_1397960] using wordTrace_append hprefix tailTrace_1397960
  have hstable : (prefixWord ++ tailWord_1397960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397960).length < 2 ^ (prefixWord ++ tailWord_1397960).sum := by decide
  have hdescent : baseEnd_1397960 < baseStart_1397960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397963 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 3]
def baseStart_1397963 : Nat := 118140960795 + 1397963 * 2 ^ 59
def prefixEnd_1397963 : Nat := 4983230072969 + 3 ^ 40 * 1397963 * 2
def baseEnd_1397963 : Nat := 717826956201419197033391

theorem tailTrace_1397963 : CollatzResearch.WordTrace tailWord_1397963 prefixEnd_1397963 717826956201419197033391 := by
  unfold tailWord_1397963
  simp only [CollatzResearch.WordTrace]
  refine ⟨50987899434426278917406543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33991932956284185944937695 50987899434426278917406543)
  ·
    refine ⟨76481849151639418376109815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50987899434426278917406543 76481849151639418376109815)
    ·
      refine ⟨114722773727459127564164723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76481849151639418376109815 114722773727459127564164723)
      ·
        refine ⟨172084160591188691346247085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114722773727459127564164723 172084160591188691346247085)
        ·
          refine ⟨64531560221695759254842657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172084160591188691346247085 64531560221695759254842657)
          ·
            refine ⟨48398670166271819441131993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64531560221695759254842657 48398670166271819441131993)
            ·
              refine ⟨36299002624703864580848995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48398670166271819441131993 36299002624703864580848995)
              ·
                refine ⟨54448503937055796871273493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36299002624703864580848995 54448503937055796871273493)
                ·
                  refine ⟨2552273622049490478340945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54448503937055796871273493 2552273622049490478340945)
                  ·
                    refine ⟨1914205216537117858755709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2552273622049490478340945 1914205216537117858755709)
                    ·
                      refine ⟨717826956201419197033391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1914205216537117858755709 717826956201419197033391)
                      ·
                        rfl

theorem cell23_1397963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 3].length) (baseStart_1397963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397963 prefixEnd_1397963 := by exact prefixLift 1397963
  have htrace : WordTrace (prefixWord ++ tailWord_1397963) baseStart_1397963 baseEnd_1397963 := by
    simpa [prefixWord, tailWord_1397963, baseEnd_1397963] using wordTrace_append hprefix tailTrace_1397963
  have hstable : (prefixWord ++ tailWord_1397963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397963).length < 2 ^ (prefixWord ++ tailWord_1397963).sum := by decide
  have hdescent : baseEnd_1397963 < baseStart_1397963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397970 : List Nat := [3, 2, 2, 2, 1, 1, 1, 4, 3, 4]
def baseStart_1397970 : Nat := 118140960795 + 1397970 * 2 ^ 59
def prefixEnd_1397970 : Nat := 4983230072969 + 3 ^ 40 * 1397970 * 2
def baseEnd_1397970 : Nat := 239276850188666889881953

theorem tailTrace_1397970 : CollatzResearch.WordTrace tailWord_1397970 prefixEnd_1397970 239276850188666889881953 := by
  unfold tailWord_1397970
  simp only [CollatzResearch.WordTrace]
  refine ⟨12747038686350229778227841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33992103163600612741940909 12747038686350229778227841)
  ·
    refine ⟨9560279014762672333670881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12747038686350229778227841 9560279014762672333670881)
    ·
      refine ⟨7170209261072004250253161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9560279014762672333670881 7170209261072004250253161)
      ·
        refine ⟨5377656945804003187689871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7170209261072004250253161 5377656945804003187689871)
        ·
          refine ⟨8066485418706004781534807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5377656945804003187689871 8066485418706004781534807)
          ·
            refine ⟨12099728128059007172302211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8066485418706004781534807 12099728128059007172302211)
            ·
              refine ⟨18149592192088510758453317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12099728128059007172302211 18149592192088510758453317)
              ·
                refine ⟨3403048536016595767209997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18149592192088510758453317 3403048536016595767209997)
                ·
                  refine ⟨1276143201006223412703749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3403048536016595767209997 1276143201006223412703749)
                  ·
                    refine ⟨239276850188666889881953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1276143201006223412703749 239276850188666889881953)
                    ·
                      rfl

theorem cell23_1397970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_1397970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397970 prefixEnd_1397970 := by exact prefixLift 1397970
  have htrace : WordTrace (prefixWord ++ tailWord_1397970) baseStart_1397970 baseEnd_1397970 := by
    simpa [prefixWord, tailWord_1397970, baseEnd_1397970] using wordTrace_append hprefix tailTrace_1397970
  have hstable : (prefixWord ++ tailWord_1397970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397970).length < 2 ^ (prefixWord ++ tailWord_1397970).sum := by decide
  have hdescent : baseEnd_1397970 < baseStart_1397970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1397997 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_1397997 : Nat := 118140960795 + 1397997 * 2 ^ 59
def prefixEnd_1397997 : Nat := 4983230072969 + 3 ^ 40 * 1397997 * 2
def baseEnd_1397997 : Nat := 717844414543672064008235

theorem tailTrace_1397997 : CollatzResearch.WordTrace tailWord_1397997 prefixEnd_1397997 717844414543672064008235 := by
  unfold tailWord_1397997
  simp only [CollatzResearch.WordTrace]
  refine ⟨50989139516303102724144245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33992759677535401816096163 50989139516303102724144245)
  ·
    refine ⟨4780231829653415880388523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50989139516303102724144245 4780231829653415880388523)
    ·
      refine ⟨7170347744480123820582785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4780231829653415880388523 7170347744480123820582785)
      ·
        refine ⟨5377760808360092865437089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7170347744480123820582785 5377760808360092865437089)
        ·
          refine ⟨4033320606270069649077817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5377760808360092865437089 4033320606270069649077817)
          ·
            refine ⟨3024990454702552236808363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4033320606270069649077817 3024990454702552236808363)
            ·
              refine ⟨4537485682053828355212545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3024990454702552236808363 4537485682053828355212545)
              ·
                refine ⟨3403114261540371266409409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4537485682053828355212545 3403114261540371266409409)
                ·
                  refine ⟨2552335696155278449807057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3403114261540371266409409 2552335696155278449807057)
                  ·
                    refine ⟨1914251772116458837355293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2552335696155278449807057 1914251772116458837355293)
                    ·
                      refine ⟨717844414543672064008235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1914251772116458837355293 717844414543672064008235)
                      ·
                        rfl

theorem cell23_1397997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_1397997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1397997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1397997 prefixEnd_1397997 := by exact prefixLift 1397997
  have htrace : WordTrace (prefixWord ++ tailWord_1397997) baseStart_1397997 baseEnd_1397997 := by
    simpa [prefixWord, tailWord_1397997, baseEnd_1397997] using wordTrace_append hprefix tailTrace_1397997
  have hstable : (prefixWord ++ tailWord_1397997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1397997).length < 2 ^ (prefixWord ++ tailWord_1397997).sum := by decide
  have hdescent : baseEnd_1397997 < baseStart_1397997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1397997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398017 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 6]
def baseStart_1398017 : Nat := 118140960795 + 1398017 * 2 ^ 59
def prefixEnd_1398017 : Nat := 4983230072969 + 3 ^ 40 * 1398017 * 2
def baseEnd_1398017 : Nat := 79761631572973553973127

theorem tailTrace_1398017 : CollatzResearch.WordTrace tailWord_1398017 prefixEnd_1398017 79761631572973553973127 := by
  unfold tailWord_1398017
  simp only [CollatzResearch.WordTrace]
  refine ⟨50989868976230646139872305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33993245984153764093248203 50989868976230646139872305)
  ·
    refine ⟨38242401732172984604904229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50989868976230646139872305 38242401732172984604904229)
    ·
      refine ⟨7170450324782434613419543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38242401732172984604904229 7170450324782434613419543)
      ·
        refine ⟨10755675487173651920129315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7170450324782434613419543 10755675487173651920129315)
        ·
          refine ⟨16133513230760477880193973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10755675487173651920129315 16133513230760477880193973)
          ·
            refine ⟨1512516865383794801268185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16133513230760477880193973 1512516865383794801268185)
            ·
              refine ⟨1134387649037846100951139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512516865383794801268185 1134387649037846100951139)
              ·
                refine ⟨1701581473556769151426709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134387649037846100951139 1701581473556769151426709)
                ·
                  refine ⟨79761631572973553973127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1701581473556769151426709 79761631572973553973127)
                  ·
                    rfl

theorem cell23_1398017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 6].length) (baseStart_1398017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398017 prefixEnd_1398017 := by exact prefixLift 1398017
  have htrace : WordTrace (prefixWord ++ tailWord_1398017) baseStart_1398017 baseEnd_1398017 := by
    simpa [prefixWord, tailWord_1398017, baseEnd_1398017] using wordTrace_append hprefix tailTrace_1398017
  have hstable : (prefixWord ++ tailWord_1398017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398017).length < 2 ^ (prefixWord ++ tailWord_1398017).sum := by decide
  have hdescent : baseEnd_1398017 < baseStart_1398017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398030 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 3, 5]
def baseStart_1398030 : Nat := 118140960795 + 1398030 * 2 ^ 59
def prefixEnd_1398030 : Nat := 4983230072969 + 3 ^ 40 * 1398030 * 2
def baseEnd_1398030 : Nat := 239287119801756811631861

theorem tailTrace_1398030 : CollatzResearch.WordTrace tailWord_1398030 prefixEnd_1398030 239287119801756811631861 := by
  unfold tailWord_1398030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373792890647943670011943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33993562083455699573397029 6373792890647943670011943)
  ·
    refine ⟨9560689335971915505017915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6373792890647943670011943 9560689335971915505017915)
    ·
      refine ⟨14341034003957873257526873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9560689335971915505017915 14341034003957873257526873)
      ·
        refine ⟨10755775502968404943145155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14341034003957873257526873 10755775502968404943145155)
        ·
          refine ⟨16133663254452607414717733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10755775502968404943145155 16133663254452607414717733)
          ·
            refine ⟨3025061860209863890259575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16133663254452607414717733 3025061860209863890259575)
            ·
              refine ⟨4537592790314795835389363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025061860209863890259575 4537592790314795835389363)
              ·
                refine ⟨6806389185472193753084045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537592790314795835389363 6806389185472193753084045)
                ·
                  refine ⟨2552395944552072657406517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6806389185472193753084045 2552395944552072657406517)
                  ·
                    refine ⟨239287119801756811631861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2552395944552072657406517 239287119801756811631861)
                    ·
                      rfl

theorem cell23_1398030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_1398030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398030 prefixEnd_1398030 := by exact prefixLift 1398030
  have htrace : WordTrace (prefixWord ++ tailWord_1398030) baseStart_1398030 baseEnd_1398030 := by
    simpa [prefixWord, tailWord_1398030, baseEnd_1398030] using wordTrace_append hprefix tailTrace_1398030
  have hstable : (prefixWord ++ tailWord_1398030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398030).length < 2 ^ (prefixWord ++ tailWord_1398030).sum := by decide
  have hdescent : baseEnd_1398030 < baseStart_1398030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398063 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_1398063 : Nat := 118140960795 + 1398063 * 2 ^ 59
def prefixEnd_1398063 : Nat := 4983230072969 + 3 ^ 40 * 1398063 * 2
def baseEnd_1398063 : Nat := 717878304266868805782931

theorem tailTrace_1398063 : CollatzResearch.WordTrace tailWord_1398063 prefixEnd_1398063 717878304266868805782931 := by
  unfold tailWord_1398063
  simp only [CollatzResearch.WordTrace]
  refine ⟨50991546734063995996046843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33994364489375997330697895 50991546734063995996046843)
  ·
    refine ⟨76487320101095993994070265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50991546734063995996046843 76487320101095993994070265)
    ·
      refine ⟨57365490075821995495552699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76487320101095993994070265 57365490075821995495552699)
      ·
        refine ⟨86048235113732993243329049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57365490075821995495552699 86048235113732993243329049)
        ·
          refine ⟨64536176335299744932496787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86048235113732993243329049 64536176335299744932496787)
          ·
            refine ⟨96804264502949617398745181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64536176335299744932496787 96804264502949617398745181)
            ·
              refine ⟨36301599188606106524529443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96804264502949617398745181 36301599188606106524529443)
              ·
                refine ⟨54452398782909159786794165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36301599188606106524529443 54452398782909159786794165)
                ·
                  refine ⟨5104912385897733730011953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54452398782909159786794165 5104912385897733730011953)
                  ·
                    refine ⟨3828684289423300297508965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104912385897733730011953 3828684289423300297508965)
                    ·
                      refine ⟨717878304266868805782931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3828684289423300297508965 717878304266868805782931)
                      ·
                        rfl

theorem cell23_1398063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_1398063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398063 prefixEnd_1398063 := by exact prefixLift 1398063
  have htrace : WordTrace (prefixWord ++ tailWord_1398063) baseStart_1398063 baseEnd_1398063 := by
    simpa [prefixWord, tailWord_1398063, baseEnd_1398063] using wordTrace_append hprefix tailTrace_1398063
  have hstable : (prefixWord ++ tailWord_1398063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398063).length < 2 ^ (prefixWord ++ tailWord_1398063).sum := by decide
  have hdescent : baseEnd_1398063 < baseStart_1398063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398080 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4]
def baseStart_1398080 : Nat := 118140960795 + 1398080 * 2 ^ 59
def prefixEnd_1398080 : Nat := 4983230072969 + 3 ^ 40 * 1398080 * 2
def baseEnd_1398080 : Nat := 717887033437995239270353

theorem tailTrace_1398080 : CollatzResearch.WordTrace tailWord_1398080 prefixEnd_1398080 717887033437995239270353 := by
  unfold tailWord_1398080
  simp only [CollatzResearch.WordTrace]
  refine ⟨25496083387501203949707847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33994777850001605266277129 25496083387501203949707847)
  ·
    refine ⟨38244125081251805924561771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25496083387501203949707847 38244125081251805924561771)
    ·
      refine ⟨57366187621877708886842657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38244125081251805924561771 57366187621877708886842657)
      ·
        refine ⟨43024640716408281665131993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57366187621877708886842657 43024640716408281665131993)
        ·
          refine ⟨32268480537306211248848995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43024640716408281665131993 32268480537306211248848995)
          ·
            refine ⟨48402720805959316873273493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32268480537306211248848995 48402720805959316873273493)
            ·
              refine ⟨2268877537779342978434695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48402720805959316873273493 2268877537779342978434695)
              ·
                refine ⟨3403316306669014467652043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2268877537779342978434695 3403316306669014467652043)
                ·
                  refine ⟨5104974460003521701478065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3403316306669014467652043 5104974460003521701478065)
                  ·
                    refine ⟨3828730845002641276108549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5104974460003521701478065 3828730845002641276108549)
                    ·
                      refine ⟨717887033437995239270353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3828730845002641276108549 717887033437995239270353)
                      ·
                        rfl

theorem cell23_1398080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_1398080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398080 prefixEnd_1398080 := by exact prefixLift 1398080
  have htrace : WordTrace (prefixWord ++ tailWord_1398080) baseStart_1398080 baseEnd_1398080 := by
    simpa [prefixWord, tailWord_1398080, baseEnd_1398080] using wordTrace_append hprefix tailTrace_1398080
  have hstable : (prefixWord ++ tailWord_1398080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398080).length < 2 ^ (prefixWord ++ tailWord_1398080).sum := by decide
  have hdescent : baseEnd_1398080 < baseStart_1398080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398101 : List Nat := [1, 3, 2, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_1398101 : Nat := 118140960795 + 1398101 * 2 ^ 59
def prefixEnd_1398101 : Nat := 4983230072969 + 3 ^ 40 * 1398101 * 2
def baseEnd_1398101 : Nat := 717897816531739657107757

theorem tailTrace_1398101 : CollatzResearch.WordTrace tailWord_1398101 prefixEnd_1398101 717897816531739657107757 := by
  unfold tailWord_1398101
  simp only [CollatzResearch.WordTrace]
  refine ⟨50992932707926328485930157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33995288471950885657286771 50992932707926328485930157)
  ·
    refine ⟨19122349765472373182223809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50992932707926328485930157 19122349765472373182223809)
    ·
      refine ⟨14341762324104279886667857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19122349765472373182223809 14341762324104279886667857)
      ·
        refine ⟨10756321743078209915000893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14341762324104279886667857 10756321743078209915000893)
        ·
          refine ⟨4033620653654328718125335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10756321743078209915000893 4033620653654328718125335)
          ·
            refine ⟨6050430980481493077188003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4033620653654328718125335 6050430980481493077188003)
            ·
              refine ⟨9075646470722239615782005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6050430980481493077188003 9075646470722239615782005)
              ·
                refine ⟨850841856630209963979563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9075646470722239615782005 850841856630209963979563)
                ·
                  refine ⟨1276262784945314945969345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850841856630209963979563 1276262784945314945969345)
                  ·
                    refine ⟨957197088708986209477009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1276262784945314945969345 957197088708986209477009)
                    ·
                      refine ⟨717897816531739657107757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957197088708986209477009 717897816531739657107757)
                      ·
                        rfl

theorem cell23_1398101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_1398101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398101 prefixEnd_1398101 := by exact prefixLift 1398101
  have htrace : WordTrace (prefixWord ++ tailWord_1398101) baseStart_1398101 baseEnd_1398101 := by
    simpa [prefixWord, tailWord_1398101, baseEnd_1398101] using wordTrace_append hprefix tailTrace_1398101
  have hstable : (prefixWord ++ tailWord_1398101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398101).length < 2 ^ (prefixWord ++ tailWord_1398101).sum := by decide
  have hdescent : baseEnd_1398101 < baseStart_1398101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398117 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_1398117 : Nat := 118140960795 + 1398117 * 2 ^ 59
def prefixEnd_1398117 : Nat := 4983230072969 + 3 ^ 40 * 1398117 * 2
def baseEnd_1398117 : Nat := 717906032222211594507683

theorem tailTrace_1398117 : CollatzResearch.WordTrace tailWord_1398117 prefixEnd_1398117 717906032222211594507683 := by
  unfold tailWord_1398117
  simp only [CollatzResearch.WordTrace]
  refine ⟨50993516275868363218512605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33995677517245575479008403 50993516275868363218512605)
  ·
    refine ⟨19122568603450636206942227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50993516275868363218512605 19122568603450636206942227)
    ·
      refine ⟨28683852905175954310413341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19122568603450636206942227 28683852905175954310413341)
      ·
        refine ⟨10756444839440982866405003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28683852905175954310413341 10756444839440982866405003)
        ·
          refine ⟨16134667259161474299607505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10756444839440982866405003 16134667259161474299607505)
          ·
            refine ⟨12101000444371105724705629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16134667259161474299607505 12101000444371105724705629)
            ·
              refine ⟨4537875166639164646764611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12101000444371105724705629 4537875166639164646764611)
              ·
                refine ⟨6806812749958746970146917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4537875166639164646764611 6806812749958746970146917)
                ·
                  refine ⟨1276277390617265056902547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6806812749958746970146917 1276277390617265056902547)
                  ·
                    refine ⟨1914416085925897585353821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1276277390617265056902547 1914416085925897585353821)
                    ·
                      refine ⟨717906032222211594507683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1914416085925897585353821 717906032222211594507683)
                      ·
                        rfl

theorem cell23_1398117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_1398117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398117 prefixEnd_1398117 := by exact prefixLift 1398117
  have htrace : WordTrace (prefixWord ++ tailWord_1398117) baseStart_1398117 baseEnd_1398117 := by
    simpa [prefixWord, tailWord_1398117, baseEnd_1398117] using wordTrace_append hprefix tailTrace_1398117
  have hstable : (prefixWord ++ tailWord_1398117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398117).length < 2 ^ (prefixWord ++ tailWord_1398117).sum := by decide
  have hdescent : baseEnd_1398117 < baseStart_1398117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398237 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1398237 : Nat := 118140960795 + 1398237 * 2 ^ 59
def prefixEnd_1398237 : Nat := 4983230072969 + 3 ^ 40 * 1398237 * 2
def baseEnd_1398237 : Nat := 717967649900751125007131

theorem tailTrace_1398237 : CollatzResearch.WordTrace tailWord_1398237 prefixEnd_1398237 717967649900751125007131 := by
  unfold tailWord_1398237
  simp only [CollatzResearch.WordTrace]
  refine ⟨50997893035433623712880965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33998595356955749141920643 50997893035433623712880965)
  ·
    refine ⟨9562104944143804446165181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50997893035433623712880965 9562104944143804446165181)
    ·
      refine ⟨3585789354053926667311943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9562104944143804446165181 3585789354053926667311943)
      ·
        refine ⟨5378684031080890000967915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585789354053926667311943 5378684031080890000967915)
        ·
          refine ⟨8068026046621335001451873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5378684031080890000967915 8068026046621335001451873)
          ·
            refine ⟨6051019534966001251088905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8068026046621335001451873 6051019534966001251088905)
            ·
              refine ⟨4538264651224500938316679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6051019534966001251088905 4538264651224500938316679)
              ·
                refine ⟨6807396976836751407475019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4538264651224500938316679 6807396976836751407475019)
                ·
                  refine ⟨10211095465255127111212529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6807396976836751407475019 10211095465255127111212529)
                  ·
                    refine ⟨7658321598941345333409397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10211095465255127111212529 7658321598941345333409397)
                    ·
                      refine ⟨717967649900751125007131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7658321598941345333409397 717967649900751125007131)
                      ·
                        rfl

theorem cell23_1398237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1398237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398237 prefixEnd_1398237 := by exact prefixLift 1398237
  have htrace : WordTrace (prefixWord ++ tailWord_1398237) baseStart_1398237 baseEnd_1398237 := by
    simpa [prefixWord, tailWord_1398237, baseEnd_1398237] using wordTrace_append hprefix tailTrace_1398237
  have hstable : (prefixWord ++ tailWord_1398237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398237).length < 2 ^ (prefixWord ++ tailWord_1398237).sum := by decide
  have hdescent : baseEnd_1398237 < baseStart_1398237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398257 : List Nat := [1, 2, 2, 2, 3, 2, 1, 1, 5, 4]
def baseStart_1398257 : Nat := 118140960795 + 1398257 * 2 ^ 59
def prefixEnd_1398257 : Nat := 4983230072969 + 3 ^ 40 * 1398257 * 2
def baseEnd_1398257 : Nat := 239325973171280348919013

theorem tailTrace_1398257 : CollatzResearch.WordTrace tailWord_1398257 prefixEnd_1398257 239325973171280348919013 := by
  unfold tailWord_1398257
  simp only [CollatzResearch.WordTrace]
  refine ⟨50998622495361167128609025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33999081663574111419072683 50998622495361167128609025)
  ·
    refine ⟨38248966871520875346456769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50998622495361167128609025 38248966871520875346456769)
    ·
      refine ⟨28686725153640656509842577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38248966871520875346456769 28686725153640656509842577)
      ·
        refine ⟨21515043865230492382381933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28686725153640656509842577 21515043865230492382381933)
        ·
          refine ⟨8068141449461434643393225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21515043865230492382381933 8068141449461434643393225)
          ·
            refine ⟨6051106087096075982544919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8068141449461434643393225 6051106087096075982544919)
            ·
              refine ⟨9076659130644113973817379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051106087096075982544919 9076659130644113973817379)
              ·
                refine ⟨13614988695966170960726069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9076659130644113973817379 13614988695966170960726069)
                ·
                  refine ⟨1276405190246828527568069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13614988695966170960726069 1276405190246828527568069)
                  ·
                    refine ⟨239325973171280348919013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1276405190246828527568069 239325973171280348919013)
                    ·
                      rfl

theorem cell23_1398257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_1398257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398257 prefixEnd_1398257 := by exact prefixLift 1398257
  have htrace : WordTrace (prefixWord ++ tailWord_1398257) baseStart_1398257 baseEnd_1398257 := by
    simpa [prefixWord, tailWord_1398257, baseEnd_1398257] using wordTrace_append hprefix tailTrace_1398257
  have hstable : (prefixWord ++ tailWord_1398257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398257).length < 2 ^ (prefixWord ++ tailWord_1398257).sum := by decide
  have hdescent : baseEnd_1398257 < baseStart_1398257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398261 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1398261 : Nat := 118140960795 + 1398261 * 2 ^ 59
def prefixEnd_1398261 : Nat := 4983230072969 + 3 ^ 40 * 1398261 * 2
def baseEnd_1398261 : Nat := 239326657812153010369007

theorem tailTrace_1398261 : CollatzResearch.WordTrace tailWord_1398261 prefixEnd_1398261 239326657812153010369007 := by
  unfold tailWord_1398261
  simp only [CollatzResearch.WordTrace]
  refine ⟨50998768387346675811754637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33999178924897783874503091 50998768387346675811754637)
  ·
    refine ⟨19124538145255003429407989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50998768387346675811754637 19124538145255003429407989)
    ·
      refine ⟨1792925451117656571506999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19124538145255003429407989 1792925451117656571506999)
      ·
        refine ⟨2689388176676484857260499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792925451117656571506999 2689388176676484857260499)
        ·
          refine ⟨4034082265014727285890749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689388176676484857260499 4034082265014727285890749)
          ·
            refine ⟨1512780849380522732209031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4034082265014727285890749 1512780849380522732209031)
            ·
              refine ⟨2269171274070784098313547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512780849380522732209031 2269171274070784098313547)
              ·
                refine ⟨3403756911106176147470321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269171274070784098313547 3403756911106176147470321)
                ·
                  refine ⟨2552817683329632110602741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3403756911106176147470321 2552817683329632110602741)
                  ·
                    refine ⟨239326657812153010369007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2552817683329632110602741 239326657812153010369007)
                    ·
                      rfl

theorem cell23_1398261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1398261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398261 prefixEnd_1398261 := by exact prefixLift 1398261
  have htrace : WordTrace (prefixWord ++ tailWord_1398261) baseStart_1398261 baseEnd_1398261 := by
    simpa [prefixWord, tailWord_1398261, baseEnd_1398261] using wordTrace_append hprefix tailTrace_1398261
  have hstable : (prefixWord ++ tailWord_1398261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398261).length < 2 ^ (prefixWord ++ tailWord_1398261).sum := by decide
  have hdescent : baseEnd_1398261 < baseStart_1398261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398264 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_1398264 : Nat := 118140960795 + 1398264 * 2 ^ 59
def prefixEnd_1398264 : Nat := 4983230072969 + 3 ^ 40 * 1398264 * 2
def baseEnd_1398264 : Nat := 717981513878422519369507

theorem tailTrace_1398264 : CollatzResearch.WordTrace tailWord_1398264 prefixEnd_1398264 717981513878422519369507 := by
  unfold tailWord_1398264
  simp only [CollatzResearch.WordTrace]
  refine ⟨25499438903167903662056923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33999251870890538216075897 25499438903167903662056923)
  ·
    refine ⟨38249158354751855493085385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25499438903167903662056923 38249158354751855493085385)
    ·
      refine ⟨28686868766063891619814039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38249158354751855493085385 28686868766063891619814039)
      ·
        refine ⟨43030303149095837429721059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28686868766063891619814039 43030303149095837429721059)
        ·
          refine ⟨64545454723643756144581589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43030303149095837429721059 64545454723643756144581589)
          ·
            refine ⟨1512784095085400534638631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 64545454723643756144581589 1512784095085400534638631)
            ·
              refine ⟨2269176142628100801957947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512784095085400534638631 2269176142628100801957947)
              ·
                refine ⟨3403764213942151202936921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269176142628100801957947 3403764213942151202936921)
                ·
                  refine ⟨2552823160456613402202691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3403764213942151202936921 2552823160456613402202691)
                  ·
                    refine ⟨3829234740684920103304037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2552823160456613402202691 3829234740684920103304037)
                    ·
                      refine ⟨717981513878422519369507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3829234740684920103304037 717981513878422519369507)
                      ·
                        rfl

theorem cell23_1398264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_1398264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398264 prefixEnd_1398264 := by exact prefixLift 1398264
  have htrace : WordTrace (prefixWord ++ tailWord_1398264) baseStart_1398264 baseEnd_1398264 := by
    simpa [prefixWord, tailWord_1398264, baseEnd_1398264] using wordTrace_append hprefix tailTrace_1398264
  have hstable : (prefixWord ++ tailWord_1398264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398264).length < 2 ^ (prefixWord ++ tailWord_1398264).sum := by decide
  have hdescent : baseEnd_1398264 < baseStart_1398264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398342 : List Nat := [6, 1, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1398342 : Nat := 118140960795 + 1398342 * 2 ^ 59
def prefixEnd_1398342 : Nat := 4983230072969 + 3 ^ 40 * 1398342 * 2
def baseEnd_1398342 : Nat := 239340521789824404731383

theorem tailTrace_1398342 : CollatzResearch.WordTrace tailWord_1398342 prefixEnd_1398342 239340521789824404731383 := by
  unfold tailWord_1398342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593803834376663332670415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34001148466702151096968853 1593803834376663332670415)
  ·
    refine ⟨2390705751564994999005623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1593803834376663332670415 2390705751564994999005623)
    ·
      refine ⟨3586058627347492498508435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2390705751564994999005623 3586058627347492498508435)
      ·
        refine ⟨5379087941021238747762653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586058627347492498508435 5379087941021238747762653)
        ·
          refine ⟨2017157977882964530410995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5379087941021238747762653 2017157977882964530410995)
          ·
            refine ⟨3025736966824446795616493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017157977882964530410995 3025736966824446795616493)
            ·
              refine ⟨1134651362559167548356185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3025736966824446795616493 1134651362559167548356185)
              ·
                refine ⟨850988521919375661267139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134651362559167548356185 850988521919375661267139)
                ·
                  refine ⟨1276482782879063491900709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 850988521919375661267139 1276482782879063491900709)
                  ·
                    refine ⟨239340521789824404731383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1276482782879063491900709 239340521789824404731383)
                    ·
                      rfl

theorem cell23_1398342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1398342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398342 prefixEnd_1398342 := by exact prefixLift 1398342
  have htrace : WordTrace (prefixWord ++ tailWord_1398342) baseStart_1398342 baseEnd_1398342 := by
    simpa [prefixWord, tailWord_1398342, baseEnd_1398342] using wordTrace_append hprefix tailTrace_1398342
  have hstable : (prefixWord ++ tailWord_1398342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398342).length < 2 ^ (prefixWord ++ tailWord_1398342).sum := by decide
  have hdescent : baseEnd_1398342 < baseStart_1398342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398357 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1398357 : Nat := 118140960795 + 1398357 * 2 ^ 59
def prefixEnd_1398357 : Nat := 4983230072969 + 3 ^ 40 * 1398357 * 2
def baseEnd_1398357 : Nat := 718029267579290655506579

theorem tailTrace_1398357 : CollatzResearch.WordTrace tailWord_1398357 prefixEnd_1398357 718029267579290655506579 := by
  unfold tailWord_1398357
  simp only [CollatzResearch.WordTrace]
  refine ⟨51002269794998884207249325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34001513196665922804832883 51002269794998884207249325)
  ·
    refine ⟨19125851173124581577718497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51002269794998884207249325 19125851173124581577718497)
    ·
      refine ⟨14344388379843436183288873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19125851173124581577718497 14344388379843436183288873)
      ·
        refine ⟨10758291284882577137466655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14344388379843436183288873 10758291284882577137466655)
        ·
          refine ⟨16137436927323865706199983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758291284882577137466655 16137436927323865706199983)
          ·
            refine ⟨24206155390985798559299975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16137436927323865706199983 24206155390985798559299975)
            ·
              refine ⟨36309233086478697838949963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24206155390985798559299975 36309233086478697838949963)
              ·
                refine ⟨54463849629718046758424945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36309233086478697838949963 54463849629718046758424945)
                ·
                  refine ⟨40847887222288535068818709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54463849629718046758424945 40847887222288535068818709)
                  ·
                    refine ⟨1914744713544775081350877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40847887222288535068818709 1914744713544775081350877)
                    ·
                      refine ⟨718029267579290655506579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1914744713544775081350877 718029267579290655506579)
                      ·
                        rfl

theorem cell23_1398357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1398357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398357 prefixEnd_1398357 := by exact prefixLift 1398357
  have htrace : WordTrace (prefixWord ++ tailWord_1398357) baseStart_1398357 baseEnd_1398357 := by
    simpa [prefixWord, tailWord_1398357, baseEnd_1398357] using wordTrace_append hprefix tailTrace_1398357
  have hstable : (prefixWord ++ tailWord_1398357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398357).length < 2 ^ (prefixWord ++ tailWord_1398357).sum := by decide
  have hdescent : baseEnd_1398357 < baseStart_1398357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398371 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1398371 : Nat := 118140960795 + 1398371 * 2 ^ 59
def prefixEnd_1398371 : Nat := 4983230072969 + 3 ^ 40 * 1398371 * 2
def baseEnd_1398371 : Nat := 718036456308453600731515

theorem tailTrace_1398371 : CollatzResearch.WordTrace tailWord_1398371 prefixEnd_1398371 718036456308453600731515 := by
  unfold tailWord_1398371
  simp only [CollatzResearch.WordTrace]
  refine ⟨51002780416948164598258967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34001853611298776398839311 51002780416948164598258967)
  ·
    refine ⟨76504170625422246897388451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51002780416948164598258967 76504170625422246897388451)
    ·
      refine ⟨114756255938133370346082677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76504170625422246897388451 114756255938133370346082677)
      ·
        refine ⟨10758398994200003469945251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114756255938133370346082677 10758398994200003469945251)
        ·
          refine ⟨16137598491300005204917877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758398994200003469945251 16137598491300005204917877)
          ·
            refine ⟨1512899858559375487961051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16137598491300005204917877 1512899858559375487961051)
            ·
              refine ⟨2269349787839063231941577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512899858559375487961051 2269349787839063231941577)
              ·
                refine ⟨1702012340879297423956183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2269349787839063231941577 1702012340879297423956183)
                ·
                  refine ⟨2553018511318946135934275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702012340879297423956183 2553018511318946135934275)
                  ·
                    refine ⟨3829527766978419203901413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553018511318946135934275 3829527766978419203901413)
                    ·
                      refine ⟨718036456308453600731515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3829527766978419203901413 718036456308453600731515)
                      ·
                        rfl

theorem cell23_1398371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1398371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398371 prefixEnd_1398371 := by exact prefixLift 1398371
  have htrace : WordTrace (prefixWord ++ tailWord_1398371) baseStart_1398371 baseEnd_1398371 := by
    simpa [prefixWord, tailWord_1398371, baseEnd_1398371] using wordTrace_append hprefix tailTrace_1398371
  have hstable : (prefixWord ++ tailWord_1398371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398371).length < 2 ^ (prefixWord ++ tailWord_1398371).sum := by decide
  have hdescent : baseEnd_1398371 < baseStart_1398371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398384 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_1398384 : Nat := 118140960795 + 1398384 * 2 ^ 59
def prefixEnd_1398384 : Nat := 4983230072969 + 3 ^ 40 * 1398384 * 2
def baseEnd_1398384 : Nat := 718043131556962049868955

theorem tailTrace_1398384 : CollatzResearch.WordTrace tailWord_1398384 prefixEnd_1398384 718043131556962049868955 := by
  unfold tailWord_1398384
  simp only [CollatzResearch.WordTrace]
  refine ⟨25501627282950533909241103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34002169710600711878988137 25501627282950533909241103)
  ·
    refine ⟨38252440924425800863861655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25501627282950533909241103 38252440924425800863861655)
    ·
      refine ⟨57378661386638701295792483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38252440924425800863861655 57378661386638701295792483)
      ·
        refine ⟨86067992079958051943688725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57378661386638701295792483 86067992079958051943688725)
        ·
          refine ⟨4034437128748033684860409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86067992079958051943688725 4034437128748033684860409)
          ·
            refine ⟨3025827846561025263645307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4034437128748033684860409 3025827846561025263645307)
            ·
              refine ⟨4538741769841537895467961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025827846561025263645307 4538741769841537895467961)
              ·
                refine ⟨3404056327381153421600971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538741769841537895467961 3404056327381153421600971)
                ·
                  refine ⟨5106084491071730132401457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3404056327381153421600971 5106084491071730132401457)
                  ·
                    refine ⟨3829563368303797599301093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5106084491071730132401457 3829563368303797599301093)
                    ·
                      refine ⟨718043131556962049868955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3829563368303797599301093 718043131556962049868955)
                      ·
                        rfl

theorem cell23_1398384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_1398384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398384 prefixEnd_1398384 := by exact prefixLift 1398384
  have htrace : WordTrace (prefixWord ++ tailWord_1398384) baseStart_1398384 baseEnd_1398384 := by
    simpa [prefixWord, tailWord_1398384, baseEnd_1398384] using wordTrace_append hprefix tailTrace_1398384
  have hstable : (prefixWord ++ tailWord_1398384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398384).length < 2 ^ (prefixWord ++ tailWord_1398384).sum := by decide
  have hdescent : baseEnd_1398384 < baseStart_1398384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398407 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 2, 7]
def baseStart_1398407 : Nat := 118140960795 + 1398407 * 2 ^ 59
def prefixEnd_1398407 : Nat := 4983230072969 + 3 ^ 40 * 1398407 * 2
def baseEnd_1398407 : Nat := 239351647204005153293783

theorem tailTrace_1398407 : CollatzResearch.WordTrace tailWord_1398407 prefixEnd_1398407 239351647204005153293783 := by
  unfold tailWord_1398407
  simp only [CollatzResearch.WordTrace]
  refine ⟨51004093444817742746569475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34002728963211828497712983 51004093444817742746569475)
  ·
    refine ⟨76506140167226614119854213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51004093444817742746569475 76506140167226614119854213)
    ·
      refine ⟨14344901281354990147472665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76506140167226614119854213 14344901281354990147472665)
      ·
        refine ⟨10758675961016242610604499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14344901281354990147472665 10758675961016242610604499)
        ·
          refine ⟨16138013941524363915906749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10758675961016242610604499 16138013941524363915906749)
          ·
            refine ⟨6051755228071636468465031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16138013941524363915906749 6051755228071636468465031)
            ·
              refine ⟨9077632842107454702697547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6051755228071636468465031 9077632842107454702697547)
              ·
                refine ⟨13616449263161182054046321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9077632842107454702697547 13616449263161182054046321)
                ·
                  refine ⟨10212336947370886540534741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13616449263161182054046321 10212336947370886540534741)
                  ·
                    refine ⟨239351647204005153293783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10212336947370886540534741 239351647204005153293783)
                    ·
                      rfl

theorem cell23_1398407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_1398407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398407 prefixEnd_1398407 := by exact prefixLift 1398407
  have htrace : WordTrace (prefixWord ++ tailWord_1398407) baseStart_1398407 baseEnd_1398407 := by
    simpa [prefixWord, tailWord_1398407, baseEnd_1398407] using wordTrace_append hprefix tailTrace_1398407
  have hstable : (prefixWord ++ tailWord_1398407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398407).length < 2 ^ (prefixWord ++ tailWord_1398407).sum := by decide
  have hdescent : baseEnd_1398407 < baseStart_1398407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398447 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_1398447 : Nat := 118140960795 + 1398447 * 2 ^ 59
def prefixEnd_1398447 : Nat := 4983230072969 + 3 ^ 40 * 1398447 * 2
def baseEnd_1398447 : Nat := 718075480838195303381165

theorem tailTrace_1398447 : CollatzResearch.WordTrace tailWord_1398447 prefixEnd_1398447 718075480838195303381165 := by
  unfold tailWord_1398447
  simp only [CollatzResearch.WordTrace]
  refine ⟨51005552364672829578025595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34003701576448553052017063 51005552364672829578025595)
  ·
    refine ⟨76508328547009244367038393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51005552364672829578025595 76508328547009244367038393)
    ·
      refine ⟨57381246410256933275278795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76508328547009244367038393 57381246410256933275278795)
      ·
        refine ⟨86071869615385399912918193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57381246410256933275278795 86071869615385399912918193)
        ·
          refine ⟨64553902211539049934688645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86071869615385399912918193 64553902211539049934688645)
          ·
            refine ⟨12103856664663571862754121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64553902211539049934688645 12103856664663571862754121)
            ·
              refine ⟨9077892498497678897065591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12103856664663571862754121 9077892498497678897065591)
              ·
                refine ⟨13616838747746518345598387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9077892498497678897065591 13616838747746518345598387)
                ·
                  refine ⟨20425258121619777518397581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13616838747746518345598387 20425258121619777518397581)
                  ·
                    refine ⟨7659471795607416569399093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20425258121619777518397581 7659471795607416569399093)
                    ·
                      refine ⟨718075480838195303381165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7659471795607416569399093 718075480838195303381165)
                      ·
                        rfl

theorem cell23_1398447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_1398447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398447 prefixEnd_1398447 := by exact prefixLift 1398447
  have htrace : WordTrace (prefixWord ++ tailWord_1398447) baseStart_1398447 baseEnd_1398447 := by
    simpa [prefixWord, tailWord_1398447, baseEnd_1398447] using wordTrace_append hprefix tailTrace_1398447
  have hstable : (prefixWord ++ tailWord_1398447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398447).length < 2 ^ (prefixWord ++ tailWord_1398447).sum := by decide
  have hdescent : baseEnd_1398447 < baseStart_1398447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398448 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 1, 3, 2]
def baseStart_1398448 : Nat := 118140960795 + 1398448 * 2 ^ 59
def prefixEnd_1398448 : Nat := 4983230072969 + 3 ^ 40 * 1398448 * 2
def baseEnd_1398448 : Nat := 718075994318849799468661

theorem tailTrace_1398448 : CollatzResearch.WordTrace tailWord_1398448 prefixEnd_1398448 718075994318849799468661 := by
  unfold tailWord_1398448
  simp only [CollatzResearch.WordTrace]
  refine ⟨25502794418834603374405999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34003725891779471165874665 25502794418834603374405999)
  ·
    refine ⟨38254191628251905061608999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25502794418834603374405999 38254191628251905061608999)
    ·
      refine ⟨57381287442377857592413499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38254191628251905061608999 57381287442377857592413499)
      ·
        refine ⟨86071931163566786388620249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57381287442377857592413499 86071931163566786388620249)
        ·
          refine ⟨64553948372675089791465187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86071931163566786388620249 64553948372675089791465187)
          ·
            refine ⟨96830922559012634687197781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64553948372675089791465187 96830922559012634687197781)
            ·
              refine ⟨1134737373738429312740599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 96830922559012634687197781 1134737373738429312740599)
              ·
                refine ⟨1702106060607643969110899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134737373738429312740599 1702106060607643969110899)
                ·
                  refine ⟨2553159090911465953666349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1702106060607643969110899 2553159090911465953666349)
                  ·
                    refine ⟨957434659091799732624881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2553159090911465953666349 957434659091799732624881)
                    ·
                      refine ⟨718075994318849799468661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957434659091799732624881 718075994318849799468661)
                      ·
                        rfl

theorem cell23_1398448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 3, 2].length) (baseStart_1398448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398448 prefixEnd_1398448 := by exact prefixLift 1398448
  have htrace : WordTrace (prefixWord ++ tailWord_1398448) baseStart_1398448 baseEnd_1398448 := by
    simpa [prefixWord, tailWord_1398448, baseEnd_1398448] using wordTrace_append hprefix tailTrace_1398448
  have hstable : (prefixWord ++ tailWord_1398448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398448).length < 2 ^ (prefixWord ++ tailWord_1398448).sum := by decide
  have hdescent : baseEnd_1398448 < baseStart_1398448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398524 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1398524 : Nat := 118140960795 + 1398524 * 2 ^ 59
def prefixEnd_1398524 : Nat := 4983230072969 + 3 ^ 40 * 1398524 * 2
def baseEnd_1398524 : Nat := 718115018848591502118311

theorem tailTrace_1398524 : CollatzResearch.WordTrace tailWord_1398524 prefixEnd_1398524 718115018848591502118311 := by
  unfold tailWord_1398524
  simp only [CollatzResearch.WordTrace]
  refine ⟨25504180392696935864289313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34005573856929247819052417 25504180392696935864289313)
  ·
    refine ⟨19128135294522701898216985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25504180392696935864289313 19128135294522701898216985)
    ·
      refine ⟨14346101470892026423662739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19128135294522701898216985 14346101470892026423662739)
      ·
        refine ⟨21519152206338039635494109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14346101470892026423662739 21519152206338039635494109)
        ·
          refine ⟨8069682077376764863310291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21519152206338039635494109 8069682077376764863310291)
          ·
            refine ⟨12104523116065147294965437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8069682077376764863310291 12104523116065147294965437)
            ·
              refine ⟨4539196168524430235612039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12104523116065147294965437 4539196168524430235612039)
              ·
                refine ⟨6808794252786645353418059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4539196168524430235612039 6808794252786645353418059)
                ·
                  refine ⟨10213191379179968030127089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6808794252786645353418059 10213191379179968030127089)
                  ·
                    refine ⟨7659893534384976022595317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10213191379179968030127089 7659893534384976022595317)
                    ·
                      refine ⟨718115018848591502118311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7659893534384976022595317 718115018848591502118311)
                      ·
                        rfl

theorem cell23_1398524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1398524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398524 prefixEnd_1398524 := by exact prefixLift 1398524
  have htrace : WordTrace (prefixWord ++ tailWord_1398524) baseStart_1398524 baseEnd_1398524 := by
    simpa [prefixWord, tailWord_1398524, baseEnd_1398524] using wordTrace_append hprefix tailTrace_1398524
  have hstable : (prefixWord ++ tailWord_1398524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398524).length < 2 ^ (prefixWord ++ tailWord_1398524).sum := by decide
  have hdescent : baseEnd_1398524 < baseStart_1398524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398551 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1398551 : Nat := 118140960795 + 1398551 * 2 ^ 59
def prefixEnd_1398551 : Nat := 4983230072969 + 3 ^ 40 * 1398551 * 2
def baseEnd_1398551 : Nat := 718128882826262896480687

theorem tailTrace_1398551 : CollatzResearch.WordTrace tailWord_1398551 prefixEnd_1398551 718128882826262896480687 := by
  unfold tailWord_1398551
  simp only [CollatzResearch.WordTrace]
  refine ⟨51009345556296055339811507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34006230370864036893207671 51009345556296055339811507)
  ·
    refine ⟨76514018334444083009717261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51009345556296055339811507 76514018334444083009717261)
    ·
      refine ⟨28692756875416531128643973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76514018334444083009717261 28692756875416531128643973)
      ·
        refine ⟨5379891914140599586620745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28692756875416531128643973 5379891914140599586620745)
        ·
          refine ⟨4034918935605449689965559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5379891914140599586620745 4034918935605449689965559)
          ·
            refine ⟨6052378403408174534948339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4034918935605449689965559 6052378403408174534948339)
            ·
              refine ⟨9078567605112261802422509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6052378403408174534948339 9078567605112261802422509)
              ·
                refine ⟨3404462851917098175908441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9078567605112261802422509 3404462851917098175908441)
                ·
                  refine ⟨2553347138937823631931331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404462851917098175908441 2553347138937823631931331)
                  ·
                    refine ⟨3830020708406735447896997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2553347138937823631931331 3830020708406735447896997)
                    ·
                      refine ⟨718128882826262896480687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3830020708406735447896997 718128882826262896480687)
                      ·
                        rfl

theorem cell23_1398551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1398551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398551 prefixEnd_1398551 := by exact prefixLift 1398551
  have htrace : WordTrace (prefixWord ++ tailWord_1398551) baseStart_1398551 baseEnd_1398551 := by
    simpa [prefixWord, tailWord_1398551, baseEnd_1398551] using wordTrace_append hprefix tailTrace_1398551
  have hstable : (prefixWord ++ tailWord_1398551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398551).length < 2 ^ (prefixWord ++ tailWord_1398551).sum := by decide
  have hdescent : baseEnd_1398551 < baseStart_1398551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398585 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1398585 : Nat := 118140960795 + 1398585 * 2 ^ 59
def prefixEnd_1398585 : Nat := 4983230072969 + 3 ^ 40 * 1398585 * 2
def baseEnd_1398585 : Nat := 718146341168515763455531

theorem tailTrace_1398585 : CollatzResearch.WordTrace tailWord_1398585 prefixEnd_1398585 718146341168515763455531 := by
  unfold tailWord_1398585
  simp only [CollatzResearch.WordTrace]
  refine ⟨51010585638172879146549209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34007057092115252764366139 51010585638172879146549209)
  ·
    refine ⟨38257939228629659359911907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51010585638172879146549209 38257939228629659359911907)
    ·
      refine ⟨57386908842944489039867861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38257939228629659359911907 57386908842944489039867861)
      ·
        refine ⟨1345005676006511461871903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 57386908842944489039867861 1345005676006511461871903)
        ·
          refine ⟨2017508514009767192807855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345005676006511461871903 2017508514009767192807855)
          ·
            refine ⟨3026262771014650789211783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017508514009767192807855 3026262771014650789211783)
            ·
              refine ⟨4539394156521976183817675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3026262771014650789211783 4539394156521976183817675)
              ·
                refine ⟨6809091234782964275726513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4539394156521976183817675 6809091234782964275726513)
                ·
                  refine ⟨5106818426087223206794885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6809091234782964275726513 5106818426087223206794885)
                  ·
                    refine ⟨957528454891354351274041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5106818426087223206794885 957528454891354351274041)
                    ·
                      refine ⟨718146341168515763455531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957528454891354351274041 718146341168515763455531)
                      ·
                        rfl

theorem cell23_1398585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1398585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398585 prefixEnd_1398585 := by exact prefixLift 1398585
  have htrace : WordTrace (prefixWord ++ tailWord_1398585) baseStart_1398585 baseEnd_1398585 := by
    simpa [prefixWord, tailWord_1398585, baseEnd_1398585] using wordTrace_append hprefix tailTrace_1398585
  have hstable : (prefixWord ++ tailWord_1398585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398585).length < 2 ^ (prefixWord ++ tailWord_1398585).sum := by decide
  have hdescent : baseEnd_1398585 < baseStart_1398585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398605 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1398605 : Nat := 118140960795 + 1398605 * 2 ^ 59
def prefixEnd_1398605 : Nat := 4983230072969 + 3 ^ 40 * 1398605 * 2
def baseEnd_1398605 : Nat := 718156610781605685205439

theorem tailTrace_1398605 : CollatzResearch.WordTrace tailWord_1398605 prefixEnd_1398605 718156610781605685205439 := by
  unfold tailWord_1398605
  simp only [CollatzResearch.WordTrace]
  refine ⟨51011315098100422562277269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34007543398733615041518179 51011315098100422562277269)
  ·
    refine ⟨2391155395223457307606747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 51011315098100422562277269 2391155395223457307606747)
    ·
      refine ⟨3586733092835185961410121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391155395223457307606747 3586733092835185961410121)
      ·
        refine ⟨2690049819626389471057591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3586733092835185961410121 2690049819626389471057591)
        ·
          refine ⟨4035074729439584206586387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690049819626389471057591 4035074729439584206586387)
          ·
            refine ⟨6052612094159376309879581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035074729439584206586387 6052612094159376309879581)
            ·
              refine ⟨2269729535309766116204843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6052612094159376309879581 2269729535309766116204843)
              ·
                refine ⟨3404594302964649174307265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269729535309766116204843 3404594302964649174307265)
                ·
                  refine ⟨2553445727223486880730449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3404594302964649174307265 2553445727223486880730449)
                  ·
                    refine ⟨1915084295417615160547837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2553445727223486880730449 1915084295417615160547837)
                    ·
                      refine ⟨718156610781605685205439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1915084295417615160547837 718156610781605685205439)
                      ·
                        rfl

theorem cell23_1398605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1398605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398605 prefixEnd_1398605 := by exact prefixLift 1398605
  have htrace : WordTrace (prefixWord ++ tailWord_1398605) baseStart_1398605 baseEnd_1398605 := by
    simpa [prefixWord, tailWord_1398605, baseEnd_1398605] using wordTrace_append hprefix tailTrace_1398605
  have hstable : (prefixWord ++ tailWord_1398605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398605).length < 2 ^ (prefixWord ++ tailWord_1398605).sum := by decide
  have hdescent : baseEnd_1398605 < baseStart_1398605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398686 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1398686 : Nat := 118140960795 + 1398686 * 2 ^ 59
def prefixEnd_1398686 : Nat := 4983230072969 + 3 ^ 40 * 1398686 * 2
def baseEnd_1398686 : Nat := 718198202714619868292567

theorem tailTrace_1398686 : CollatzResearch.WordTrace tailWord_1398686 prefixEnd_1398686 718198202714619868292567 := by
  unfold tailWord_1398686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376783676350871674496989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34009512940537982263983941 6376783676350871674496989)
  ·
    refine ⟨2391293878631576877936371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6376783676350871674496989 2391293878631576877936371)
    ·
      refine ⟨3586940817947365316904557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391293878631576877936371 3586940817947365316904557)
      ·
        refine ⟨1345102806730261993839209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3586940817947365316904557 1345102806730261993839209)
        ·
          refine ⟨1008827105047696495379407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345102806730261993839209 1008827105047696495379407)
          ·
            refine ⟨1513240657571544743069111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008827105047696495379407 1513240657571544743069111)
            ·
              refine ⟨2269860986357317114603667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513240657571544743069111 2269860986357317114603667)
              ·
                refine ⟨3404791479535975671905501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269860986357317114603667 3404791479535975671905501)
                ·
                  refine ⟨1276796804825990876964563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3404791479535975671905501 1276796804825990876964563)
                  ·
                    refine ⟨1915195207238986315446845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1276796804825990876964563 1915195207238986315446845)
                    ·
                      refine ⟨718198202714619868292567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1915195207238986315446845 718198202714619868292567)
                      ·
                        rfl

theorem cell23_1398686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1398686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398686 prefixEnd_1398686 := by exact prefixLift 1398686
  have htrace : WordTrace (prefixWord ++ tailWord_1398686) baseStart_1398686 baseEnd_1398686 := by
    simpa [prefixWord, tailWord_1398686, baseEnd_1398686] using wordTrace_append hprefix tailTrace_1398686
  have hstable : (prefixWord ++ tailWord_1398686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398686).length < 2 ^ (prefixWord ++ tailWord_1398686).sum := by decide
  have hdescent : baseEnd_1398686 < baseStart_1398686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398692 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 3, 2, 2]
def baseStart_1398692 : Nat := 118140960795 + 1398692 * 2 ^ 59
def prefixEnd_1398692 : Nat := 4983230072969 + 3 ^ 40 * 1398692 * 2
def baseEnd_1398692 : Nat := 718201283598546844817539

theorem tailTrace_1398692 : CollatzResearch.WordTrace tailWord_1398692 prefixEnd_1398692 718201283598546844817539 := by
  unfold tailWord_1398692
  simp only [CollatzResearch.WordTrace]
  refine ⟨25507244124392618210347165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34009658832523490947129553 25507244124392618210347165)
  ·
    refine ⟨9565216546647231828880187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25507244124392618210347165 9565216546647231828880187)
    ·
      refine ⟨14347824819970847743320281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9565216546647231828880187 14347824819970847743320281)
      ·
        refine ⟨10760868614978135807490211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14347824819970847743320281 10760868614978135807490211)
        ·
          refine ⟨16141302922467203711235317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10760868614978135807490211 16141302922467203711235317)
          ·
            refine ⟨1513247148981300347928311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16141302922467203711235317 1513247148981300347928311)
            ·
              refine ⟨2269870723471950521892467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513247148981300347928311 2269870723471950521892467)
              ·
                refine ⟨3404806085207925782838701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2269870723471950521892467 3404806085207925782838701)
                ·
                  refine ⟨1276802281952972168564513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3404806085207925782838701 1276802281952972168564513)
                  ·
                    refine ⟨957601711464729126423385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1276802281952972168564513 957601711464729126423385)
                    ·
                      refine ⟨718201283598546844817539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957601711464729126423385 718201283598546844817539)
                      ·
                        rfl

theorem cell23_1398692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_1398692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398692 prefixEnd_1398692 := by exact prefixLift 1398692
  have htrace : WordTrace (prefixWord ++ tailWord_1398692) baseStart_1398692 baseEnd_1398692 := by
    simpa [prefixWord, tailWord_1398692, baseEnd_1398692] using wordTrace_append hprefix tailTrace_1398692
  have hstable : (prefixWord ++ tailWord_1398692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398692).length < 2 ^ (prefixWord ++ tailWord_1398692).sum := by decide
  have hdescent : baseEnd_1398692 < baseStart_1398692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398782 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_1398782 : Nat := 118140960795 + 1398782 * 2 ^ 59
def prefixEnd_1398782 : Nat := 4983230072969 + 3 ^ 40 * 1398782 * 2
def baseEnd_1398782 : Nat := 718247496857451492692125

theorem tailTrace_1398782 : CollatzResearch.WordTrace tailWord_1398782 prefixEnd_1398782 718247496857451492692125 := by
  unfold tailWord_1398782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377221352307397723933825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34011847212306121194313733 6377221352307397723933825)
  ·
    refine ⟨4782916014230548292950369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6377221352307397723933825 4782916014230548292950369)
    ·
      refine ⟨3587187010672911219712777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4782916014230548292950369 3587187010672911219712777)
      ·
        refine ⟨2690390258004683414784583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3587187010672911219712777 2690390258004683414784583)
        ·
          refine ⟨4035585387007025122176875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690390258004683414784583 4035585387007025122176875)
          ·
            refine ⟨6053378080510537683265313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035585387007025122176875 6053378080510537683265313)
            ·
              refine ⟨4540033560382903262448985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6053378080510537683265313 4540033560382903262448985)
              ·
                refine ⟨3405025170287177446836739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4540033560382903262448985 3405025170287177446836739)
                ·
                  refine ⟨5107537755430766170255109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3405025170287177446836739 5107537755430766170255109)
                  ·
                    refine ⟨957663329143268656922833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5107537755430766170255109 957663329143268656922833)
                    ·
                      refine ⟨718247496857451492692125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957663329143268656922833 718247496857451492692125)
                      ·
                        rfl

theorem cell23_1398782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_1398782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398782 prefixEnd_1398782 := by exact prefixLift 1398782
  have htrace : WordTrace (prefixWord ++ tailWord_1398782) baseStart_1398782 baseEnd_1398782 := by
    simpa [prefixWord, tailWord_1398782, baseEnd_1398782] using wordTrace_append hprefix tailTrace_1398782
  have hstable : (prefixWord ++ tailWord_1398782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398782).length < 2 ^ (prefixWord ++ tailWord_1398782).sum := by decide
  have hdescent : baseEnd_1398782 < baseStart_1398782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398798 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1398798 : Nat := 118140960795 + 1398798 * 2 ^ 59
def prefixEnd_1398798 : Nat := 4983230072969 + 3 ^ 40 * 1398798 * 2
def baseEnd_1398798 : Nat := 718255712547923430092051

theorem tailTrace_1398798 : CollatzResearch.WordTrace tailWord_1398798 prefixEnd_1398798 718255712547923430092051 := by
  unfold tailWord_1398798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377294298300152065506631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34012236257600811016035365 6377294298300152065506631)
  ·
    refine ⟨9565941447450228098259947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6377294298300152065506631 9565941447450228098259947)
    ·
      refine ⟨14348912171175342147389921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9565941447450228098259947 14348912171175342147389921)
      ·
        refine ⟨10761684128381506610542441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14348912171175342147389921 10761684128381506610542441)
        ·
          refine ⟨8071263096286129957906831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10761684128381506610542441 8071263096286129957906831)
          ·
            refine ⟨12106894644429194936860247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8071263096286129957906831 12106894644429194936860247)
            ·
              refine ⟨18160341966643792405290371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12106894644429194936860247 18160341966643792405290371)
              ·
                refine ⟨27240512949965688607935557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18160341966643792405290371 27240512949965688607935557)
                ·
                  refine ⟨5107596178118566613987917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27240512949965688607935557 5107596178118566613987917)
                  ·
                    refine ⟨1915348566794462480245469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5107596178118566613987917 1915348566794462480245469)
                    ·
                      refine ⟨718255712547923430092051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1915348566794462480245469 718255712547923430092051)
                      ·
                        rfl

theorem cell23_1398798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1398798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398798 prefixEnd_1398798 := by exact prefixLift 1398798
  have htrace : WordTrace (prefixWord ++ tailWord_1398798) baseStart_1398798 baseEnd_1398798 := by
    simpa [prefixWord, tailWord_1398798, baseEnd_1398798] using wordTrace_append hprefix tailTrace_1398798
  have hstable : (prefixWord ++ tailWord_1398798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398798).length < 2 ^ (prefixWord ++ tailWord_1398798).sum := by decide
  have hdescent : baseEnd_1398798 < baseStart_1398798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398851 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6]
def baseStart_1398851 : Nat := 118140960795 + 1398851 * 2 ^ 59
def prefixEnd_1398851 : Nat := 4983230072969 + 3 ^ 40 * 1398851 * 2
def baseEnd_1398851 : Nat := 718282927022611722729307

theorem tailTrace_1398851 : CollatzResearch.WordTrace tailWord_1398851 prefixEnd_1398851 718282927022611722729307 := by
  unfold tailWord_1398851
  simp only [CollatzResearch.WordTrace]
  refine ⟨51020287455209206575732407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34013524970139471050488271 51020287455209206575732407)
  ·
    refine ⟨76530431182813809863598611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51020287455209206575732407 76530431182813809863598611)
    ·
      refine ⟨114795646774220714795397917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76530431182813809863598611 114795646774220714795397917)
      ·
        refine ⟨43048367540332768048274219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114795646774220714795397917 43048367540332768048274219)
        ·
          refine ⟨64572551310499152072411329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43048367540332768048274219 64572551310499152072411329)
          ·
            refine ⟨48429413482874364054308497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64572551310499152072411329 48429413482874364054308497)
            ·
              refine ⟨36322060112155773040731373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48429413482874364054308497 36322060112155773040731373)
              ·
                refine ⟨13620772542058414890274265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36322060112155773040731373 13620772542058414890274265)
                ·
                  refine ⟨10215579406543811167705699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13620772542058414890274265 10215579406543811167705699)
                  ·
                    refine ⟨15323369109815716751558549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10215579406543811167705699 15323369109815716751558549)
                    ·
                      refine ⟨718282927022611722729307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15323369109815716751558549 718282927022611722729307)
                      ·
                        rfl

theorem cell23_1398851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_1398851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398851 prefixEnd_1398851 := by exact prefixLift 1398851
  have htrace : WordTrace (prefixWord ++ tailWord_1398851) baseStart_1398851 baseEnd_1398851 := by
    simpa [prefixWord, tailWord_1398851, baseEnd_1398851] using wordTrace_append hprefix tailTrace_1398851
  have hstable : (prefixWord ++ tailWord_1398851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398851).length < 2 ^ (prefixWord ++ tailWord_1398851).sum := by decide
  have hdescent : baseEnd_1398851 < baseStart_1398851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398928 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_1398928 : Nat := 118140960795 + 1398928 * 2 ^ 59
def prefixEnd_1398928 : Nat := 4983230072969 + 3 ^ 40 * 1398928 * 2
def baseEnd_1398928 : Nat := 718322465033007921466453

theorem tailTrace_1398928 : CollatzResearch.WordTrace tailWord_1398928 prefixEnd_1398928 718322465033007921466453 := by
  unfold tailWord_1398928
  simp only [CollatzResearch.WordTrace]
  refine ⟨25511547937965124363142719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34015397250620165817523625 25511547937965124363142719)
  ·
    refine ⟨38267321906947686544714079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25511547937965124363142719 38267321906947686544714079)
    ·
      refine ⟨57400982860421529817071119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38267321906947686544714079 57400982860421529817071119)
      ·
        refine ⟨86101474290632294725606679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57400982860421529817071119 86101474290632294725606679)
        ·
          refine ⟨129152211435948442088410019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86101474290632294725606679 129152211435948442088410019)
          ·
            refine ⟨193728317153922663132615029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129152211435948442088410019 193728317153922663132615029)
            ·
              refine ⟨18162029733180249668682659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193728317153922663132615029 18162029733180249668682659)
              ·
                refine ⟨27243044599770374503023989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18162029733180249668682659 27243044599770374503023989)
                ·
                  refine ⟨2554035431228472609658499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27243044599770374503023989 2554035431228472609658499)
                  ·
                    refine ⟨3831053146842708914487749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2554035431228472609658499 3831053146842708914487749)
                    ·
                      refine ⟨718322465033007921466453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3831053146842708914487749 718322465033007921466453)
                      ·
                        rfl

theorem cell23_1398928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_1398928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398928 prefixEnd_1398928 := by exact prefixLift 1398928
  have htrace : WordTrace (prefixWord ++ tailWord_1398928) baseStart_1398928 baseEnd_1398928 := by
    simpa [prefixWord, tailWord_1398928, baseEnd_1398928] using wordTrace_append hprefix tailTrace_1398928
  have hstable : (prefixWord ++ tailWord_1398928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398928).length < 2 ^ (prefixWord ++ tailWord_1398928).sum := by decide
  have hdescent : baseEnd_1398928 < baseStart_1398928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398945 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1398945 : Nat := 118140960795 + 1398945 * 2 ^ 59
def prefixEnd_1398945 : Nat := 4983230072969 + 3 ^ 40 * 1398945 * 2
def baseEnd_1398945 : Nat := 718331194204134354953875

theorem tailTrace_1398945 : CollatzResearch.WordTrace tailWord_1398945 prefixEnd_1398945 718331194204134354953875 := by
  unfold tailWord_1398945
  simp only [CollatzResearch.WordTrace]
  refine ⟨51023715916868660629654289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34015810611245773753102859 51023715916868660629654289)
  ·
    refine ⟨38267786937651495472240717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51023715916868660629654289 38267786937651495472240717)
    ·
      refine ⟨14350420101619310802090269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38267786937651495472240717 14350420101619310802090269)
      ·
        refine ⟨5381407538107241550783851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14350420101619310802090269 5381407538107241550783851)
        ·
          refine ⟨8072111307160862326175777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5381407538107241550783851 8072111307160862326175777)
          ·
            refine ⟨6054083480370646744631833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8072111307160862326175777 6054083480370646744631833)
            ·
              refine ⟨4540562610277985058473875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6054083480370646744631833 4540562610277985058473875)
              ·
                refine ⟨6810843915416977587710813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540562610277985058473875 6810843915416977587710813)
                ·
                  refine ⟨2554066468281366595391555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6810843915416977587710813 2554066468281366595391555)
                  ·
                    refine ⟨3831099702422049893087333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2554066468281366595391555 3831099702422049893087333)
                    ·
                      refine ⟨718331194204134354953875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3831099702422049893087333 718331194204134354953875)
                      ·
                        rfl

theorem cell23_1398945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1398945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398945 prefixEnd_1398945 := by exact prefixLift 1398945
  have htrace : WordTrace (prefixWord ++ tailWord_1398945) baseStart_1398945 baseEnd_1398945 := by
    simpa [prefixWord, tailWord_1398945, baseEnd_1398945] using wordTrace_append hprefix tailTrace_1398945
  have hstable : (prefixWord ++ tailWord_1398945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398945).length < 2 ^ (prefixWord ++ tailWord_1398945).sum := by decide
  have hdescent : baseEnd_1398945 < baseStart_1398945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398962 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2]
def baseStart_1398962 : Nat := 118140960795 + 1398962 * 2 ^ 59
def prefixEnd_1398962 : Nat := 4983230072969 + 3 ^ 40 * 1398962 * 2
def baseEnd_1398962 : Nat := 718339923375260788441297

theorem tailTrace_1398962 : CollatzResearch.WordTrace tailWord_1398962 prefixEnd_1398962 718339923375260788441297 := by
  unfold tailWord_1398962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12756083989451768133255785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34016223971871381688682093 12756083989451768133255785)
  ·
    refine ⟨9567062992088826099941839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12756083989451768133255785 9567062992088826099941839)
    ·
      refine ⟨14350594488133239149912759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9567062992088826099941839 14350594488133239149912759)
      ·
        refine ⟨21525891732199858724869139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14350594488133239149912759 21525891732199858724869139)
        ·
          refine ⟨32288837598299788087303709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21525891732199858724869139 32288837598299788087303709)
          ·
            refine ⟨12108314099362420532738891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32288837598299788087303709 12108314099362420532738891)
            ·
              refine ⟨18162471149043630799108337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12108314099362420532738891 18162471149043630799108337)
              ·
                refine ⟨13621853361782723099331253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18162471149043630799108337 13621853361782723099331253)
                ·
                  refine ⟨1277048752667130290562305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13621853361782723099331253 1277048752667130290562305)
                  ·
                    refine ⟨957786564500347717921729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1277048752667130290562305 957786564500347717921729)
                    ·
                      refine ⟨718339923375260788441297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957786564500347717921729 718339923375260788441297)
                      ·
                        rfl

theorem cell23_1398962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_1398962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398962 prefixEnd_1398962 := by exact prefixLift 1398962
  have htrace : WordTrace (prefixWord ++ tailWord_1398962) baseStart_1398962 baseEnd_1398962 := by
    simpa [prefixWord, tailWord_1398962, baseEnd_1398962] using wordTrace_append hprefix tailTrace_1398962
  have hstable : (prefixWord ++ tailWord_1398962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398962).length < 2 ^ (prefixWord ++ tailWord_1398962).sum := by decide
  have hdescent : baseEnd_1398962 < baseStart_1398962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398972 : List Nat := [2, 2, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_1398972 : Nat := 118140960795 + 1398972 * 2 ^ 59
def prefixEnd_1398972 : Nat := 4983230072969 + 3 ^ 40 * 1398972 * 2
def baseEnd_1398972 : Nat := 239448352727268583105417

theorem tailTrace_1398972 : CollatzResearch.WordTrace tailWord_1398972 prefixEnd_1398972 239448352727268583105417 := by
  unfold tailWord_1398972
  simp only [CollatzResearch.WordTrace]
  refine ⟨25512350343885422120443585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34016467125180562827258113 25512350343885422120443585)
  ·
    refine ⟨19134262757914066590332689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25512350343885422120443585 19134262757914066590332689)
    ·
      refine ⟨14350697068435549942749517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19134262757914066590332689 14350697068435549942749517)
      ·
        refine ⟨5381511400663331228531069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14350697068435549942749517 5381511400663331228531069)
        ·
          refine ⟨2018066775248749210699151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5381511400663331228531069 2018066775248749210699151)
          ·
            refine ⟨3027100162873123816048727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018066775248749210699151 3027100162873123816048727)
            ·
              refine ⟨4540650244309685724073091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027100162873123816048727 4540650244309685724073091)
              ·
                refine ⟨6810975366464528586109637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4540650244309685724073091 6810975366464528586109637)
                ·
                  refine ⟨1277057881212099109895557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6810975366464528586109637 1277057881212099109895557)
                  ·
                    refine ⟨239448352727268583105417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277057881212099109895557 239448352727268583105417)
                    ·
                      rfl

theorem cell23_1398972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_1398972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398972 prefixEnd_1398972 := by exact prefixLift 1398972
  have htrace : WordTrace (prefixWord ++ tailWord_1398972) baseStart_1398972 baseEnd_1398972 := by
    simpa [prefixWord, tailWord_1398972, baseEnd_1398972] using wordTrace_append hprefix tailTrace_1398972
  have hstable : (prefixWord ++ tailWord_1398972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398972).length < 2 ^ (prefixWord ++ tailWord_1398972).sum := by decide
  have hdescent : baseEnd_1398972 < baseStart_1398972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1398995 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 3]
def baseStart_1398995 : Nat := 118140960795 + 1398995 * 2 ^ 59
def prefixEnd_1398995 : Nat := 4983230072969 + 3 ^ 40 * 1398995 * 2
def baseEnd_1398995 : Nat := 718356868236859159328645

theorem tailTrace_1398995 : CollatzResearch.WordTrace tailWord_1398995 prefixEnd_1398995 718356868236859159328645 := by
  unfold tailWord_1398995
  simp only [CollatzResearch.WordTrace]
  refine ⟨51025539566687519168974439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34017026377791679445982959 51025539566687519168974439)
  ·
    refine ⟨76538309350031278753461659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51025539566687519168974439 76538309350031278753461659)
    ·
      refine ⟨114807464025046918130192489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76538309350031278753461659 114807464025046918130192489)
      ·
        refine ⟨86105598018785188597644367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114807464025046918130192489 86105598018785188597644367)
        ·
          refine ⟨129158397028177782896466551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86105598018785188597644367 129158397028177782896466551)
          ·
            refine ⟨193737595542266674344699827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129158397028177782896466551 193737595542266674344699827)
            ·
              refine ⟨290606393313400011517049741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 193737595542266674344699827 290606393313400011517049741)
              ·
                refine ⟨108977397492525004318893653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290606393313400011517049741 108977397492525004318893653)
                ·
                  refine ⟨1277078876865527394362035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 108977397492525004318893653 1277078876865527394362035)
                  ·
                    refine ⟨1915618315298291091543053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1277078876865527394362035 1915618315298291091543053)
                    ·
                      refine ⟨718356868236859159328645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1915618315298291091543053 718356868236859159328645)
                      ·
                        rfl

theorem cell23_1398995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 3].length) (baseStart_1398995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1398995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1398995 prefixEnd_1398995 := by exact prefixLift 1398995
  have htrace : WordTrace (prefixWord ++ tailWord_1398995) baseStart_1398995 baseEnd_1398995 := by
    simpa [prefixWord, tailWord_1398995, baseEnd_1398995] using wordTrace_append hprefix tailTrace_1398995
  have hstable : (prefixWord ++ tailWord_1398995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1398995).length < 2 ^ (prefixWord ++ tailWord_1398995).sum := by decide
  have hdescent : baseEnd_1398995 < baseStart_1398995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1398995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399008 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1399008 : Nat := 118140960795 + 1399008 * 2 ^ 59
def prefixEnd_1399008 : Nat := 4983230072969 + 3 ^ 40 * 1399008 * 2
def baseEnd_1399008 : Nat := 718363543485367608466085

theorem tailTrace_1399008 : CollatzResearch.WordTrace tailWord_1399008 prefixEnd_1399008 718363543485367608466085 := by
  unfold tailWord_1399008
  simp only [CollatzResearch.WordTrace]
  refine ⟨25513006857820211194598839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34017342477093614926131785 25513006857820211194598839)
  ·
    refine ⟨38269510286730316791898259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25513006857820211194598839 38269510286730316791898259)
    ·
      refine ⟨57404265430095475187847389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38269510286730316791898259 57404265430095475187847389)
      ·
        refine ⟨21526599536285803195442771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57404265430095475187847389 21526599536285803195442771)
        ·
          refine ⟨32289899304428704793164157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21526599536285803195442771 32289899304428704793164157)
          ·
            refine ⟨12108712239160764297436559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32289899304428704793164157 12108712239160764297436559)
            ·
              refine ⟨18163068358741146446154839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12108712239160764297436559 18163068358741146446154839)
              ·
                refine ⟨27244602538111719669232259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18163068358741146446154839 27244602538111719669232259)
                ·
                  refine ⟨40866903807167579503848389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27244602538111719669232259 40866903807167579503848389)
                  ·
                    refine ⟨7662544463843921156971573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40866903807167579503848389 7662544463843921156971573)
                    ·
                      refine ⟨718363543485367608466085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7662544463843921156971573 718363543485367608466085)
                      ·
                        rfl

theorem cell23_1399008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1399008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399008 prefixEnd_1399008 := by exact prefixLift 1399008
  have htrace : WordTrace (prefixWord ++ tailWord_1399008) baseStart_1399008 baseEnd_1399008 := by
    simpa [prefixWord, tailWord_1399008, baseEnd_1399008] using wordTrace_append hprefix tailTrace_1399008
  have hstable : (prefixWord ++ tailWord_1399008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399008).length < 2 ^ (prefixWord ++ tailWord_1399008).sum := by decide
  have hdescent : baseEnd_1399008 < baseStart_1399008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399013 : List Nat := [1, 3, 1, 4, 2, 3, 1, 3, 1, 2, 2]
def baseStart_1399013 : Nat := 118140960795 + 1399013 * 2 ^ 59
def prefixEnd_1399013 : Nat := 4983230072969 + 3 ^ 40 * 1399013 * 2
def baseEnd_1399013 : Nat := 718366110888640088903563

theorem tailTrace_1399013 : CollatzResearch.WordTrace tailWord_1399013 prefixEnd_1399013 718366110888640088903563 := by
  unfold tailWord_1399013
  simp only [CollatzResearch.WordTrace]
  refine ⟨51026196080622308243129693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34017464053748205495419795 51026196080622308243129693)
  ·
    refine ⟨19134823530233365591173635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51026196080622308243129693 19134823530233365591173635)
    ·
      refine ⟨28702235295350048386760453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19134823530233365591173635 28702235295350048386760453)
      ·
        refine ⟨5381669117878134072517585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28702235295350048386760453 5381669117878134072517585)
        ·
          refine ⟨4036251838408600554388189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5381669117878134072517585 4036251838408600554388189)
          ·
            refine ⟨1513594439403225207895571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4036251838408600554388189 1513594439403225207895571)
            ·
              refine ⟨2270391659104837811843357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513594439403225207895571 2270391659104837811843357)
              ·
                refine ⟨851396872164314179441259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2270391659104837811843357 851396872164314179441259)
                ·
                  refine ⟨1277095308246471269161889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851396872164314179441259 1277095308246471269161889)
                  ·
                    refine ⟨957821481184853451871417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1277095308246471269161889 957821481184853451871417)
                    ·
                      refine ⟨718366110888640088903563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957821481184853451871417 718366110888640088903563)
                      ·
                        rfl

theorem cell23_1399013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_1399013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399013 prefixEnd_1399013 := by exact prefixLift 1399013
  have htrace : WordTrace (prefixWord ++ tailWord_1399013) baseStart_1399013 baseEnd_1399013 := by
    simpa [prefixWord, tailWord_1399013, baseEnd_1399013] using wordTrace_append hprefix tailTrace_1399013
  have hstable : (prefixWord ++ tailWord_1399013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399013).length < 2 ^ (prefixWord ++ tailWord_1399013).sum := by decide
  have hdescent : baseEnd_1399013 < baseStart_1399013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399022 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_1399022 : Nat := 118140960795 + 1399022 * 2 ^ 59
def prefixEnd_1399022 : Nat := 4983230072969 + 3 ^ 40 * 1399022 * 2
def baseEnd_1399022 : Nat := 718370732214530553691021

theorem tailTrace_1399022 : CollatzResearch.WordTrace tailWord_1399022 prefixEnd_1399022 718370732214530553691021 := by
  unfold tailWord_1399022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6378315542198712847525915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34017682891726468520138213 6378315542198712847525915)
  ·
    refine ⟨9567473313298069271288873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6378315542198712847525915 9567473313298069271288873)
    ·
      refine ⟨7175604984973551953466655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9567473313298069271288873 7175604984973551953466655)
      ·
        refine ⟨10763407477460327930199983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175604984973551953466655 10763407477460327930199983)
        ·
          refine ⟨16145111216190491895299975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10763407477460327930199983 16145111216190491895299975)
          ·
            refine ⟨24217666824285737842949963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16145111216190491895299975 24217666824285737842949963)
            ·
              refine ⟨36326500236428606764424945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24217666824285737842949963 36326500236428606764424945)
              ·
                refine ⟨27244875177321455073318709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36326500236428606764424945 27244875177321455073318709)
                ·
                  refine ⟨2554207047873886413123629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27244875177321455073318709 2554207047873886413123629)
                  ·
                    refine ⟨957827642952707404921361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554207047873886413123629 957827642952707404921361)
                    ·
                      refine ⟨718370732214530553691021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957827642952707404921361 718370732214530553691021)
                      ·
                        rfl

theorem cell23_1399022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_1399022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399022 prefixEnd_1399022 := by exact prefixLift 1399022
  have htrace : WordTrace (prefixWord ++ tailWord_1399022) baseStart_1399022 baseEnd_1399022 := by
    simpa [prefixWord, tailWord_1399022, baseEnd_1399022] using wordTrace_append hprefix tailTrace_1399022
  have hstable : (prefixWord ++ tailWord_1399022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399022).length < 2 ^ (prefixWord ++ tailWord_1399022).sum := by decide
  have hdescent : baseEnd_1399022 < baseStart_1399022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399052 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 1, 4, 2]
def baseStart_1399052 : Nat := 118140960795 + 1399052 * 2 ^ 59
def prefixEnd_1399052 : Nat := 4983230072969 + 3 ^ 40 * 1399052 * 2
def baseEnd_1399052 : Nat := 718386136634165436315883

theorem tailTrace_1399052 : CollatzResearch.WordTrace tailWord_1399052 prefixEnd_1399052 718386136634165436315883 := by
  unfold tailWord_1399052
  simp only [CollatzResearch.WordTrace]
  refine ⟨25513809263740508951899705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34018412351654011935866273 25513809263740508951899705)
  ·
    refine ⟨19135356947805381713924779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25513809263740508951899705 19135356947805381713924779)
    ·
      refine ⟨28703035421708072570887169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19135356947805381713924779 28703035421708072570887169)
      ·
        refine ⟨21527276566281054428165377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28703035421708072570887169 21527276566281054428165377)
        ·
          refine ⟨16145457424710790821124033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21527276566281054428165377 16145457424710790821124033)
          ·
            refine ⟨12109093068533093115843025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16145457424710790821124033 12109093068533093115843025)
            ·
              refine ⟨9081819801399819836882269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12109093068533093115843025 9081819801399819836882269)
              ·
                refine ⟨3405682425524932438830851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9081819801399819836882269 3405682425524932438830851)
                ·
                  refine ⟨5108523638287398658246277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3405682425524932438830851 5108523638287398658246277)
                  ·
                    refine ⟨957848182178887248421177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5108523638287398658246277 957848182178887248421177)
                    ·
                      refine ⟨718386136634165436315883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 957848182178887248421177 718386136634165436315883)
                      ·
                        rfl

theorem cell23_1399052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_1399052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399052 prefixEnd_1399052 := by exact prefixLift 1399052
  have htrace : WordTrace (prefixWord ++ tailWord_1399052) baseStart_1399052 baseEnd_1399052 := by
    simpa [prefixWord, tailWord_1399052, baseEnd_1399052] using wordTrace_append hprefix tailTrace_1399052
  have hstable : (prefixWord ++ tailWord_1399052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399052).length < 2 ^ (prefixWord ++ tailWord_1399052).sum := by decide
  have hdescent : baseEnd_1399052 < baseStart_1399052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399102 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1399102 : Nat := 118140960795 + 1399102 * 2 ^ 59
def prefixEnd_1399102 : Nat := 4983230072969 + 3 ^ 40 * 1399102 * 2
def baseEnd_1399102 : Nat := 718411810666890240690653

theorem tailTrace_1399102 : CollatzResearch.WordTrace tailWord_1399102 prefixEnd_1399102 718411810666890240690653 := by
  unfold tailWord_1399102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6378680272162484555389945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34019628118199917628746373 6378680272162484555389945)
  ·
    refine ⟨4784010204121863416542459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6378680272162484555389945 4784010204121863416542459)
    ·
      refine ⟨7176015306182795124813689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4784010204121863416542459 7176015306182795124813689)
      ·
        refine ⟨5382011479637096343610267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7176015306182795124813689 5382011479637096343610267)
        ·
          refine ⟨8073017219455644515415401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382011479637096343610267 8073017219455644515415401)
          ·
            refine ⟨6054762914591733386561551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8073017219455644515415401 6054762914591733386561551)
            ·
              refine ⟨9082144371887600079842327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6054762914591733386561551 9082144371887600079842327)
              ·
                refine ⟨13623216557831400119763491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9082144371887600079842327 13623216557831400119763491)
                ·
                  refine ⟨20434824836747100179645237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13623216557831400119763491 20434824836747100179645237)
                  ·
                    refine ⟨1915764828445040641841741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20434824836747100179645237 1915764828445040641841741)
                    ·
                      refine ⟨718411810666890240690653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1915764828445040641841741 718411810666890240690653)
                      ·
                        rfl

theorem cell23_1399102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1399102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399102 prefixEnd_1399102 := by exact prefixLift 1399102
  have htrace : WordTrace (prefixWord ++ tailWord_1399102) baseStart_1399102 baseEnd_1399102 := by
    simpa [prefixWord, tailWord_1399102, baseEnd_1399102] using wordTrace_append hprefix tailTrace_1399102
  have hstable : (prefixWord ++ tailWord_1399102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399102).length < 2 ^ (prefixWord ++ tailWord_1399102).sum := by decide
  have hdescent : baseEnd_1399102 < baseStart_1399102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399122 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 2, 5]
def baseStart_1399122 : Nat := 118140960795 + 1399122 * 2 ^ 59
def prefixEnd_1399122 : Nat := 4983230072969 + 3 ^ 40 * 1399122 * 2
def baseEnd_1399122 : Nat := 239474026759993387480187

theorem tailTrace_1399122 : CollatzResearch.WordTrace tailWord_1399122 prefixEnd_1399122 239474026759993387480187 := by
  unfold tailWord_1399122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12757542909306854964711905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34020114424818279905898413 12757542909306854964711905)
  ·
    refine ⟨9568157181980141223533929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12757542909306854964711905 9568157181980141223533929)
    ·
      refine ⟨7176117886485105917650447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9568157181980141223533929 7176117886485105917650447)
      ·
        refine ⟨10764176829727658876475671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7176117886485105917650447 10764176829727658876475671)
        ·
          refine ⟨16146265244591488314713507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10764176829727658876475671 16146265244591488314713507)
          ·
            refine ⟨24219397866887232472070261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16146265244591488314713507 24219397866887232472070261)
            ·
              refine ⟨2270568550020678044256587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24219397866887232472070261 2270568550020678044256587)
              ·
                refine ⟨3405852825031017066384881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270568550020678044256587 3405852825031017066384881)
                ·
                  refine ⟨2554389618773262799788661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3405852825031017066384881 2554389618773262799788661)
                  ·
                    refine ⟨239474026759993387480187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2554389618773262799788661 239474026759993387480187)
                    ·
                      rfl

theorem cell23_1399122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_1399122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399122 prefixEnd_1399122 := by exact prefixLift 1399122
  have htrace : WordTrace (prefixWord ++ tailWord_1399122) baseStart_1399122 baseEnd_1399122 := by
    simpa [prefixWord, tailWord_1399122, baseEnd_1399122] using wordTrace_append hprefix tailTrace_1399122
  have hstable : (prefixWord ++ tailWord_1399122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399122).length < 2 ^ (prefixWord ++ tailWord_1399122).sum := by decide
  have hdescent : baseEnd_1399122 < baseStart_1399122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399152 : List Nat := [2, 1, 1, 1, 4, 3, 1, 3, 3, 4]
def baseStart_1399152 : Nat := 118140960795 + 1399152 * 2 ^ 59
def prefixEnd_1399152 : Nat := 4983230072969 + 3 ^ 40 * 1399152 * 2
def baseEnd_1399152 : Nat := 239479161566538348355141

theorem tailTrace_1399152 : CollatzResearch.WordTrace tailWord_1399152 prefixEnd_1399152 239479161566538348355141 := by
  unfold tailWord_1399152
  simp only [CollatzResearch.WordTrace]
  refine ⟨25515632913559367491219855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34020843884745823321626473 25515632913559367491219855)
  ·
    refine ⟨38273449370339051236829783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25515632913559367491219855 38273449370339051236829783)
    ·
      refine ⟨57410174055508576855244675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38273449370339051236829783 57410174055508576855244675)
      ·
        refine ⟨86115261083262865282867013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57410174055508576855244675 86115261083262865282867013)
        ·
          refine ⟨16146611453111787240537565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86115261083262865282867013 16146611453111787240537565)
          ·
            refine ⟨6054979294916920215201587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16146611453111787240537565 6054979294916920215201587)
            ·
              refine ⟨9082468942375380322802381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6054979294916920215201587 9082468942375380322802381)
              ·
                refine ⟨3405925853390767621050893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9082468942375380322802381 3405925853390767621050893)
                ·
                  refine ⟨1277222195021537857894085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3405925853390767621050893 1277222195021537857894085)
                  ·
                    refine ⟨239479161566538348355141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277222195021537857894085 239479161566538348355141)
                    ·
                      rfl

theorem cell23_1399152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_1399152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399152 prefixEnd_1399152 := by exact prefixLift 1399152
  have htrace : WordTrace (prefixWord ++ tailWord_1399152) baseStart_1399152 baseEnd_1399152 := by
    simpa [prefixWord, tailWord_1399152, baseEnd_1399152] using wordTrace_append hprefix tailTrace_1399152
  have hstable : (prefixWord ++ tailWord_1399152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399152).length < 2 ^ (prefixWord ++ tailWord_1399152).sum := by decide
  have hdescent : baseEnd_1399152 < baseStart_1399152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399169 : List Nat := [1, 2, 4, 3, 1, 1, 2, 2, 3, 4]
def baseStart_1399169 : Nat := 118140960795 + 1399169 * 2 ^ 59
def prefixEnd_1399169 : Nat := 4983230072969 + 3 ^ 40 * 1399169 * 2
def baseEnd_1399169 : Nat := 239482071290247159517615

theorem tailTrace_1399169 : CollatzResearch.WordTrace tailWord_1399169 prefixEnd_1399169 239482071290247159517615 := by
  unfold tailWord_1399169
  simp only [CollatzResearch.WordTrace]
  refine ⟨51031885868057146885808561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34021257245371431257205707 51031885868057146885808561)
  ·
    refine ⟨38273914401042860164356421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51031885868057146885808561 38273914401042860164356421)
    ·
      refine ⟨7176358950195536280816829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38273914401042860164356421 7176358950195536280816829)
      ·
        refine ⟨2691134606323326105306311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7176358950195536280816829 2691134606323326105306311)
        ·
          refine ⟨4036701909484989157959467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691134606323326105306311 4036701909484989157959467)
          ·
            refine ⟨6055052864227483736939201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036701909484989157959467 6055052864227483736939201)
            ·
              refine ⟨4541289648170612802704401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055052864227483736939201 4541289648170612802704401)
              ·
                refine ⟨3405967236127959602028301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541289648170612802704401 3405967236127959602028301)
                ·
                  refine ⟨1277237713547984850760613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3405967236127959602028301 1277237713547984850760613)
                  ·
                    refine ⟨239482071290247159517615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277237713547984850760613 239482071290247159517615)
                    ·
                      rfl

theorem cell23_1399169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_1399169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399169 prefixEnd_1399169 := by exact prefixLift 1399169
  have htrace : WordTrace (prefixWord ++ tailWord_1399169) baseStart_1399169 baseEnd_1399169 := by
    simpa [prefixWord, tailWord_1399169, baseEnd_1399169] using wordTrace_append hprefix tailTrace_1399169
  have hstable : (prefixWord ++ tailWord_1399169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399169).length < 2 ^ (prefixWord ++ tailWord_1399169).sum := by decide
  have hdescent : baseEnd_1399169 < baseStart_1399169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399182 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_1399182 : Nat := 118140960795 + 1399182 * 2 ^ 59
def prefixEnd_1399182 : Nat := 4983230072969 + 3 ^ 40 * 1399182 * 2
def baseEnd_1399182 : Nat := 79828098791027769743365

theorem tailTrace_1399182 : CollatzResearch.WordTrace tailWord_1399182 prefixEnd_1399182 79828098791027769743365 := by
  unfold tailWord_1399182
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379045002126256263253975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34021573344673366737354533 6379045002126256263253975)
  ·
    refine ⟨9568567503189384394880963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6379045002126256263253975 9568567503189384394880963)
    ·
      refine ⟨14352851254784076592321445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9568567503189384394880963 14352851254784076592321445)
      ·
        refine ⟨2691159610272014361060271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14352851254784076592321445 2691159610272014361060271)
        ·
          refine ⟨4036739415408021541590407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691159610272014361060271 4036739415408021541590407)
          ·
            refine ⟨6055109123112032312385611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4036739415408021541590407 6055109123112032312385611)
            ·
              refine ⟨9082663684668048468578417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055109123112032312385611 9082663684668048468578417)
              ·
                refine ⟨6811997763501036351433813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9082663684668048468578417 6811997763501036351433813)
                ·
                  refine ⟨79828098791027769743365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6811997763501036351433813 79828098791027769743365)
                  ·
                    rfl

theorem cell23_1399182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_1399182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399182 prefixEnd_1399182 := by exact prefixLift 1399182
  have htrace : WordTrace (prefixWord ++ tailWord_1399182) baseStart_1399182 baseEnd_1399182 := by
    simpa [prefixWord, tailWord_1399182, baseEnd_1399182] using wordTrace_append hprefix tailTrace_1399182
  have hstable : (prefixWord ++ tailWord_1399182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399182).length < 2 ^ (prefixWord ++ tailWord_1399182).sum := by decide
  have hdescent : baseEnd_1399182 < baseStart_1399182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399215 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_1399215 : Nat := 118140960795 + 1399215 * 2 ^ 59
def prefixEnd_1399215 : Nat := 4983230072969 + 3 ^ 40 * 1399215 * 2
def baseEnd_1399215 : Nat := 718469833980848298577633

theorem tailTrace_1399215 : CollatzResearch.WordTrace tailWord_1399215 prefixEnd_1399215 718469833980848298577633 := by
  unfold tailWord_1399215
  simp only [CollatzResearch.WordTrace]
  refine ⟨51033563625890496741983099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34022375750593664494655399 51033563625890496741983099)
  ·
    refine ⟨76550345438835745112974649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51033563625890496741983099 76550345438835745112974649)
    ·
      refine ⟨57412759079126808834730987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76550345438835745112974649 57412759079126808834730987)
      ·
        refine ⟨86119138618690213252096481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57412759079126808834730987 86119138618690213252096481)
        ·
          refine ⟨64589353964017659939072361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86119138618690213252096481 64589353964017659939072361)
          ·
            refine ⟨48442015473013244954304271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64589353964017659939072361 48442015473013244954304271)
            ·
              refine ⟨72663023209519867431456407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48442015473013244954304271 72663023209519867431456407)
              ·
                refine ⟨108994534814279801147184611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72663023209519867431456407 108994534814279801147184611)
                ·
                  refine ⟨163491802221419701720776917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108994534814279801147184611 163491802221419701720776917)
                  ·
                    refine ⟨3831839114564524259080709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 163491802221419701720776917 3831839114564524259080709)
                    ·
                      refine ⟨718469833980848298577633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3831839114564524259080709 718469833980848298577633)
                      ·
                        rfl

theorem cell23_1399215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_1399215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399215 prefixEnd_1399215 := by exact prefixLift 1399215
  have htrace : WordTrace (prefixWord ++ tailWord_1399215) baseStart_1399215 baseEnd_1399215 := by
    simpa [prefixWord, tailWord_1399215, baseEnd_1399215] using wordTrace_append hprefix tailTrace_1399215
  have hstable : (prefixWord ++ tailWord_1399215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399215).length < 2 ^ (prefixWord ++ tailWord_1399215).sum := by decide
  have hdescent : baseEnd_1399215 < baseStart_1399215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399229 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_1399229 : Nat := 118140960795 + 1399229 * 2 ^ 59
def prefixEnd_1399229 : Nat := 4983230072969 + 3 ^ 40 * 1399229 * 2
def baseEnd_1399229 : Nat := 239492340903337081267523

theorem tailTrace_1399229 : CollatzResearch.WordTrace tailWord_1399229 prefixEnd_1399229 239492340903337081267523 := by
  unfold tailWord_1399229
  simp only [CollatzResearch.WordTrace]
  refine ⟨51034074247839777132992741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34022716165226518088661827 51034074247839777132992741)
  ·
    refine ⟨9568888921469958212436139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51034074247839777132992741 9568888921469958212436139)
    ·
      refine ⟨14353333382204937318654209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9568888921469958212436139 14353333382204937318654209)
      ·
        refine ⟨10765000036653702988990657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14353333382204937318654209 10765000036653702988990657)
        ·
          refine ⟨8073750027490277241742993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10765000036653702988990657 8073750027490277241742993)
          ·
            refine ⟨6055312520617707931307245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8073750027490277241742993 6055312520617707931307245)
            ·
              refine ⟨2270742195231640474240217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6055312520617707931307245 2270742195231640474240217)
              ·
                refine ⟨1703056646423730355680163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270742195231640474240217 1703056646423730355680163)
                ·
                  refine ⟨2554584969635595533520245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703056646423730355680163 2554584969635595533520245)
                  ·
                    refine ⟨239492340903337081267523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2554584969635595533520245 239492340903337081267523)
                    ·
                      rfl

theorem cell23_1399229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_1399229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399229 prefixEnd_1399229 := by exact prefixLift 1399229
  have htrace : WordTrace (prefixWord ++ tailWord_1399229) baseStart_1399229 baseEnd_1399229 := by
    simpa [prefixWord, tailWord_1399229, baseEnd_1399229] using wordTrace_append hprefix tailTrace_1399229
  have hstable : (prefixWord ++ tailWord_1399229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399229).length < 2 ^ (prefixWord ++ tailWord_1399229).sum := by decide
  have hdescent : baseEnd_1399229 < baseStart_1399229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399242 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 1, 6]
def baseStart_1399242 : Nat := 118140960795 + 1399242 * 2 ^ 59
def prefixEnd_1399242 : Nat := 4983230072969 + 3 ^ 40 * 1399242 * 2
def baseEnd_1399242 : Nat := 239494565986173230980003

theorem tailTrace_1399242 : CollatzResearch.WordTrace tailWord_1399242 prefixEnd_1399242 239494565986173230980003 := by
  unfold tailWord_1399242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12758637099198170088303995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34023032264528453568810653 12758637099198170088303995)
  ·
    refine ⟨19137955648797255132455993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12758637099198170088303995 19137955648797255132455993)
    ·
      refine ⟨14353466736597941349341995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19137955648797255132455993 14353466736597941349341995)
      ·
        refine ⟨21530200104896912024012993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14353466736597941349341995 21530200104896912024012993)
        ·
          refine ⟨16147650078672684018009745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21530200104896912024012993 16147650078672684018009745)
          ·
            refine ⟨12110737559004513013507309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16147650078672684018009745 12110737559004513013507309)
            ·
              refine ⟨4541526584626692380065241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12110737559004513013507309 4541526584626692380065241)
              ·
                refine ⟨3406144938470019285048931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4541526584626692380065241 3406144938470019285048931)
                ·
                  refine ⟨5109217407705028927573397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406144938470019285048931 5109217407705028927573397)
                  ·
                    refine ⟨239494565986173230980003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5109217407705028927573397 239494565986173230980003)
                    ·
                      rfl

theorem cell23_1399242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_1399242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399242 prefixEnd_1399242 := by exact prefixLift 1399242
  have htrace : WordTrace (prefixWord ++ tailWord_1399242) baseStart_1399242 baseEnd_1399242 := by
    simpa [prefixWord, tailWord_1399242, baseEnd_1399242] using wordTrace_append hprefix tailTrace_1399242
  have hstable : (prefixWord ++ tailWord_1399242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399242).length < 2 ^ (prefixWord ++ tailWord_1399242).sum := by decide
  have hdescent : baseEnd_1399242 < baseStart_1399242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399272 : List Nat := [2, 1, 4, 1, 1, 3, 3, 8]
def baseStart_1399272 : Nat := 118140960795 + 1399272 * 2 ^ 59
def prefixEnd_1399272 : Nat := 4983230072969 + 3 ^ 40 * 1399272 * 2
def baseEnd_1399272 : Nat := 26611077865857576872773

theorem tailTrace_1399272 : CollatzResearch.WordTrace tailWord_1399272 prefixEnd_1399272 26611077865857576872773 := by
  unfold tailWord_1399272
  simp only [CollatzResearch.WordTrace]
  refine ⟨25517821293341997738404035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34023761724455996984538713 25517821293341997738404035)
  ·
    refine ⟨38276731940012996607606053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25517821293341997738404035 38276731940012996607606053)
    ·
      refine ⟨7176887238752436863926135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38276731940012996607606053 7176887238752436863926135)
      ·
        refine ⟨10765330858128655295889203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7176887238752436863926135 10765330858128655295889203)
        ·
          refine ⟨16147996287192982943833805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10765330858128655295889203 16147996287192982943833805)
          ·
            refine ⟨6055498607697368603937677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16147996287192982943833805 6055498607697368603937677)
            ·
              refine ⟨2270811977886513226476629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6055498607697368603937677 2270811977886513226476629)
              ·
                refine ⟨26611077865857576872773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2270811977886513226476629 26611077865857576872773)
                ·
                  rfl

theorem cell23_1399272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 8].length) (baseStart_1399272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399272 prefixEnd_1399272 := by exact prefixLift 1399272
  have htrace : WordTrace (prefixWord ++ tailWord_1399272) baseStart_1399272 baseEnd_1399272 := by
    simpa [prefixWord, tailWord_1399272, baseEnd_1399272] using wordTrace_append hprefix tailTrace_1399272
  have hstable : (prefixWord ++ tailWord_1399272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399272).length < 2 ^ (prefixWord ++ tailWord_1399272).sum := by decide
  have hdescent : baseEnd_1399272 < baseStart_1399272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399286 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3]
def baseStart_1399286 : Nat := 118140960795 + 1399286 * 2 ^ 59
def prefixEnd_1399286 : Nat := 4983230072969 + 3 ^ 40 * 1399286 * 2
def baseEnd_1399286 : Nat := 718506291107317520789807

theorem tailTrace_1399286 : CollatzResearch.WordTrace tailWord_1399286 prefixEnd_1399286 718506291107317520789807 := by
  unfold tailWord_1399286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189759575539579741738607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34024102139088850578545141 3189759575539579741738607)
  ·
    refine ⟨4784639363309369612607911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3189759575539579741738607 4784639363309369612607911)
    ·
      refine ⟨7176959044964054418911867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4784639363309369612607911 7176959044964054418911867)
      ·
        refine ⟨10765438567446081628367801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7176959044964054418911867 10765438567446081628367801)
        ·
          refine ⟨8074078925584561221275851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10765438567446081628367801 8074078925584561221275851)
          ·
            refine ⟨12111118388376841831913777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8074078925584561221275851 12111118388376841831913777)
            ·
              refine ⟨9083338791282631373935333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12111118388376841831913777 9083338791282631373935333)
              ·
                refine ⟨1703126023365493382612875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9083338791282631373935333 1703126023365493382612875)
                ·
                  refine ⟨2554689035048240073919313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703126023365493382612875 2554689035048240073919313)
                  ·
                    refine ⟨1916016776286180055439485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2554689035048240073919313 1916016776286180055439485)
                    ·
                      refine ⟨718506291107317520789807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1916016776286180055439485 718506291107317520789807)
                      ·
                        rfl

theorem cell23_1399286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3].length) (baseStart_1399286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399286 prefixEnd_1399286 := by exact prefixLift 1399286
  have htrace : WordTrace (prefixWord ++ tailWord_1399286) baseStart_1399286 baseEnd_1399286 := by
    simpa [prefixWord, tailWord_1399286, baseEnd_1399286] using wordTrace_append hprefix tailTrace_1399286
  have hstable : (prefixWord ++ tailWord_1399286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399286).length < 2 ^ (prefixWord ++ tailWord_1399286).sum := by decide
  have hdescent : baseEnd_1399286 < baseStart_1399286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399299 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 3]
def baseStart_1399299 : Nat := 118140960795 + 1399299 * 2 ^ 59
def prefixEnd_1399299 : Nat := 4983230072969 + 3 ^ 40 * 1399299 * 2
def baseEnd_1399299 : Nat := 718512966355825969927247

theorem tailTrace_1399299 : CollatzResearch.WordTrace tailWord_1399299 prefixEnd_1399299 718512966355825969927247 := by
  unfold tailWord_1399299
  simp only [CollatzResearch.WordTrace]
  refine ⟨51036627357586179088040951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34024418238390786058693967 51036627357586179088040951)
  ·
    refine ⟨76554941036379268632061427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51036627357586179088040951 76554941036379268632061427)
    ·
      refine ⟨114832411554568902948092141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76554941036379268632061427 114832411554568902948092141)
      ·
        refine ⟨43062154332963338605534553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114832411554568902948092141 43062154332963338605534553)
        ·
          refine ⟨32296615749722503954150915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43062154332963338605534553 32296615749722503954150915)
          ·
            refine ⟨48444923624583755931226373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32296615749722503954150915 48444923624583755931226373)
            ·
              refine ⟨9083423179609454237104945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48444923624583755931226373 9083423179609454237104945)
              ·
                refine ⟨6812567384707090677828709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9083423179609454237104945 6812567384707090677828709)
                ·
                  refine ⟨1277356384632579502092883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6812567384707090677828709 1277356384632579502092883)
                  ·
                    refine ⟨1916034576948869253139325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1277356384632579502092883 1916034576948869253139325)
                    ·
                      refine ⟨718512966355825969927247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1916034576948869253139325 718512966355825969927247)
                      ·
                        rfl

theorem cell23_1399299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_1399299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399299 prefixEnd_1399299 := by exact prefixLift 1399299
  have htrace : WordTrace (prefixWord ++ tailWord_1399299) baseStart_1399299 baseEnd_1399299 := by
    simpa [prefixWord, tailWord_1399299, baseEnd_1399299] using wordTrace_append hprefix tailTrace_1399299
  have hstable : (prefixWord ++ tailWord_1399299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399299).length < 2 ^ (prefixWord ++ tailWord_1399299).sum := by decide
  have hdescent : baseEnd_1399299 < baseStart_1399299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399300 : List Nat := [2, 3, 2, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1399300 : Nat := 118140960795 + 1399300 * 2 ^ 59
def prefixEnd_1399300 : Nat := 4983230072969 + 3 ^ 40 * 1399300 * 2
def baseEnd_1399300 : Nat := 718513479836480466014743

theorem tailTrace_1399300 : CollatzResearch.WordTrace tailWord_1399300 prefixEnd_1399300 718513479836480466014743 := by
  unfold tailWord_1399300
  simp only [CollatzResearch.WordTrace]
  refine ⟨25518331915291278129413677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34024442553721704172551569 25518331915291278129413677)
  ·
    refine ⟨9569374468234229298530129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25518331915291278129413677 9569374468234229298530129)
    ·
      refine ⟨7177030851175671973897597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9569374468234229298530129 7177030851175671973897597)
      ·
        refine ⟨2691386569190876990211599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7177030851175671973897597 2691386569190876990211599)
        ·
          refine ⟨4037079853786315485317399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691386569190876990211599 4037079853786315485317399)
          ·
            refine ⟨6055619780679473227976099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037079853786315485317399 6055619780679473227976099)
            ·
              refine ⟨9083429671019209841964149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6055619780679473227976099 9083429671019209841964149)
              ·
                refine ⟨851571531658050922684139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9083429671019209841964149 851571531658050922684139)
                ·
                  refine ⟨1277357297487076384026209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851571531658050922684139 1277357297487076384026209)
                  ·
                    refine ⟨958017973115307288019657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1277357297487076384026209 958017973115307288019657)
                    ·
                      refine ⟨718513479836480466014743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958017973115307288019657 718513479836480466014743)
                      ·
                        rfl

theorem cell23_1399300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1399300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399300 prefixEnd_1399300 := by exact prefixLift 1399300
  have htrace : WordTrace (prefixWord ++ tailWord_1399300) baseStart_1399300 baseEnd_1399300 := by
    simpa [prefixWord, tailWord_1399300, baseEnd_1399300] using wordTrace_append hprefix tailTrace_1399300
  have hstable : (prefixWord ++ tailWord_1399300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399300).length < 2 ^ (prefixWord ++ tailWord_1399300).sum := by decide
  have hdescent : baseEnd_1399300 < baseStart_1399300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399322 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1399322 : Nat := 118140960795 + 1399322 * 2 ^ 59
def prefixEnd_1399322 : Nat := 4983230072969 + 3 ^ 40 * 1399322 * 2
def baseEnd_1399322 : Nat := 718524776410879379939641

theorem tailTrace_1399322 : CollatzResearch.WordTrace tailWord_1399322 prefixEnd_1399322 718524776410879379939641 := by
  unfold tailWord_1399322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759366559125713504032055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34024977491001902677418813 12759366559125713504032055)
  ·
    refine ⟨19139049838688570256048083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12759366559125713504032055 19139049838688570256048083)
    ·
      refine ⟨28708574758032855384072125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19139049838688570256048083 28708574758032855384072125)
      ·
        refine ⟨10765715534262320769027047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28708574758032855384072125 10765715534262320769027047)
        ·
          refine ⟨16148573301393481153540571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10765715534262320769027047 16148573301393481153540571)
          ·
            refine ⟨24222859952090221730310857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16148573301393481153540571 24222859952090221730310857)
            ·
              refine ⟨18167144964067666297733143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24222859952090221730310857 18167144964067666297733143)
              ·
                refine ⟨27250717446101499446599715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18167144964067666297733143 27250717446101499446599715)
                ·
                  refine ⟨40876076169152249169899573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27250717446101499446599715 40876076169152249169899573)
                  ·
                    refine ⟨3832132140858023359678085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40876076169152249169899573 3832132140858023359678085)
                    ·
                      refine ⟨718524776410879379939641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3832132140858023359678085 718524776410879379939641)
                      ·
                        rfl

theorem cell23_1399322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1399322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399322 prefixEnd_1399322 := by exact prefixLift 1399322
  have htrace : WordTrace (prefixWord ++ tailWord_1399322) baseStart_1399322 baseEnd_1399322 := by
    simpa [prefixWord, tailWord_1399322, baseEnd_1399322] using wordTrace_append hprefix tailTrace_1399322
  have hstable : (prefixWord ++ tailWord_1399322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399322).length < 2 ^ (prefixWord ++ tailWord_1399322).sum := by decide
  have hdescent : baseEnd_1399322 < baseStart_1399322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399372 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1399372 : Nat := 118140960795 + 1399372 * 2 ^ 59
def prefixEnd_1399372 : Nat := 4983230072969 + 3 ^ 40 * 1399372 * 2
def baseEnd_1399372 : Nat := 718550450443604184314411

theorem tailTrace_1399372 : CollatzResearch.WordTrace tailWord_1399372 prefixEnd_1399372 718550450443604184314411 := by
  unfold tailWord_1399372
  simp only [CollatzResearch.WordTrace]
  refine ⟨25519644943160856277724185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34026193257547808370298913 25519644943160856277724185)
  ·
    refine ⟨19139733707370642208293139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25519644943160856277724185 19139733707370642208293139)
    ·
      refine ⟨28709600561055963312439709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19139733707370642208293139 28709600561055963312439709)
      ·
        refine ⟨10766100210395986242164891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28709600561055963312439709 10766100210395986242164891)
        ·
          refine ⟨16149150315593979363247337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10766100210395986242164891 16149150315593979363247337)
          ·
            refine ⟨12111862736695484522435503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16149150315593979363247337 12111862736695484522435503)
            ·
              refine ⟨18167794105043226783653255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12111862736695484522435503 18167794105043226783653255)
              ·
                refine ⟨27251691157564840175479883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18167794105043226783653255 27251691157564840175479883)
                ·
                  refine ⟨40877536736347260263219825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27251691157564840175479883 40877536736347260263219825)
                  ·
                    refine ⟨30658152552260445197414869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40877536736347260263219825 30658152552260445197414869)
                    ·
                      refine ⟨718550450443604184314411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30658152552260445197414869 718550450443604184314411)
                      ·
                        rfl

theorem cell23_1399372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1399372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399372 prefixEnd_1399372 := by exact prefixLift 1399372
  have htrace : WordTrace (prefixWord ++ tailWord_1399372) baseStart_1399372 baseEnd_1399372 := by
    simpa [prefixWord, tailWord_1399372, baseEnd_1399372] using wordTrace_append hprefix tailTrace_1399372
  have hstable : (prefixWord ++ tailWord_1399372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399372).length < 2 ^ (prefixWord ++ tailWord_1399372).sum := by decide
  have hdescent : baseEnd_1399372 < baseStart_1399372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399392 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 3, 7]
def baseStart_1399392 : Nat := 118140960795 + 1399392 * 2 ^ 59
def prefixEnd_1399392 : Nat := 4983230072969 + 3 ^ 40 * 1399392 * 2
def baseEnd_1399392 : Nat := 239520240018898035354773

theorem tailTrace_1399392 : CollatzResearch.WordTrace tailWord_1399392 prefixEnd_1399392 239520240018898035354773 := by
  unfold tailWord_1399392
  simp only [CollatzResearch.WordTrace]
  refine ⟨25520009673124627985588215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34026679564166170647450953 25520009673124627985588215)
  ·
    refine ⟨38280014509686941978382323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25520009673124627985588215 38280014509686941978382323)
    ·
      refine ⟨57420021764530412967573485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38280014509686941978382323 57420021764530412967573485)
      ·
        refine ⟨21532508161698904862840057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57420021764530412967573485 21532508161698904862840057)
        ·
          refine ⟨16149381121274178647130043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21532508161698904862840057 16149381121274178647130043)
          ·
            refine ⟨24224071681911267970695065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16149381121274178647130043 24224071681911267970695065)
            ·
              refine ⟨18168053761433450978021299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24224071681911267970695065 18168053761433450978021299)
              ·
                refine ⟨27252080642150176467031949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18168053761433450978021299 27252080642150176467031949)
                ·
                  refine ⟨10219530240806316175136981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27252080642150176467031949 10219530240806316175136981)
                  ·
                    refine ⟨239520240018898035354773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10219530240806316175136981 239520240018898035354773)
                    ·
                      rfl

theorem cell23_1399392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_1399392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399392 prefixEnd_1399392 := by exact prefixLift 1399392
  have htrace : WordTrace (prefixWord ++ tailWord_1399392) baseStart_1399392 baseEnd_1399392 := by
    simpa [prefixWord, tailWord_1399392, baseEnd_1399392] using wordTrace_append hprefix tailTrace_1399392
  have hstable : (prefixWord ++ tailWord_1399392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399392).length < 2 ^ (prefixWord ++ tailWord_1399392).sum := by decide
  have hdescent : baseEnd_1399392 < baseStart_1399392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399394 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1399394 : Nat := 118140960795 + 1399394 * 2 ^ 59
def prefixEnd_1399394 : Nat := 4983230072969 + 3 ^ 40 * 1399394 * 2
def baseEnd_1399394 : Nat := 718561747018003098239311

theorem tailTrace_1399394 : CollatzResearch.WordTrace tailWord_1399394 prefixEnd_1399394 718561747018003098239311 := by
  unfold tailWord_1399394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12760023073060502578187309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34026728194828006875166157 12760023073060502578187309)
  ·
    refine ⟨4785008652397688466820241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12760023073060502578187309 4785008652397688466820241)
    ·
      refine ⟨3588756489298266350115181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4785008652397688466820241 3588756489298266350115181)
      ·
        refine ⟨1345783683486849881293193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3588756489298266350115181 1345783683486849881293193)
        ·
          refine ⟨1009337762615137410969895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345783683486849881293193 1009337762615137410969895)
          ·
            refine ⟨1514006643922706116454843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009337762615137410969895 1514006643922706116454843)
            ·
              refine ⟨2271009965884059174682265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514006643922706116454843 2271009965884059174682265)
              ·
                refine ⟨1703257474413044381011699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2271009965884059174682265 1703257474413044381011699)
                ·
                  refine ⟨2554886211619566571517549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703257474413044381011699 2554886211619566571517549)
                  ·
                    refine ⟨958082329357337464319081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2554886211619566571517549 958082329357337464319081)
                    ·
                      refine ⟨718561747018003098239311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958082329357337464319081 718561747018003098239311)
                      ·
                        rfl

theorem cell23_1399394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1399394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399394 prefixEnd_1399394 := by exact prefixLift 1399394
  have htrace : WordTrace (prefixWord ++ tailWord_1399394) baseStart_1399394 baseEnd_1399394 := by
    simpa [prefixWord, tailWord_1399394, baseEnd_1399394] using wordTrace_append hprefix tailTrace_1399394
  have hstable : (prefixWord ++ tailWord_1399394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399394).length < 2 ^ (prefixWord ++ tailWord_1399394).sum := by decide
  have hdescent : baseEnd_1399394 < baseStart_1399394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399449 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 3]
def baseStart_1399449 : Nat := 118140960795 + 1399449 * 2 ^ 59
def prefixEnd_1399449 : Nat := 4983230072969 + 3 ^ 40 * 1399449 * 2
def baseEnd_1399449 : Nat := 718589988454000383051557

theorem tailTrace_1399449 : CollatzResearch.WordTrace tailWord_1399449 prefixEnd_1399449 718589988454000383051557 := by
  unfold tailWord_1399449
  simp only [CollatzResearch.WordTrace]
  refine ⟨51042098307042754706001401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34028065538028503137334267 51042098307042754706001401)
  ·
    refine ⟨38281573730282066029501051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51042098307042754706001401 38281573730282066029501051)
    ·
      refine ⟨57422360595423099044251577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38281573730282066029501051 57422360595423099044251577)
      ·
        refine ⟨43066770446567324283188683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57422360595423099044251577 43066770446567324283188683)
        ·
          refine ⟨64600155669850986424783025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43066770446567324283188683 64600155669850986424783025)
          ·
            refine ⟨48450116752388239818587269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64600155669850986424783025 48450116752388239818587269)
            ·
              refine ⟨9084396891072794965985113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48450116752388239818587269 9084396891072794965985113)
              ·
                refine ⟨6813297668304596224488835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9084396891072794965985113 6813297668304596224488835)
                ·
                  refine ⟨10219946502456894336733253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813297668304596224488835 10219946502456894336733253)
                  ·
                    refine ⟨1916239969210667688137485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10219946502456894336733253 1916239969210667688137485)
                    ·
                      refine ⟨718589988454000383051557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1916239969210667688137485 718589988454000383051557)
                      ·
                        rfl

theorem cell23_1399449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_1399449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399449 prefixEnd_1399449 := by exact prefixLift 1399449
  have htrace : WordTrace (prefixWord ++ tailWord_1399449) baseStart_1399449 baseEnd_1399449 := by
    simpa [prefixWord, tailWord_1399449, baseEnd_1399449] using wordTrace_append hprefix tailTrace_1399449
  have hstable : (prefixWord ++ tailWord_1399449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399449).length < 2 ^ (prefixWord ++ tailWord_1399449).sum := by decide
  have hdescent : baseEnd_1399449 < baseStart_1399449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399463 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1399463 : Nat := 118140960795 + 1399463 * 2 ^ 59
def prefixEnd_1399463 : Nat := 4983230072969 + 3 ^ 40 * 1399463 * 2
def baseEnd_1399463 : Nat := 718597177183163328276493

theorem tailTrace_1399463 : CollatzResearch.WordTrace tailWord_1399463 prefixEnd_1399463 718597177183163328276493 := by
  unfold tailWord_1399463
  simp only [CollatzResearch.WordTrace]
  refine ⟨51042608928992035097011043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34028405952661356731340695 51042608928992035097011043)
  ·
    refine ⟨76563913393488052645516565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51042608928992035097011043 76563913393488052645516565)
    ·
      refine ⟨3588933440319752467758589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76563913393488052645516565 3588933440319752467758589)
      ·
        refine ⟨1345850040119907175409471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3588933440319752467758589 1345850040119907175409471)
        ·
          refine ⟨2018775060179860763114207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345850040119907175409471 2018775060179860763114207)
          ·
            refine ⟨3028162590269791144671311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018775060179860763114207 3028162590269791144671311)
            ·
              refine ⟨4542243885404686717006967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028162590269791144671311 4542243885404686717006967)
              ·
                refine ⟨6813365828107030075510451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542243885404686717006967 6813365828107030075510451)
                ·
                  refine ⟨10220048742160545113265677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813365828107030075510451 10220048742160545113265677)
                  ·
                    refine ⟨3832518278310204417474629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10220048742160545113265677 3832518278310204417474629)
                    ·
                      refine ⟨718597177183163328276493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3832518278310204417474629 718597177183163328276493)
                      ·
                        rfl

theorem cell23_1399463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1399463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399463 prefixEnd_1399463 := by exact prefixLift 1399463
  have htrace : WordTrace (prefixWord ++ tailWord_1399463) baseStart_1399463 baseEnd_1399463 := by
    simpa [prefixWord, tailWord_1399463, baseEnd_1399463] using wordTrace_append hprefix tailTrace_1399463
  have hstable : (prefixWord ++ tailWord_1399463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399463).length < 2 ^ (prefixWord ++ tailWord_1399463).sum := by decide
  have hdescent : baseEnd_1399463 < baseStart_1399463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399523 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1399523 : Nat := 118140960795 + 1399523 * 2 ^ 59
def prefixEnd_1399523 : Nat := 4983230072969 + 3 ^ 40 * 1399523 * 2
def baseEnd_1399523 : Nat := 718627986022433093526217

theorem tailTrace_1399523 : CollatzResearch.WordTrace tailWord_1399523 prefixEnd_1399523 718627986022433093526217 := by
  unfold tailWord_1399523
  simp only [CollatzResearch.WordTrace]
  refine ⟨51044797308774665344195223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34029864872516443562796815 51044797308774665344195223)
  ·
    refine ⟨76567195963161998016292835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51044797308774665344195223 76567195963161998016292835)
    ·
      refine ⟨114850793944742997024439253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76567195963161998016292835 114850793944742997024439253)
      ·
        refine ⟨2691815483079913992760295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 114850793944742997024439253 2691815483079913992760295)
        ·
          refine ⟨4037723224619870989140443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691815483079913992760295 4037723224619870989140443)
          ·
            refine ⟨6056584836929806483710665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4037723224619870989140443 6056584836929806483710665)
            ·
              refine ⟨4542438627697354862782999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6056584836929806483710665 4542438627697354862782999)
              ·
                refine ⟨6813657941546032294174499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542438627697354862782999 6813657941546032294174499)
                ·
                  refine ⟨10220486912319048441261749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6813657941546032294174499 10220486912319048441261749)
                  ·
                    refine ⟨958170648029910791368289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10220486912319048441261749 958170648029910791368289)
                    ·
                      refine ⟨718627986022433093526217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958170648029910791368289 718627986022433093526217)
                      ·
                        rfl

theorem cell23_1399523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1399523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399523 prefixEnd_1399523 := by exact prefixLift 1399523
  have htrace : WordTrace (prefixWord ++ tailWord_1399523) baseStart_1399523 baseEnd_1399523 := by
    simpa [prefixWord, tailWord_1399523, baseEnd_1399523] using wordTrace_append hprefix tailTrace_1399523
  have hstable : (prefixWord ++ tailWord_1399523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399523).length < 2 ^ (prefixWord ++ tailWord_1399523).sum := by decide
  have hdescent : baseEnd_1399523 < baseStart_1399523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399529 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 1, 6]
def baseStart_1399529 : Nat := 118140960795 + 1399529 * 2 ^ 59
def prefixEnd_1399529 : Nat := 4983230072969 + 3 ^ 40 * 1399529 * 2
def baseEnd_1399529 : Nat := 239543688968786690017063

theorem tailTrace_1399529 : CollatzResearch.WordTrace tailWord_1399529 prefixEnd_1399529 239543688968786690017063 := by
  unfold tailWord_1399529
  simp only [CollatzResearch.WordTrace]
  refine ⟨51045016146752928368913641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34030010764501952245942427 51045016146752928368913641)
  ·
    refine ⟨38283762110064696276685231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51045016146752928368913641 38283762110064696276685231)
    ·
      refine ⟨57425643165097044415027847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38283762110064696276685231 57425643165097044415027847)
      ·
        refine ⟨86138464747645566622541771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57425643165097044415027847 86138464747645566622541771)
        ·
          refine ⟨129207697121468349933812657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86138464747645566622541771 129207697121468349933812657)
          ·
            refine ⟨96905772841101262450359493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129207697121468349933812657 96905772841101262450359493)
            ·
              refine ⟨18169832407706486709442405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96905772841101262450359493 18169832407706486709442405)
              ·
                refine ⟨3406843576444966258020451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18169832407706486709442405 3406843576444966258020451)
                ·
                  refine ⟨5110265364667449387030677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406843576444966258020451 5110265364667449387030677)
                  ·
                    refine ⟨239543688968786690017063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5110265364667449387030677 239543688968786690017063)
                    ·
                      rfl

theorem cell23_1399529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_1399529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399529 prefixEnd_1399529 := by exact prefixLift 1399529
  have htrace : WordTrace (prefixWord ++ tailWord_1399529) baseStart_1399529 baseEnd_1399529 := by
    simpa [prefixWord, tailWord_1399529, baseEnd_1399529] using wordTrace_append hprefix tailTrace_1399529
  have hstable : (prefixWord ++ tailWord_1399529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399529).length < 2 ^ (prefixWord ++ tailWord_1399529).sum := by decide
  have hdescent : baseEnd_1399529 < baseStart_1399529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399536 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4]
def baseStart_1399536 : Nat := 118140960795 + 1399536 * 2 ^ 59
def prefixEnd_1399536 : Nat := 4983230072969 + 3 ^ 40 * 1399536 * 2
def baseEnd_1399536 : Nat := 718634661270941542663657

theorem tailTrace_1399536 : CollatzResearch.WordTrace tailWord_1399536 prefixEnd_1399536 718634661270941542663657 := by
  unfold tailWord_1399536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25522635728863784282209231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34030180971818379042945641 25522635728863784282209231)
  ·
    refine ⟨38283953593295676423313847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25522635728863784282209231 38283953593295676423313847)
    ·
      refine ⟨57425930389943514634970771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38283953593295676423313847 57425930389943514634970771)
      ·
        refine ⟨86138895584915271952456157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57425930389943514634970771 86138895584915271952456157)
        ·
          refine ⟨32302085844343226982171059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86138895584915271952456157 32302085844343226982171059)
          ·
            refine ⟨48453128766514840473256589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32302085844343226982171059 48453128766514840473256589)
            ·
              refine ⟨18169923287443065177471221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48453128766514840473256589 18169923287443065177471221)
              ·
                refine ⟨1703430308197787360387927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18169923287443065177471221 1703430308197787360387927)
                ·
                  refine ⟨2555145462296681040581891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703430308197787360387927 2555145462296681040581891)
                  ·
                    refine ⟨3832718193445021560872837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2555145462296681040581891 3832718193445021560872837)
                    ·
                      refine ⟨718634661270941542663657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3832718193445021560872837 718634661270941542663657)
                      ·
                        rfl

theorem cell23_1399536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_1399536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399536 prefixEnd_1399536 := by exact prefixLift 1399536
  have htrace : WordTrace (prefixWord ++ tailWord_1399536) baseStart_1399536 baseEnd_1399536 := by
    simpa [prefixWord, tailWord_1399536, baseEnd_1399536] using wordTrace_append hprefix tailTrace_1399536
  have hstable : (prefixWord ++ tailWord_1399536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399536).length < 2 ^ (prefixWord ++ tailWord_1399536).sum := by decide
  have hdescent : baseEnd_1399536 < baseStart_1399536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399541 : List Nat := [1, 3, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1399541 : Nat := 118140960795 + 1399541 * 2 ^ 59
def prefixEnd_1399541 : Nat := 4983230072969 + 3 ^ 40 * 1399541 * 2
def baseEnd_1399541 : Nat := 239545742891404674367045

theorem tailTrace_1399541 : CollatzResearch.WordTrace tailWord_1399541 prefixEnd_1399541 239545742891404674367045 := by
  unfold tailWord_1399541
  simp only [CollatzResearch.WordTrace]
  refine ⟨51045453822709454418350477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34030302548472969612233651 51045453822709454418350477)
  ·
    refine ⟨19142045183516045406881429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51045453822709454418350477 19142045183516045406881429)
    ·
      refine ⟨897283367977314628447567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19142045183516045406881429 897283367977314628447567)
      ·
        refine ⟨1345925051965971942671351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897283367977314628447567 1345925051965971942671351)
        ·
          refine ⟨2018887577948957914007027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345925051965971942671351 2018887577948957914007027)
          ·
            refine ⟨3028331366923436871010541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018887577948957914007027 3028331366923436871010541)
            ·
              refine ⟨1135624262596288826628953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3028331366923436871010541 1135624262596288826628953)
              ·
                refine ⟨851718196947216619971715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1135624262596288826628953 851718196947216619971715)
                ·
                  refine ⟨1277577295420824929957573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851718196947216619971715 1277577295420824929957573)
                  ·
                    refine ⟨239545742891404674367045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277577295420824929957573 239545742891404674367045)
                    ·
                      rfl

theorem cell23_1399541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1399541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399541 prefixEnd_1399541 := by exact prefixLift 1399541
  have htrace : WordTrace (prefixWord ++ tailWord_1399541) baseStart_1399541 baseEnd_1399541 := by
    simpa [prefixWord, tailWord_1399541, baseEnd_1399541] using wordTrace_append hprefix tailTrace_1399541
  have hstable : (prefixWord ++ tailWord_1399541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399541).length < 2 ^ (prefixWord ++ tailWord_1399541).sum := by decide
  have hdescent : baseEnd_1399541 < baseStart_1399541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399546 : List Nat := [3, 1, 1, 1, 1, 3, 4, 1, 4, 4]
def baseStart_1399546 : Nat := 118140960795 + 1399546 * 2 ^ 59
def prefixEnd_1399546 : Nat := 4983230072969 + 3 ^ 40 * 1399546 * 2
def baseEnd_1399546 : Nat := 239546598692495501179537

theorem tailTrace_1399546 : CollatzResearch.WordTrace tailWord_1399546 prefixEnd_1399546 239546598692495501179537 := by
  unfold tailWord_1399546
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761409046922835068070623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34030424125127560181521661 12761409046922835068070623)
  ·
    refine ⟨19142113570384252602105935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12761409046922835068070623 19142113570384252602105935)
    ·
      refine ⟨28713170355576378903158903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19142113570384252602105935 28713170355576378903158903)
      ·
        refine ⟨43069755533364568354738355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28713170355576378903158903 43069755533364568354738355)
        ·
          refine ⟨64604633300046852532107533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43069755533364568354738355 64604633300046852532107533)
          ·
            refine ⟨24226737487517569699540325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64604633300046852532107533 24226737487517569699540325)
            ·
              refine ⟨4542513278909544318663811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24226737487517569699540325 4542513278909544318663811)
              ·
                refine ⟨6813769918364316477995717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542513278909544318663811 6813769918364316477995717)
                ·
                  refine ⟨1277581859693309339624197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6813769918364316477995717 1277581859693309339624197)
                  ·
                    refine ⟨239546598692495501179537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277581859693309339624197 239546598692495501179537)
                    ·
                      rfl

theorem cell23_1399546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_1399546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399546 prefixEnd_1399546 := by exact prefixLift 1399546
  have htrace : WordTrace (prefixWord ++ tailWord_1399546) baseStart_1399546 baseEnd_1399546 := by
    simpa [prefixWord, tailWord_1399546, baseEnd_1399546] using wordTrace_append hprefix tailTrace_1399546
  have hstable : (prefixWord ++ tailWord_1399546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399546).length < 2 ^ (prefixWord ++ tailWord_1399546).sum := by decide
  have hdescent : baseEnd_1399546 < baseStart_1399546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399549 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1399549 : Nat := 118140960795 + 1399549 * 2 ^ 59
def prefixEnd_1399549 : Nat := 4983230072969 + 3 ^ 40 * 1399549 * 2
def baseEnd_1399549 : Nat := 718641336519449991801097

theorem tailTrace_1399549 : CollatzResearch.WordTrace tailWord_1399549 prefixEnd_1399549 718641336519449991801097 := by
  unfold tailWord_1399549
  simp only [CollatzResearch.WordTrace]
  refine ⟨51045745606680471784641701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34030497071120314523094467 51045745606680471784641701)
  ·
    refine ⟨9571077301252588459620319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51045745606680471784641701 9571077301252588459620319)
    ·
      refine ⟨14356615951878882689430479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571077301252588459620319 14356615951878882689430479)
      ·
        refine ⟨21534923927818324034145719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14356615951878882689430479 21534923927818324034145719)
        ·
          refine ⟨32302385891727486051218579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21534923927818324034145719 32302385891727486051218579)
          ·
            refine ⟨48453578837591229076827869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32302385891727486051218579 48453578837591229076827869)
            ·
              refine ⟨18170092064096710903810451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48453578837591229076827869 18170092064096710903810451)
              ·
                refine ⟨27255138096145066355715677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18170092064096710903810451 27255138096145066355715677)
                ·
                  refine ⟨10220676786054399883393379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27255138096145066355715677 10220676786054399883393379)
                  ·
                    refine ⟨15331015179081599825090069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10220676786054399883393379 15331015179081599825090069)
                    ·
                      refine ⟨718641336519449991801097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15331015179081599825090069 718641336519449991801097)
                      ·
                        rfl

theorem cell23_1399549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1399549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399549 prefixEnd_1399549 := by exact prefixLift 1399549
  have htrace : WordTrace (prefixWord ++ tailWord_1399549) baseStart_1399549 baseEnd_1399549 := by
    simpa [prefixWord, tailWord_1399549, baseEnd_1399549] using wordTrace_append hprefix tailTrace_1399549
  have hstable : (prefixWord ++ tailWord_1399549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399549).length < 2 ^ (prefixWord ++ tailWord_1399549).sum := by decide
  have hdescent : baseEnd_1399549 < baseStart_1399549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399556 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1399556 : Nat := 118140960795 + 1399556 * 2 ^ 59
def prefixEnd_1399556 : Nat := 4983230072969 + 3 ^ 40 * 1399556 * 2
def baseEnd_1399556 : Nat := 718644930884031464413565

theorem tailTrace_1399556 : CollatzResearch.WordTrace tailWord_1399556 prefixEnd_1399556 718644930884031464413565 := by
  unfold tailWord_1399556
  simp only [CollatzResearch.WordTrace]
  refine ⟨25523000458827555990073261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34030667278436741320097681 25523000458827555990073261)
  ·
    refine ⟨9571125172060333496277473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25523000458827555990073261 9571125172060333496277473)
    ·
      refine ⟨7178343879045250122208105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9571125172060333496277473 7178343879045250122208105)
      ·
        refine ⟨5383757909283937591656079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7178343879045250122208105 5383757909283937591656079)
        ·
          refine ⟨8075636863925906387484119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5383757909283937591656079 8075636863925906387484119)
          ·
            refine ⟨12113455295888859581226179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8075636863925906387484119 12113455295888859581226179)
            ·
              refine ⟨18170182943833289371839269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12113455295888859581226179 18170182943833289371839269)
              ·
                refine ⟨3406909301968741757219863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18170182943833289371839269 3406909301968741757219863)
                ·
                  refine ⟨5110363952953112635829795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406909301968741757219863 5110363952953112635829795)
                  ·
                    refine ⟨7665545929429668953744693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5110363952953112635829795 7665545929429668953744693)
                    ·
                      refine ⟨718644930884031464413565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7665545929429668953744693 718644930884031464413565)
                      ·
                        rfl

theorem cell23_1399556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1399556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399556 prefixEnd_1399556 := by exact prefixLift 1399556
  have htrace : WordTrace (prefixWord ++ tailWord_1399556) baseStart_1399556 baseEnd_1399556 := by
    simpa [prefixWord, tailWord_1399556, baseEnd_1399556] using wordTrace_append hprefix tailTrace_1399556
  have hstable : (prefixWord ++ tailWord_1399556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399556).length < 2 ^ (prefixWord ++ tailWord_1399556).sum := by decide
  have hdescent : baseEnd_1399556 < baseStart_1399556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399566 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1399566 : Nat := 118140960795 + 1399566 * 2 ^ 59
def prefixEnd_1399566 : Nat := 4983230072969 + 3 ^ 40 * 1399566 * 2
def baseEnd_1399566 : Nat := 718650065690576425288519

theorem tailTrace_1399566 : CollatzResearch.WordTrace tailWord_1399566 prefixEnd_1399566 718650065690576425288519 := by
  unfold tailWord_1399566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6380795705952360461001319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34030910431745922458673701 6380795705952360461001319)
  ·
    refine ⟨9571193558928540691501979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6380795705952360461001319 9571193558928540691501979)
    ·
      refine ⟨14356790338392811037252969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571193558928540691501979 14356790338392811037252969)
      ·
        refine ⟨10767592753794608277939727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14356790338392811037252969 10767592753794608277939727)
        ·
          refine ⟨16151389130691912416909591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10767592753794608277939727 16151389130691912416909591)
          ·
            refine ⟨24227083696037868625364387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16151389130691912416909591 24227083696037868625364387)
            ·
              refine ⟨36340625544056802938046581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24227083696037868625364387 36340625544056802938046581)
              ·
                refine ⟨3406933644755325275441867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36340625544056802938046581 3406933644755325275441867)
                ·
                  refine ⟨5110400467132987913162801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3406933644755325275441867 5110400467132987913162801)
                  ·
                    refine ⟨3832800350349740934872101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5110400467132987913162801 3832800350349740934872101)
                    ·
                      refine ⟨718650065690576425288519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3832800350349740934872101 718650065690576425288519)
                      ·
                        rfl

theorem cell23_1399566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1399566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399566 prefixEnd_1399566 := by exact prefixLift 1399566
  have htrace : WordTrace (prefixWord ++ tailWord_1399566) baseStart_1399566 baseEnd_1399566 := by
    simpa [prefixWord, tailWord_1399566, baseEnd_1399566] using wordTrace_append hprefix tailTrace_1399566
  have hstable : (prefixWord ++ tailWord_1399566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399566).length < 2 ^ (prefixWord ++ tailWord_1399566).sum := by decide
  have hdescent : baseEnd_1399566 < baseStart_1399566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399570 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1399570 : Nat := 118140960795 + 1399570 * 2 ^ 59
def prefixEnd_1399570 : Nat := 4983230072969 + 3 ^ 40 * 1399570 * 2
def baseEnd_1399570 : Nat := 718652119613194409638501

theorem tailTrace_1399570 : CollatzResearch.WordTrace tailWord_1399570 prefixEnd_1399570 718652119613194409638501 := by
  unfold tailWord_1399570
  simp only [CollatzResearch.WordTrace]
  refine ⟨12761627884901098092789041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34031007693069594914104109 12761627884901098092789041)
  ·
    refine ⟨9571220913675823569591781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12761627884901098092789041 9571220913675823569591781)
    ·
      refine ⟨1794603921314216919298459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9571220913675823569591781 1794603921314216919298459)
      ·
        refine ⟨2691905881971325378947689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794603921314216919298459 2691905881971325378947689)
        ·
          refine ⟨2018929411478494034210767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2691905881971325378947689 2018929411478494034210767)
          ·
            refine ⟨3028394117217741051316151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2018929411478494034210767 3028394117217741051316151)
            ·
              refine ⟨4542591175826611576974227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028394117217741051316151 4542591175826611576974227)
              ·
                refine ⟨6813886763739917365461341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542591175826611576974227 6813886763739917365461341)
                ·
                  refine ⟨2555207536402469012048003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6813886763739917365461341 2555207536402469012048003)
                  ·
                    refine ⟨3832811304603703518072005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2555207536402469012048003 3832811304603703518072005)
                    ·
                      refine ⟨718652119613194409638501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3832811304603703518072005 718652119613194409638501)
                      ·
                        rfl

theorem cell23_1399570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1399570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399570 prefixEnd_1399570 := by exact prefixLift 1399570
  have htrace : WordTrace (prefixWord ++ tailWord_1399570) baseStart_1399570 baseEnd_1399570 := by
    simpa [prefixWord, tailWord_1399570, baseEnd_1399570] using wordTrace_append hprefix tailTrace_1399570
  have hstable : (prefixWord ++ tailWord_1399570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399570).length < 2 ^ (prefixWord ++ tailWord_1399570).sum := by decide
  have hdescent : baseEnd_1399570 < baseStart_1399570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399660 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 4, 2, 2]
def baseStart_1399660 : Nat := 118140960795 + 1399660 * 2 ^ 59
def prefixEnd_1399660 : Nat := 4983230072969 + 3 ^ 40 * 1399660 * 2
def baseEnd_1399660 : Nat := 718698332872099057513087

theorem tailTrace_1399660 : CollatzResearch.WordTrace tailWord_1399660 prefixEnd_1399660 718698332872099057513087 := by
  unfold tailWord_1399660
  simp only [CollatzResearch.WordTrace]
  refine ⟨25524897054639168870966217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34033196072852225161288289 25524897054639168870966217)
  ·
    refine ⟨19143672790979376653224663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25524897054639168870966217 19143672790979376653224663)
    ·
      refine ⟨28715509186469064979836995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19143672790979376653224663 28715509186469064979836995)
      ·
        refine ⟨43073263779703597469755493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28715509186469064979836995 43073263779703597469755493)
        ·
          refine ⟨8076236958694424525579155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43073263779703597469755493 8076236958694424525579155)
          ·
            refine ⟨12114355438041636788368733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076236958694424525579155 12114355438041636788368733)
            ·
              refine ⟨4542883289265613795638275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12114355438041636788368733 4542883289265613795638275)
              ·
                refine ⟨6814324933898420693457413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4542883289265613795638275 6814324933898420693457413)
                ·
                  refine ⟨1277685925105953880023265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6814324933898420693457413 1277685925105953880023265)
                  ·
                    refine ⟨958264443829465410017449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1277685925105953880023265 958264443829465410017449)
                    ·
                      refine ⟨718698332872099057513087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958264443829465410017449 718698332872099057513087)
                      ·
                        rfl

theorem cell23_1399660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_1399660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399660 prefixEnd_1399660 := by exact prefixLift 1399660
  have htrace : WordTrace (prefixWord ++ tailWord_1399660) baseStart_1399660 baseEnd_1399660 := by
    simpa [prefixWord, tailWord_1399660, baseEnd_1399660] using wordTrace_append hprefix tailTrace_1399660
  have hstable : (prefixWord ++ tailWord_1399660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399660).length < 2 ^ (prefixWord ++ tailWord_1399660).sum := by decide
  have hdescent : baseEnd_1399660 < baseStart_1399660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399666 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 7]
def baseStart_1399666 : Nat := 118140960795 + 1399666 * 2 ^ 59
def prefixEnd_1399666 : Nat := 4983230072969 + 3 ^ 40 * 1399666 * 2
def baseEnd_1399666 : Nat := 79855712639558448226451

theorem tailTrace_1399666 : CollatzResearch.WordTrace tailWord_1399666 prefixEnd_1399666 79855712639558448226451 := by
  unfold tailWord_1399666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762503236814150191662713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34033341964837733844433901 12762503236814150191662713)
  ·
    refine ⟨9571877427610612643747035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12762503236814150191662713 9571877427610612643747035)
    ·
      refine ⟨14357816141415918965620553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571877427610612643747035 14357816141415918965620553)
      ·
        refine ⟨10768362106061939224215415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14357816141415918965620553 10768362106061939224215415)
        ·
          refine ⟨16152543159092908836323123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10768362106061939224215415 16152543159092908836323123)
          ·
            refine ⟨24228814738639363254484685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16152543159092908836323123 24228814738639363254484685)
            ·
              refine ⟨9085805526989761220431757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24228814738639363254484685 9085805526989761220431757)
              ·
                refine ⟨3407177072621160457661909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9085805526989761220431757 3407177072621160457661909)
                ·
                  refine ⟨79855712639558448226451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3407177072621160457661909 79855712639558448226451)
                  ·
                    rfl

theorem cell23_1399666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_1399666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399666 prefixEnd_1399666 := by exact prefixLift 1399666
  have htrace : WordTrace (prefixWord ++ tailWord_1399666) baseStart_1399666 baseEnd_1399666 := by
    simpa [prefixWord, tailWord_1399666, baseEnd_1399666] using wordTrace_append hprefix tailTrace_1399666
  have hstable : (prefixWord ++ tailWord_1399666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399666).length < 2 ^ (prefixWord ++ tailWord_1399666).sum := by decide
  have hdescent : baseEnd_1399666 < baseStart_1399666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399713 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 4, 5]
def baseStart_1399713 : Nat := 118140960795 + 1399713 * 2 ^ 59
def prefixEnd_1399713 : Nat := 4983230072969 + 3 ^ 40 * 1399713 * 2
def baseEnd_1399713 : Nat := 239575182448929116716781

theorem tailTrace_1399713 : CollatzResearch.WordTrace tailWord_1399713 prefixEnd_1399713 239575182448929116716781 := by
  unfold tailWord_1399713
  simp only [CollatzResearch.WordTrace]
  refine ⟨51051727178086327793611793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34034484785390885195741195 51051727178086327793611793)
  ·
    refine ⟨38288795383564745845208845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51051727178086327793611793 38288795383564745845208845)
    ·
      refine ⟨14358298268836779691953317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38288795383564745845208845 14358298268836779691953317)
      ·
        refine ⟨2692180925406896192241247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14358298268836779691953317 2692180925406896192241247)
        ·
          refine ⟨4038271388110344288361871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692180925406896192241247 4038271388110344288361871)
          ·
            refine ⟨6057407082165516432542807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038271388110344288361871 6057407082165516432542807)
            ·
              refine ⟨9086110623248274648814211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057407082165516432542807 9086110623248274648814211)
              ·
                refine ⟨13629165934872411973221317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9086110623248274648814211 13629165934872411973221317)
                ·
                  refine ⟨2555468612788577244978997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13629165934872411973221317 2555468612788577244978997)
                  ·
                    refine ⟨239575182448929116716781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2555468612788577244978997 239575182448929116716781)
                    ·
                      rfl

theorem cell23_1399713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_1399713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399713 prefixEnd_1399713 := by exact prefixLift 1399713
  have htrace : WordTrace (prefixWord ++ tailWord_1399713) baseStart_1399713 baseEnd_1399713 := by
    simpa [prefixWord, tailWord_1399713, baseEnd_1399713] using wordTrace_append hprefix tailTrace_1399713
  have hstable : (prefixWord ++ tailWord_1399713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399713).length < 2 ^ (prefixWord ++ tailWord_1399713).sum := by decide
  have hdescent : baseEnd_1399713 < baseStart_1399713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399733 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1399733 : Nat := 118140960795 + 1399733 * 2 ^ 59
def prefixEnd_1399733 : Nat := 4983230072969 + 3 ^ 40 * 1399733 * 2
def baseEnd_1399733 : Nat := 718735816959877271900251

theorem tailTrace_1399733 : CollatzResearch.WordTrace tailWord_1399733 prefixEnd_1399733 718735816959877271900251 := by
  unfold tailWord_1399733
  simp only [CollatzResearch.WordTrace]
  refine ⟨51052456638013871209339853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34034971092009247472893235 51052456638013871209339853)
  ·
    refine ⟨19144671239255201703502445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51052456638013871209339853 19144671239255201703502445)
    ·
      refine ⟨7179251714720700638813417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19144671239255201703502445 7179251714720700638813417)
      ·
        refine ⟨5384438786040525479110063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7179251714720700638813417 5384438786040525479110063)
        ·
          refine ⟨8076658179060788218665095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5384438786040525479110063 8076658179060788218665095)
          ·
            refine ⟨12114987268591182327997643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8076658179060788218665095 12114987268591182327997643)
            ·
              refine ⟨18172480902886773491996465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12114987268591182327997643 18172480902886773491996465)
              ·
                refine ⟨13629360677165080118997349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18172480902886773491996465 13629360677165080118997349)
                ·
                  refine ⟨2555505126968452522312003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13629360677165080118997349 2555505126968452522312003)
                  ·
                    refine ⟨3833257690452678783468005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2555505126968452522312003 3833257690452678783468005)
                    ·
                      refine ⟨718735816959877271900251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3833257690452678783468005 718735816959877271900251)
                      ·
                        rfl

theorem cell23_1399733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1399733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399733 prefixEnd_1399733 := by exact prefixLift 1399733
  have htrace : WordTrace (prefixWord ++ tailWord_1399733) baseStart_1399733 baseEnd_1399733 := by
    simpa [prefixWord, tailWord_1399733, baseEnd_1399733] using wordTrace_append hprefix tailTrace_1399733
  have hstable : (prefixWord ++ tailWord_1399733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399733).length < 2 ^ (prefixWord ++ tailWord_1399733).sum := by decide
  have hdescent : baseEnd_1399733 < baseStart_1399733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399760 : List Nat := [2, 1, 1, 1, 1, 2, 3, 7, 1, 4]
def baseStart_1399760 : Nat := 118140960795 + 1399760 * 2 ^ 59
def prefixEnd_1399760 : Nat := 4983230072969 + 3 ^ 40 * 1399760 * 2
def baseEnd_1399760 : Nat := 239583226979182888754209

theorem tailTrace_1399760 : CollatzResearch.WordTrace tailWord_1399760 prefixEnd_1399760 239583226979182888754209 := by
  unfold tailWord_1399760
  simp only [CollatzResearch.WordTrace]
  refine ⟨25526720704458027410286367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34035627605944036547048489 25526720704458027410286367)
  ·
    refine ⟨38290081056687041115429551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25526720704458027410286367 38290081056687041115429551)
    ·
      refine ⟨57435121585030561673144327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38290081056687041115429551 57435121585030561673144327)
      ·
        refine ⟨86152682377545842509716491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57435121585030561673144327 86152682377545842509716491)
        ·
          refine ⟨129229023566318763764574737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86152682377545842509716491 129229023566318763764574737)
          ·
            refine ⟨96921767674739072823431053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129229023566318763764574737 96921767674739072823431053)
            ·
              refine ⟨36345662878027152308786645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96921767674739072823431053 36345662878027152308786645)
              ·
                refine ⟨851851473703761382237187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 36345662878027152308786645 851851473703761382237187)
                ·
                  refine ⟨1277777210555642073355781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 851851473703761382237187 1277777210555642073355781)
                  ·
                    refine ⟨239583226979182888754209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1277777210555642073355781 239583226979182888754209)
                    ·
                      rfl

theorem cell23_1399760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 7, 1, 4].length) (baseStart_1399760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399760 prefixEnd_1399760 := by exact prefixLift 1399760
  have htrace : WordTrace (prefixWord ++ tailWord_1399760) baseStart_1399760 baseEnd_1399760 := by
    simpa [prefixWord, tailWord_1399760, baseEnd_1399760] using wordTrace_append hprefix tailTrace_1399760
  have hstable : (prefixWord ++ tailWord_1399760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399760).length < 2 ^ (prefixWord ++ tailWord_1399760).sum := by decide
  have hdescent : baseEnd_1399760 < baseStart_1399760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399770 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_1399770 : Nat := 118140960795 + 1399770 * 2 ^ 59
def prefixEnd_1399770 : Nat := 4983230072969 + 3 ^ 40 * 1399770 * 2
def baseEnd_1399770 : Nat := 718754815744093627137581

theorem tailTrace_1399770 : CollatzResearch.WordTrace tailWord_1399770 prefixEnd_1399770 718754815744093627137581 := by
  unfold tailWord_1399770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12763451534719956632109191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34035870759253217685624509 12763451534719956632109191)
  ·
    refine ⟨19145177302079934948163787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12763451534719956632109191 19145177302079934948163787)
    ·
      refine ⟨28717765953119902422245681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19145177302079934948163787 28717765953119902422245681)
      ·
        refine ⟨21538324464839926816684261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28717765953119902422245681 21538324464839926816684261)
        ·
          refine ⟨4038435837157486278128299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21538324464839926816684261 4038435837157486278128299)
          ·
            refine ⟨6057653755736229417192449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038435837157486278128299 6057653755736229417192449)
            ·
              refine ⟨4543240316802172062894337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6057653755736229417192449 4543240316802172062894337)
              ·
                refine ⟨3407430237601629047170753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4543240316802172062894337 3407430237601629047170753)
                ·
                  refine ⟨2555572678201221785378065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3407430237601629047170753 2555572678201221785378065)
                  ·
                    refine ⟨1916679508650916339033549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2555572678201221785378065 1916679508650916339033549)
                    ·
                      refine ⟨718754815744093627137581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1916679508650916339033549 718754815744093627137581)
                      ·
                        rfl

theorem cell23_1399770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_1399770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399770 prefixEnd_1399770 := by exact prefixLift 1399770
  have htrace : WordTrace (prefixWord ++ tailWord_1399770) baseStart_1399770 baseEnd_1399770 := by
    simpa [prefixWord, tailWord_1399770, baseEnd_1399770] using wordTrace_append hprefix tailTrace_1399770
  have hstable : (prefixWord ++ tailWord_1399770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399770).length < 2 ^ (prefixWord ++ tailWord_1399770).sum := by decide
  have hdescent : baseEnd_1399770 < baseStart_1399770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399803 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 1, 5]
def baseStart_1399803 : Nat := 118140960795 + 1399803 * 2 ^ 59
def prefixEnd_1399803 : Nat := 4983230072969 + 3 ^ 40 * 1399803 * 2
def baseEnd_1399803 : Nat := 239590586868563999341643

theorem tailTrace_1399803 : CollatzResearch.WordTrace tailWord_1399803 prefixEnd_1399803 239590586868563999341643 := by
  unfold tailWord_1399803
  simp only [CollatzResearch.WordTrace]
  refine ⟨51055009747760273164388063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34036673165173515442925375 51055009747760273164388063)
  ·
    refine ⟨76582514621640409746582095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51055009747760273164388063 76582514621640409746582095)
    ·
      refine ⟨114873771932460614619873143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76582514621640409746582095 114873771932460614619873143)
      ·
        refine ⟨172310657898690921929809715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114873771932460614619873143 172310657898690921929809715)
        ·
          refine ⟨258465986848036382894714573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172310657898690921929809715 258465986848036382894714573)
          ·
            refine ⟨96924745068013643585517965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258465986848036382894714573 96924745068013643585517965)
            ·
              refine ⟨36346779400505116344569237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96924745068013643585517965 36346779400505116344569237)
              ·
                refine ⟨1703755284398677328651683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36346779400505116344569237 1703755284398677328651683)
                ·
                  refine ⟨2555632926598015992977525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703755284398677328651683 2555632926598015992977525)
                  ·
                    refine ⟨239590586868563999341643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2555632926598015992977525 239590586868563999341643)
                    ·
                      rfl

theorem cell23_1399803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 5].length) (baseStart_1399803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399803 prefixEnd_1399803 := by exact prefixLift 1399803
  have htrace : WordTrace (prefixWord ++ tailWord_1399803) baseStart_1399803 baseEnd_1399803 := by
    simpa [prefixWord, tailWord_1399803, baseEnd_1399803] using wordTrace_append hprefix tailTrace_1399803
  have hstable : (prefixWord ++ tailWord_1399803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399803).length < 2 ^ (prefixWord ++ tailWord_1399803).sum := by decide
  have hdescent : baseEnd_1399803 < baseStart_1399803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399820 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_1399820 : Nat := 118140960795 + 1399820 * 2 ^ 59
def prefixEnd_1399820 : Nat := 4983230072969 + 3 ^ 40 * 1399820 * 2
def baseEnd_1399820 : Nat := 239593496592272810504117

theorem tailTrace_1399820 : CollatzResearch.WordTrace tailWord_1399820 prefixEnd_1399820 239593496592272810504117 := by
  unfold tailWord_1399820
  simp only [CollatzResearch.WordTrace]
  refine ⟨25527814894349342533878457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34037086525799123378504609 25527814894349342533878457)
  ·
    refine ⟨19145861170762006900408843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25527814894349342533878457 19145861170762006900408843)
    ·
      refine ⟨28718791756143010350613265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19145861170762006900408843 28718791756143010350613265)
      ·
        refine ⟨21539093817107257762959949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28718791756143010350613265 21539093817107257762959949)
        ·
          refine ⟨8077160181415221661109981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21539093817107257762959949 8077160181415221661109981)
          ·
            refine ⟨3028935068030708122916243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8077160181415221661109981 3028935068030708122916243)
            ·
              refine ⟨4543402602046062184374365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3028935068030708122916243 4543402602046062184374365)
              ·
                refine ⟨1703775975767273319140387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4543402602046062184374365 1703775975767273319140387)
                ·
                  refine ⟨2555663963650909978710581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1703775975767273319140387 2555663963650909978710581)
                  ·
                    refine ⟨239593496592272810504117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2555663963650909978710581 239593496592272810504117)
                    ·
                      rfl

theorem cell23_1399820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_1399820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399820 prefixEnd_1399820 := by exact prefixLift 1399820
  have htrace : WordTrace (prefixWord ++ tailWord_1399820) baseStart_1399820 baseEnd_1399820 := by
    simpa [prefixWord, tailWord_1399820, baseEnd_1399820] using wordTrace_append hprefix tailTrace_1399820
  have hstable : (prefixWord ++ tailWord_1399820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399820).length < 2 ^ (prefixWord ++ tailWord_1399820).sum := by decide
  have hdescent : baseEnd_1399820 < baseStart_1399820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399843 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1399843 : Nat := 118140960795 + 1399843 * 2 ^ 59
def prefixEnd_1399843 : Nat := 4983230072969 + 3 ^ 40 * 1399843 * 2
def baseEnd_1399843 : Nat := 718792299831871841524745

theorem tailTrace_1399843 : CollatzResearch.WordTrace tailWord_1399843 prefixEnd_1399843 718792299831871841524745 := by
  unfold tailWord_1399843
  simp only [CollatzResearch.WordTrace]
  refine ⟨51056468667615359995844183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34037645778410239997229455 51056468667615359995844183)
  ·
    refine ⟨76584703001423039993766275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51056468667615359995844183 76584703001423039993766275)
    ·
      refine ⟨114877054502134559990649413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76584703001423039993766275 114877054502134559990649413)
      ·
        refine ⟨21539447719150229998246765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114877054502134559990649413 21539447719150229998246765)
        ·
          refine ⟨8077292894681336249342537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21539447719150229998246765 8077292894681336249342537)
          ·
            refine ⟨6057969671011002187006903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8077292894681336249342537 6057969671011002187006903)
            ·
              refine ⟨9086954506516503280510355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6057969671011002187006903 9086954506516503280510355)
              ·
                refine ⟨13630431759774754920765533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9086954506516503280510355 13630431759774754920765533)
                ·
                  refine ⟨5111411909915533095287075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13630431759774754920765533 5111411909915533095287075)
                  ·
                    refine ⟨7667117864873299642930613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5111411909915533095287075 7667117864873299642930613)
                    ·
                      refine ⟨718792299831871841524745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7667117864873299642930613 718792299831871841524745)
                      ·
                        rfl

theorem cell23_1399843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1399843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399843 prefixEnd_1399843 := by exact prefixLift 1399843
  have htrace : WordTrace (prefixWord ++ tailWord_1399843) baseStart_1399843 baseEnd_1399843 := by
    simpa [prefixWord, tailWord_1399843, baseEnd_1399843] using wordTrace_append hprefix tailTrace_1399843
  have hstable : (prefixWord ++ tailWord_1399843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399843).length < 2 ^ (prefixWord ++ tailWord_1399843).sum := by decide
  have hdescent : baseEnd_1399843 < baseStart_1399843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399857 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 3, 2, 2]
def baseStart_1399857 : Nat := 118140960795 + 1399857 * 2 ^ 59
def prefixEnd_1399857 : Nat := 4983230072969 + 3 ^ 40 * 1399857 * 2
def baseEnd_1399857 : Nat := 718799488561034786749681

theorem tailTrace_1399857 : CollatzResearch.WordTrace tailWord_1399857 prefixEnd_1399857 718799488561034786749681 := by
  unfold tailWord_1399857
  simp only [CollatzResearch.WordTrace]
  refine ⟨51056979289564640386853825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34037986193043093591235883 51056979289564640386853825)
  ·
    refine ⟨38292734467173480290140369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51056979289564640386853825 38292734467173480290140369)
    ·
      refine ⟨28719550850380110217605277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38292734467173480290140369 28719550850380110217605277)
      ·
        refine ⟨10769831568892541331601979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28719550850380110217605277 10769831568892541331601979)
        ·
          refine ⟨16154747353338811997402969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10769831568892541331601979 16154747353338811997402969)
          ·
            refine ⟨12116060515004108998052227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16154747353338811997402969 12116060515004108998052227)
            ·
              refine ⟨18174090772506163497078341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12116060515004108998052227 18174090772506163497078341)
              ·
                refine ⟨3407642019844905655702189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18174090772506163497078341 3407642019844905655702189)
                ·
                  refine ⟨1277865757441839620888321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3407642019844905655702189 1277865757441839620888321)
                  ·
                    refine ⟨958399318081379715666241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1277865757441839620888321 958399318081379715666241)
                    ·
                      refine ⟨718799488561034786749681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958399318081379715666241 718799488561034786749681)
                      ·
                        rfl

theorem cell23_1399857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_1399857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399857 prefixEnd_1399857 := by exact prefixLift 1399857
  have htrace : WordTrace (prefixWord ++ tailWord_1399857) baseStart_1399857 baseEnd_1399857 := by
    simpa [prefixWord, tailWord_1399857, baseEnd_1399857] using wordTrace_append hprefix tailTrace_1399857
  have hstable : (prefixWord ++ tailWord_1399857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399857).length < 2 ^ (prefixWord ++ tailWord_1399857).sum := by decide
  have hdescent : baseEnd_1399857 < baseStart_1399857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399893 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_1399893 : Nat := 118140960795 + 1399893 * 2 ^ 59
def prefixEnd_1399893 : Nat := 4983230072969 + 3 ^ 40 * 1399893 * 2
def baseEnd_1399893 : Nat := 239605991288198881966505

theorem tailTrace_1399893 : CollatzResearch.WordTrace tailWord_1399893 prefixEnd_1399893 239605991288198881966505 := by
  unfold tailWord_1399893
  simp only [CollatzResearch.WordTrace]
  refine ⟨51058292317434218535164333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34038861544956145690109555 51058292317434218535164333)
  ·
    refine ⟨19146859619037831950686625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51058292317434218535164333 19146859619037831950686625)
    ·
      refine ⟨14360144714278373963014969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19146859619037831950686625 14360144714278373963014969)
      ·
        refine ⟨10770108535708780472261227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14360144714278373963014969 10770108535708780472261227)
        ·
          refine ⟨16155162803563170708391841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10770108535708780472261227 16155162803563170708391841)
          ·
            refine ⟨12116372102672378031293881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16155162803563170708391841 12116372102672378031293881)
            ·
              refine ⟨9087279077004283523470411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12116372102672378031293881 9087279077004283523470411)
              ·
                refine ⟨13630918615506425285205617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9087279077004283523470411 13630918615506425285205617)
                ·
                  refine ⟨10223188961629818963904213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13630918615506425285205617 10223188961629818963904213)
                  ·
                    refine ⟨239605991288198881966505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10223188961629818963904213 239605991288198881966505)
                    ·
                      rfl

theorem cell23_1399893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_1399893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399893 prefixEnd_1399893 := by exact prefixLift 1399893
  have htrace : WordTrace (prefixWord ++ tailWord_1399893) baseStart_1399893 baseEnd_1399893 := by
    simpa [prefixWord, tailWord_1399893, baseEnd_1399893] using wordTrace_append hprefix tailTrace_1399893
  have hstable : (prefixWord ++ tailWord_1399893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399893).length < 2 ^ (prefixWord ++ tailWord_1399893).sum := by decide
  have hdescent : baseEnd_1399893 < baseStart_1399893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399943 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1399943 : Nat := 118140960795 + 1399943 * 2 ^ 59
def prefixEnd_1399943 : Nat := 4983230072969 + 3 ^ 40 * 1399943 * 2
def baseEnd_1399943 : Nat := 718843647897321450274285

theorem tailTrace_1399943 : CollatzResearch.WordTrace tailWord_1399943 prefixEnd_1399943 718843647897321450274285 := by
  unfold tailWord_1399943
  simp only [CollatzResearch.WordTrace]
  refine ⟨51060115967253077074484483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34040077311502051382989655 51060115967253077074484483)
  ·
    refine ⟨76590173950879615611726725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51060115967253077074484483 76590173950879615611726725)
    ·
      refine ⟨14360657615789927927198761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76590173950879615611726725 14360657615789927927198761)
      ·
        refine ⟨10770493211842445945399071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14360657615789927927198761 10770493211842445945399071)
        ·
          refine ⟨16155739817763668918098607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10770493211842445945399071 16155739817763668918098607)
          ·
            refine ⟨24233609726645503377147911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16155739817763668918098607 24233609726645503377147911)
            ·
              refine ⟨36350414589968255065721867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24233609726645503377147911 36350414589968255065721867)
              ·
                refine ⟨54525621884952382598582801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36350414589968255065721867 54525621884952382598582801)
                ·
                  refine ⟨40894216413714286948937101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54525621884952382598582801 40894216413714286948937101)
                  ·
                    refine ⟨15335331155142857605851413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40894216413714286948937101 15335331155142857605851413)
                    ·
                      refine ⟨718843647897321450274285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15335331155142857605851413 718843647897321450274285)
                      ·
                        rfl

theorem cell23_1399943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1399943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399943 prefixEnd_1399943 := by exact prefixLift 1399943
  have htrace : WordTrace (prefixWord ++ tailWord_1399943) baseStart_1399943 baseEnd_1399943 := by
    simpa [prefixWord, tailWord_1399943, baseEnd_1399943] using wordTrace_append hprefix tailTrace_1399943
  have hstable : (prefixWord ++ tailWord_1399943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399943).length < 2 ^ (prefixWord ++ tailWord_1399943).sum := by decide
  have hdescent : baseEnd_1399943 < baseStart_1399943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399947 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 4, 2, 2]
def baseStart_1399947 : Nat := 118140960795 + 1399947 * 2 ^ 59
def prefixEnd_1399947 : Nat := 4983230072969 + 3 ^ 40 * 1399947 * 2
def baseEnd_1399947 : Nat := 718845701819939434624267

theorem tailTrace_1399947 : CollatzResearch.WordTrace tailWord_1399947 prefixEnd_1399947 718845701819939434624267 := by
  unfold tailWord_1399947
  simp only [CollatzResearch.WordTrace]
  refine ⟨51060261859238585757630095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34040174572825723838420063 51060261859238585757630095)
  ·
    refine ⟨76590392788857878636445143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51060261859238585757630095 76590392788857878636445143)
    ·
      refine ⟨114885589183286817954667715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76590392788857878636445143 114885589183286817954667715)
      ·
        refine ⟨172328383774930226932001573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114885589183286817954667715 172328383774930226932001573)
        ·
          refine ⟨32311571957799417549750295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172328383774930226932001573 32311571957799417549750295)
          ·
            refine ⟨48467357936699126324625443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32311571957799417549750295 48467357936699126324625443)
            ·
              refine ⟨72701036905048689486938165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48467357936699126324625443 72701036905048689486938165)
              ·
                refine ⟨6815722209848314639400453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72701036905048689486938165 6815722209848314639400453)
                ·
                  refine ⟨1277947914346558994887585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6815722209848314639400453 1277947914346558994887585)
                  ·
                    refine ⟨958460935759919246165689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1277947914346558994887585 958460935759919246165689)
                    ·
                      refine ⟨718845701819939434624267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958460935759919246165689 718845701819939434624267)
                      ·
                        rfl

theorem cell23_1399947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 2, 2].length) (baseStart_1399947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399947 prefixEnd_1399947 := by exact prefixLift 1399947
  have htrace : WordTrace (prefixWord ++ tailWord_1399947) baseStart_1399947 baseEnd_1399947 := by
    simpa [prefixWord, tailWord_1399947, baseEnd_1399947] using wordTrace_append hprefix tailTrace_1399947
  have hstable : (prefixWord ++ tailWord_1399947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399947).length < 2 ^ (prefixWord ++ tailWord_1399947).sum := by decide
  have hdescent : baseEnd_1399947 < baseStart_1399947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399960 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1399960 : Nat := 118140960795 + 1399960 * 2 ^ 59
def prefixEnd_1399960 : Nat := 4983230072969 + 3 ^ 40 * 1399960 * 2
def baseEnd_1399960 : Nat := 718852377068447883761707

theorem tailTrace_1399960 : CollatzResearch.WordTrace tailWord_1399960 prefixEnd_1399960 718852377068447883761707 := by
  unfold tailWord_1399960
  simp only [CollatzResearch.WordTrace]
  refine ⟨25530368004095744488926667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34040490672127659318568889 25530368004095744488926667)
  ·
    refine ⟨38295552006143616733390001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25530368004095744488926667 38295552006143616733390001)
    ·
      refine ⟨28721664004607712550042501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38295552006143616733390001 28721664004607712550042501)
      ·
        refine ⟨5385312000863946103132969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28721664004607712550042501 5385312000863946103132969)
        ·
          refine ⟨4038984000647959577349727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5385312000863946103132969 4038984000647959577349727)
          ·
            refine ⟨6058476000971939366024591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038984000647959577349727 6058476000971939366024591)
            ·
              refine ⟨9087714001457909049036887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6058476000971939366024591 9087714001457909049036887)
              ·
                refine ⟨13631571002186863573555331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9087714001457909049036887 13631571002186863573555331)
                ·
                  refine ⟨20447356503280295360332997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13631571002186863573555331 20447356503280295360332997)
                  ·
                    refine ⟨3833879344365055380062437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20447356503280295360332997 3833879344365055380062437)
                    ·
                      refine ⟨718852377068447883761707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3833879344365055380062437 718852377068447883761707)
                      ·
                        rfl

theorem cell23_1399960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1399960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399960 prefixEnd_1399960 := by exact prefixLift 1399960
  have htrace : WordTrace (prefixWord ++ tailWord_1399960) baseStart_1399960 baseEnd_1399960 := by
    simpa [prefixWord, tailWord_1399960, baseEnd_1399960] using wordTrace_append hprefix tailTrace_1399960
  have hstable : (prefixWord ++ tailWord_1399960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399960).length < 2 ^ (prefixWord ++ tailWord_1399960).sum := by decide
  have hdescent : baseEnd_1399960 < baseStart_1399960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399964 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1399964 : Nat := 118140960795 + 1399964 * 2 ^ 59
def prefixEnd_1399964 : Nat := 4983230072969 + 3 ^ 40 * 1399964 * 2
def baseEnd_1399964 : Nat := 718854430991065868111689

theorem tailTrace_1399964 : CollatzResearch.WordTrace tailWord_1399964 prefixEnd_1399964 718854430991065868111689 := by
  unfold tailWord_1399964
  simp only [CollatzResearch.WordTrace]
  refine ⟨25530440950088498830499473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34040587933451331773999297 25530440950088498830499473)
  ·
    refine ⟨19147830712566374122874605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25530440950088498830499473 19147830712566374122874605)
    ·
      refine ⟨7180436517212390296077977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19147830712566374122874605 7180436517212390296077977)
      ·
        refine ⟨5385327387909292722058483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7180436517212390296077977 5385327387909292722058483)
        ·
          refine ⟨8077991081863939083087725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5385327387909292722058483 8077991081863939083087725)
          ·
            refine ⟨3029246655698977156157897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8077991081863939083087725 3029246655698977156157897)
            ·
              refine ⟨2271934991774232867118423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029246655698977156157897 2271934991774232867118423)
              ·
                refine ⟨3407902487661349300677635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2271934991774232867118423 3407902487661349300677635)
                ·
                  refine ⟨5111853731492023951016453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3407902487661349300677635 5111853731492023951016453)
                  ·
                    refine ⟨958472574654754490815585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5111853731492023951016453 958472574654754490815585)
                    ·
                      refine ⟨718854430991065868111689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958472574654754490815585 718854430991065868111689)
                      ·
                        rfl

theorem cell23_1399964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1399964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399964 prefixEnd_1399964 := by exact prefixLift 1399964
  have htrace : WordTrace (prefixWord ++ tailWord_1399964) baseStart_1399964 baseEnd_1399964 := by
    simpa [prefixWord, tailWord_1399964, baseEnd_1399964] using wordTrace_append hprefix tailTrace_1399964
  have hstable : (prefixWord ++ tailWord_1399964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399964).length < 2 ^ (prefixWord ++ tailWord_1399964).sum := by decide
  have hdescent : baseEnd_1399964 < baseStart_1399964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1399998 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_1399998 : Nat := 118140960795 + 1399998 * 2 ^ 59
def prefixEnd_1399998 : Nat := 4983230072969 + 3 ^ 40 * 1399998 * 2
def baseEnd_1399998 : Nat := 718871889333318735086533

theorem tailTrace_1399998 : CollatzResearch.WordTrace tailWord_1399998 prefixEnd_1399998 718871889333318735086533 := by
  unfold tailWord_1399998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382765247756727683467081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34041414654702547645157765 6382765247756727683467081)
  ·
    refine ⟨4787073935817545762600311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6382765247756727683467081 4787073935817545762600311)
    ·
      refine ⟨7180610903726318643900467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787073935817545762600311 7180610903726318643900467)
      ·
        refine ⟨10770916355589477965850701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7180610903726318643900467 10770916355589477965850701)
        ·
          refine ⟨4039093633346054237194013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10770916355589477965850701 4039093633346054237194013)
          ·
            refine ⟨1514660112504770338947755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4039093633346054237194013 1514660112504770338947755)
            ·
              refine ⟨2271990168757155508421633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514660112504770338947755 2271990168757155508421633)
              ·
                refine ⟨1703992626567866631316225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2271990168757155508421633 1703992626567866631316225)
                ·
                  refine ⟨1277994469925899973487169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1703992626567866631316225 1277994469925899973487169)
                  ·
                    refine ⟨958495852444424980115377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1277994469925899973487169 958495852444424980115377)
                    ·
                      refine ⟨718871889333318735086533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958495852444424980115377 718871889333318735086533)
                      ·
                        rfl

theorem cell23_1399998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_1399998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1399998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1399998 prefixEnd_1399998 := by exact prefixLift 1399998
  have htrace : WordTrace (prefixWord ++ tailWord_1399998) baseStart_1399998 baseEnd_1399998 := by
    simpa [prefixWord, tailWord_1399998, baseEnd_1399998] using wordTrace_append hprefix tailTrace_1399998
  have hstable : (prefixWord ++ tailWord_1399998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1399998).length < 2 ^ (prefixWord ++ tailWord_1399998).sum := by decide
  have hdescent : baseEnd_1399998 < baseStart_1399998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1399998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400057 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1400057 : Nat := 118140960795 + 1400057 * 2 ^ 59
def prefixEnd_1400057 : Nat := 4983230072969 + 3 ^ 40 * 1400057 * 2
def baseEnd_1400057 : Nat := 718902184691934004248761

theorem tailTrace_1400057 : CollatzResearch.WordTrace tailWord_1400057 prefixEnd_1400057 718902184691934004248761 := by
  unfold tailWord_1400057
  simp only [CollatzResearch.WordTrace]
  refine ⟨51064273888840074544134425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34042849259226716362756283 51064273888840074544134425)
  ·
    refine ⟨38298205416630055908100819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51064273888840074544134425 38298205416630055908100819)
    ·
      refine ⟨57447308124945083862151229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38298205416630055908100819 57447308124945083862151229)
      ·
        refine ⟨21542740546854406448306711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57447308124945083862151229 21542740546854406448306711)
        ·
          refine ⟨32314110820281609672460067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21542740546854406448306711 32314110820281609672460067)
          ·
            refine ⟨48471166230422414508690101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32314110820281609672460067 48471166230422414508690101)
            ·
              refine ⟨4544171834102101360189697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48471166230422414508690101 4544171834102101360189697)
              ·
                refine ⟨3408128875576576020142273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4544171834102101360189697 3408128875576576020142273)
                ·
                  refine ⟨2556096656682432015106705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3408128875576576020142273 2556096656682432015106705)
                  ·
                    refine ⟨1917072492511824011330029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2556096656682432015106705 1917072492511824011330029)
                    ·
                      refine ⟨718902184691934004248761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1917072492511824011330029 718902184691934004248761)
                      ·
                        rfl

theorem cell23_1400057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1400057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400057 prefixEnd_1400057 := by exact prefixLift 1400057
  have htrace : WordTrace (prefixWord ++ tailWord_1400057) baseStart_1400057 baseEnd_1400057 := by
    simpa [prefixWord, tailWord_1400057, baseEnd_1400057] using wordTrace_append hprefix tailTrace_1400057
  have hstable : (prefixWord ++ tailWord_1400057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400057).length < 2 ^ (prefixWord ++ tailWord_1400057).sum := by decide
  have hdescent : baseEnd_1400057 < baseStart_1400057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400120 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 5, 6]
def baseStart_1400120 : Nat := 118140960795 + 1400120 * 2 ^ 59
def prefixEnd_1400120 : Nat := 4983230072969 + 3 ^ 40 * 1400120 * 2
def baseEnd_1400120 : Nat := 239644844657722419253657

theorem tailTrace_1400120 : CollatzResearch.WordTrace tailWord_1400120 prefixEnd_1400120 239644844657722419253657 := by
  unfold tailWord_1400120
  simp only [CollatzResearch.WordTrace]
  refine ⟨25533285843805918151838907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34044381125074557535785209 25533285843805918151838907)
  ·
    refine ⟨38299928765708877227758361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25533285843805918151838907 38299928765708877227758361)
    ·
      refine ⟨28724946574281657920818771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38299928765708877227758361 28724946574281657920818771)
      ·
        refine ⟨43087419861422486881228157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28724946574281657920818771 43087419861422486881228157)
        ·
          refine ⟨16157782448033432580460559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43087419861422486881228157 16157782448033432580460559)
          ·
            refine ⟨24236673672050148870690839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16157782448033432580460559 24236673672050148870690839)
            ·
              refine ⟨36355010508075223306036259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24236673672050148870690839 36355010508075223306036259)
              ·
                refine ⟨54532515762112834959054389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36355010508075223306036259 54532515762112834959054389)
                ·
                  refine ⟨5112423352698078277411349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54532515762112834959054389 5112423352698078277411349)
                  ·
                    refine ⟨239644844657722419253657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5112423352698078277411349 239644844657722419253657)
                    ·
                      rfl

theorem cell23_1400120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_1400120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400120 prefixEnd_1400120 := by exact prefixLift 1400120
  have htrace : WordTrace (prefixWord ++ tailWord_1400120) baseStart_1400120 baseEnd_1400120 := by
    simpa [prefixWord, tailWord_1400120, baseEnd_1400120] using wordTrace_append hprefix tailTrace_1400120
  have hstable : (prefixWord ++ tailWord_1400120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400120).length < 2 ^ (prefixWord ++ tailWord_1400120).sum := by decide
  have hdescent : baseEnd_1400120 < baseStart_1400120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400127 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_1400127 : Nat := 118140960795 + 1400127 * 2 ^ 59
def prefixEnd_1400127 : Nat := 4983230072969 + 3 ^ 40 * 1400127 * 2
def baseEnd_1400127 : Nat := 718938128337748730373439

theorem tailTrace_1400127 : CollatzResearch.WordTrace tailWord_1400127 prefixEnd_1400127 718938128337748730373439 := by
  unfold tailWord_1400127
  simp only [CollatzResearch.WordTrace]
  refine ⟨51066826998586476499182635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34044551332390984332788423 51066826998586476499182635)
  ·
    refine ⟨76600240497879714748773953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51066826998586476499182635 76600240497879714748773953)
    ·
      refine ⟨57450180373409786061580465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76600240497879714748773953 57450180373409786061580465)
      ·
        refine ⟨43087635280057339546185349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57450180373409786061580465 43087635280057339546185349)
        ·
          refine ⟨8078931615010751164909753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43087635280057339546185349 8078931615010751164909753)
          ·
            refine ⟨6059198711258063373682315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8078931615010751164909753 6059198711258063373682315)
            ·
              refine ⟨9088798066887095060523473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6059198711258063373682315 9088798066887095060523473)
              ·
                refine ⟨6816598550165321295392605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9088798066887095060523473 6816598550165321295392605)
                ·
                  refine ⟨2556224456311995485772227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6816598550165321295392605 2556224456311995485772227)
                  ·
                    refine ⟨3834336684467993228658341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2556224456311995485772227 3834336684467993228658341)
                    ·
                      refine ⟨718938128337748730373439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3834336684467993228658341 718938128337748730373439)
                      ·
                        rfl

theorem cell23_1400127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_1400127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400127 prefixEnd_1400127 := by exact prefixLift 1400127
  have htrace : WordTrace (prefixWord ++ tailWord_1400127) baseStart_1400127 baseEnd_1400127 := by
    simpa [prefixWord, tailWord_1400127, baseEnd_1400127] using wordTrace_append hprefix tailTrace_1400127
  have hstable : (prefixWord ++ tailWord_1400127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400127).length < 2 ^ (prefixWord ++ tailWord_1400127).sum := by decide
  have hdescent : baseEnd_1400127 < baseStart_1400127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400147 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 3]
def baseStart_1400147 : Nat := 118140960795 + 1400147 * 2 ^ 59
def prefixEnd_1400147 : Nat := 4983230072969 + 3 ^ 40 * 1400147 * 2
def baseEnd_1400147 : Nat := 718948397950838652123347

theorem tailTrace_1400147 : CollatzResearch.WordTrace tailWord_1400147 prefixEnd_1400147 718948397950838652123347 := by
  unfold tailWord_1400147
  simp only [CollatzResearch.WordTrace]
  refine ⟨51067556458514019914910695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34045037639009346609940463 51067556458514019914910695)
  ·
    refine ⟨76601334687771029872366043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51067556458514019914910695 76601334687771029872366043)
    ·
      refine ⟨114902002031656544808549065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76601334687771029872366043 114902002031656544808549065)
      ·
        refine ⟨86176501523742408606411799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114902002031656544808549065 86176501523742408606411799)
        ·
          refine ⟨129264752285613612909617699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86176501523742408606411799 129264752285613612909617699)
          ·
            refine ⟨193897128428420419364426549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129264752285613612909617699 193897128428420419364426549)
            ·
              refine ⟨18177855790164414315414989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 193897128428420419364426549 18177855790164414315414989)
              ·
                refine ⟨6816695921311655368280621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18177855790164414315414989 6816695921311655368280621)
                ·
                  refine ⟨2556260970491870763105233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6816695921311655368280621 2556260970491870763105233)
                  ·
                    refine ⟨1917195727868903072328925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2556260970491870763105233 1917195727868903072328925)
                    ·
                      refine ⟨718948397950838652123347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1917195727868903072328925 718948397950838652123347)
                      ·
                        rfl

theorem cell23_1400147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_1400147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400147 prefixEnd_1400147 := by exact prefixLift 1400147
  have htrace : WordTrace (prefixWord ++ tailWord_1400147) baseStart_1400147 baseEnd_1400147 := by
    simpa [prefixWord, tailWord_1400147, baseEnd_1400147] using wordTrace_append hprefix tailTrace_1400147
  have hstable : (prefixWord ++ tailWord_1400147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400147).length < 2 ^ (prefixWord ++ tailWord_1400147).sum := by decide
  have hdescent : baseEnd_1400147 < baseStart_1400147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400167 : List Nat := [1, 1, 5, 1, 4, 1, 10]
def baseStart_1400167 : Nat := 118140960795 + 1400167 * 2 ^ 59
def prefixEnd_1400167 : Nat := 4983230072969 + 3 ^ 40 * 1400167 * 2
def baseEnd_1400167 : Nat := 8876032932888007084855

theorem tailTrace_1400167 : CollatzResearch.WordTrace tailWord_1400167 prefixEnd_1400167 8876032932888007084855 := by
  unfold tailWord_1400167
  simp only [CollatzResearch.WordTrace]
  refine ⟨51068285918441563330638755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34045523945627708887092503 51068285918441563330638755)
  ·
    refine ⟨76602428877662344995958133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51068285918441563330638755 76602428877662344995958133)
    ·
      refine ⟨7181477707280844843371075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76602428877662344995958133 7181477707280844843371075)
      ·
        refine ⟨10772216560921267265056613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7181477707280844843371075 10772216560921267265056613)
        ·
          refine ⟨2019790605172737612198115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10772216560921267265056613 2019790605172737612198115)
          ·
            refine ⟨3029685907759106418297173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019790605172737612198115 3029685907759106418297173)
            ·
              refine ⟨8876032932888007084855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3029685907759106418297173 8876032932888007084855)
              ·
                rfl

theorem cell23_1400167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 10].length) (baseStart_1400167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400167 prefixEnd_1400167 := by exact prefixLift 1400167
  have htrace : WordTrace (prefixWord ++ tailWord_1400167) baseStart_1400167 baseEnd_1400167 := by
    simpa [prefixWord, tailWord_1400167, baseEnd_1400167] using wordTrace_append hprefix tailTrace_1400167
  have hstable : (prefixWord ++ tailWord_1400167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400167).length < 2 ^ (prefixWord ++ tailWord_1400167).sum := by decide
  have hdescent : baseEnd_1400167 < baseStart_1400167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400177 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_1400177 : Nat := 118140960795 + 1400177 * 2 ^ 59
def prefixEnd_1400177 : Nat := 4983230072969 + 3 ^ 40 * 1400177 * 2
def baseEnd_1400177 : Nat := 718963802370473534748209

theorem tailTrace_1400177 : CollatzResearch.WordTrace tailWord_1400177 prefixEnd_1400177 718963802370473534748209 := by
  unfold tailWord_1400177
  simp only [CollatzResearch.WordTrace]
  refine ⟨51068650648405335038502785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34045767098936890025668523 51068650648405335038502785)
  ·
    refine ⟨38301487986304001278877089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51068650648405335038502785 38301487986304001278877089)
    ·
      refine ⟨28726115989728000959157817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38301487986304001278877089 28726115989728000959157817)
      ·
        refine ⟨21544586992296000719368363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28726115989728000959157817 21544586992296000719368363)
        ·
          refine ⟨32316880488444001079052545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21544586992296000719368363 32316880488444001079052545)
          ·
            refine ⟨24237660366333000809289409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32316880488444001079052545 24237660366333000809289409)
            ·
              refine ⟨18178245274749750606967057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24237660366333000809289409 18178245274749750606967057)
              ·
                refine ⟨13633683956062312955225293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18178245274749750606967057 13633683956062312955225293)
                ·
                  refine ⟨5112631483523367358209485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13633683956062312955225293 5112631483523367358209485)
                  ·
                    refine ⟨1917236806321262759328557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5112631483523367358209485 1917236806321262759328557)
                    ·
                      refine ⟨718963802370473534748209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1917236806321262759328557 718963802370473534748209)
                      ·
                        rfl

theorem cell23_1400177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_1400177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400177 prefixEnd_1400177 := by exact prefixLift 1400177
  have htrace : WordTrace (prefixWord ++ tailWord_1400177) baseStart_1400177 baseEnd_1400177 := by
    simpa [prefixWord, tailWord_1400177, baseEnd_1400177] using wordTrace_append hprefix tailTrace_1400177
  have hstable : (prefixWord ++ tailWord_1400177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400177).length < 2 ^ (prefixWord ++ tailWord_1400177).sum := by decide
  have hdescent : baseEnd_1400177 < baseStart_1400177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400178 : List Nat := [3, 2, 1, 2, 1, 2, 1, 6, 1, 2, 2]
def baseStart_1400178 : Nat := 118140960795 + 1400178 * 2 ^ 59
def prefixEnd_1400178 : Nat := 4983230072969 + 3 ^ 40 * 1400178 * 2
def baseEnd_1400178 : Nat := 718964315851128030835705

theorem tailTrace_1400178 : CollatzResearch.WordTrace tailWord_1400178 prefixEnd_1400178 718964315851128030835705 := by
  unfold tailWord_1400178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767171780350428052322297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34045791414267808139526125 12767171780350428052322297)
  ·
    refine ⟨9575378835262821039241723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12767171780350428052322297 9575378835262821039241723)
    ·
      refine ⟨14363068252894231558862585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9575378835262821039241723 14363068252894231558862585)
      ·
        refine ⟨10772301189670673669146939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14363068252894231558862585 10772301189670673669146939)
        ·
          refine ⟨16158451784506010503720409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10772301189670673669146939 16158451784506010503720409)
          ·
            refine ⟨12118838838379507877790307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16158451784506010503720409 12118838838379507877790307)
            ·
              refine ⟨18178258257569261816685461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12118838838379507877790307 18178258257569261816685461)
              ·
                refine ⟨852105855823559147657131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18178258257569261816685461 852105855823559147657131)
                ·
                  refine ⟨1278158783735338721485697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852105855823559147657131 1278158783735338721485697)
                  ·
                    refine ⟨958619087801504041114273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1278158783735338721485697 958619087801504041114273)
                    ·
                      refine ⟨718964315851128030835705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958619087801504041114273 718964315851128030835705)
                      ·
                        rfl

theorem cell23_1400178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_1400178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400178 prefixEnd_1400178 := by exact prefixLift 1400178
  have htrace : WordTrace (prefixWord ++ tailWord_1400178) baseStart_1400178 baseEnd_1400178 := by
    simpa [prefixWord, tailWord_1400178, baseEnd_1400178] using wordTrace_append hprefix tailTrace_1400178
  have hstable : (prefixWord ++ tailWord_1400178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400178).length < 2 ^ (prefixWord ++ tailWord_1400178).sum := by decide
  have hdescent : baseEnd_1400178 < baseStart_1400178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400201 : List Nat := [1, 2, 1, 1, 8, 1, 2, 7]
def baseStart_1400201 : Nat := 118140960795 + 1400201 * 2 ^ 59
def prefixEnd_1400201 : Nat := 4983230072969 + 3 ^ 40 * 1400201 * 2
def baseEnd_1400201 : Nat := 26628745403932645957337

theorem tailTrace_1400201 : CollatzResearch.WordTrace tailWord_1400201 prefixEnd_1400201 26628745403932645957337 := by
  unfold tailWord_1400201
  simp only [CollatzResearch.WordTrace]
  refine ⟨51069526000318387137376457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34046350666878924758250971 51069526000318387137376457)
  ·
    refine ⟨38302144500238790353032343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51069526000318387137376457 38302144500238790353032343)
    ·
      refine ⟨57453216750358185529548515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38302144500238790353032343 57453216750358185529548515)
      ·
        refine ⟨86179825125537278294322773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57453216750358185529548515 86179825125537278294322773)
        ·
          refine ⟨1009919825689889980011595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 86179825125537278294322773 1009919825689889980011595)
          ·
            refine ⟨1514879738534834970017393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009919825689889980011595 1514879738534834970017393)
            ·
              refine ⟨1136159803901126227513045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514879738534834970017393 1136159803901126227513045)
              ·
                refine ⟨26628745403932645957337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1136159803901126227513045 26628745403932645957337)
                ·
                  rfl

theorem cell23_1400201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 7].length) (baseStart_1400201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400201 prefixEnd_1400201 := by exact prefixLift 1400201
  have htrace : WordTrace (prefixWord ++ tailWord_1400201) baseStart_1400201 baseEnd_1400201 := by
    simpa [prefixWord, tailWord_1400201, baseEnd_1400201] using wordTrace_append hprefix tailTrace_1400201
  have hstable : (prefixWord ++ tailWord_1400201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400201).length < 2 ^ (prefixWord ++ tailWord_1400201).sum := by decide
  have hdescent : baseEnd_1400201 < baseStart_1400201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400212 : List Nat := [2, 4, 2, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_1400212 : Nat := 118140960795 + 1400212 * 2 ^ 59
def prefixEnd_1400212 : Nat := 4983230072969 + 3 ^ 40 * 1400212 * 2
def baseEnd_1400212 : Nat := 718981774193380897810549

theorem tailTrace_1400212 : CollatzResearch.WordTrace tailWord_1400212 prefixEnd_1400212 718981774193380897810549 := by
  unfold tailWord_1400212
  simp only [CollatzResearch.WordTrace]
  refine ⟨25534963601639268008013445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34046618135519024010684593 25534963601639268008013445)
  ·
    refine ⟨4787805675307362751502521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25534963601639268008013445 4787805675307362751502521)
    ·
      refine ⟨3590854256480522063626891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4787805675307362751502521 3590854256480522063626891)
      ·
        refine ⟨5386281384720783095440337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590854256480522063626891 5386281384720783095440337)
        ·
          refine ⟨4039711038540587321580253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5386281384720783095440337 4039711038540587321580253)
          ·
            refine ⟨1514891639452720245592595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4039711038540587321580253 1514891639452720245592595)
            ·
              refine ⟨2272337459179080368388893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514891639452720245592595 2272337459179080368388893)
              ·
                refine ⟨852126547192155138145835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2272337459179080368388893 852126547192155138145835)
                ·
                  refine ⟨1278189820788232707218753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852126547192155138145835 1278189820788232707218753)
                  ·
                    refine ⟨958642365591174530414065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1278189820788232707218753 958642365591174530414065)
                    ·
                      refine ⟨718981774193380897810549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958642365591174530414065 718981774193380897810549)
                      ·
                        rfl

theorem cell23_1400212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_1400212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400212 prefixEnd_1400212 := by exact prefixLift 1400212
  have htrace : WordTrace (prefixWord ++ tailWord_1400212) baseStart_1400212 baseEnd_1400212 := by
    simpa [prefixWord, tailWord_1400212, baseEnd_1400212] using wordTrace_append hprefix tailTrace_1400212
  have hstable : (prefixWord ++ tailWord_1400212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400212).length < 2 ^ (prefixWord ++ tailWord_1400212).sum := by decide
  have hdescent : baseEnd_1400212 < baseStart_1400212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400245 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_1400245 : Nat := 118140960795 + 1400245 * 2 ^ 59
def prefixEnd_1400245 : Nat := 4983230072969 + 3 ^ 40 * 1400245 * 2
def baseEnd_1400245 : Nat := 718998719054979268697897

theorem tailTrace_1400245 : CollatzResearch.WordTrace tailWord_1400245 prefixEnd_1400245 718998719054979268697897 := by
  unfold tailWord_1400245
  simp only [CollatzResearch.WordTrace]
  refine ⟨51071130812158982651978189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34047420541439321767985459 51071130812158982651978189)
  ·
    refine ⟨19151674054559618494491821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51071130812158982651978189 19151674054559618494491821)
    ·
      refine ⟨7181877770459856935434433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19151674054559618494491821 7181877770459856935434433)
      ·
        refine ⟨5386408327844892701575825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7181877770459856935434433 5386408327844892701575825)
        ·
          refine ⟨4039806245883669526181869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5386408327844892701575825 4039806245883669526181869)
          ·
            refine ⟨1514927342206376072318201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4039806245883669526181869 1514927342206376072318201)
            ·
              refine ⟨1136195506654782054238651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514927342206376072318201 1136195506654782054238651)
              ·
                refine ⟨1704293259982173081357977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136195506654782054238651 1704293259982173081357977)
                ·
                  refine ⟨1278219944986629811018483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1704293259982173081357977 1278219944986629811018483)
                  ·
                    refine ⟨1917329917479944716527725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1278219944986629811018483 1917329917479944716527725)
                    ·
                      refine ⟨718998719054979268697897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1917329917479944716527725 718998719054979268697897)
                      ·
                        rfl

theorem cell23_1400245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_1400245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400245 prefixEnd_1400245 := by exact prefixLift 1400245
  have htrace : WordTrace (prefixWord ++ tailWord_1400245) baseStart_1400245 baseEnd_1400245 := by
    simpa [prefixWord, tailWord_1400245, baseEnd_1400245] using wordTrace_append hprefix tailTrace_1400245
  have hstable : (prefixWord ++ tailWord_1400245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400245).length < 2 ^ (prefixWord ++ tailWord_1400245).sum := by decide
  have hdescent : baseEnd_1400245 < baseStart_1400245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400247 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_1400247 : Nat := 118140960795 + 1400247 * 2 ^ 59
def prefixEnd_1400247 : Nat := 4983230072969 + 3 ^ 40 * 1400247 * 2
def baseEnd_1400247 : Nat := 718999746016288260872887

theorem tailTrace_1400247 : CollatzResearch.WordTrace tailWord_1400247 prefixEnd_1400247 718999746016288260872887 := by
  unfold tailWord_1400247
  simp only [CollatzResearch.WordTrace]
  refine ⟨51071203758151736993550995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34047469172101157995700663 51071203758151736993550995)
  ·
    refine ⟨76606805637227605490326493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51071203758151736993550995 76606805637227605490326493)
    ·
      refine ⟨28727552113960352058872435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76606805637227605490326493 28727552113960352058872435)
      ·
        refine ⟨43091328170940528088308653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28727552113960352058872435 43091328170940528088308653)
        ·
          refine ⟨16159248064102698033115745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43091328170940528088308653 16159248064102698033115745)
          ·
            refine ⟨12119436048077023524836809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16159248064102698033115745 12119436048077023524836809)
            ·
              refine ⟨9089577036057767643627607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12119436048077023524836809 9089577036057767643627607)
              ·
                refine ⟨13634365554086651465441411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9089577036057767643627607 13634365554086651465441411)
                ·
                  refine ⟨20451548331129977198162117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13634365554086651465441411 20451548331129977198162117)
                  ·
                    refine ⟨3834665312086870724655397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20451548331129977198162117 3834665312086870724655397)
                    ·
                      refine ⟨718999746016288260872887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3834665312086870724655397 718999746016288260872887)
                      ·
                        rfl

theorem cell23_1400247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_1400247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400247 prefixEnd_1400247 := by exact prefixLift 1400247
  have htrace : WordTrace (prefixWord ++ tailWord_1400247) baseStart_1400247 baseEnd_1400247 := by
    simpa [prefixWord, tailWord_1400247, baseEnd_1400247] using wordTrace_append hprefix tailTrace_1400247
  have hstable : (prefixWord ++ tailWord_1400247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400247).length < 2 ^ (prefixWord ++ tailWord_1400247).sum := by decide
  have hdescent : baseEnd_1400247 < baseStart_1400247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400285 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_1400285 : Nat := 118140960795 + 1400285 * 2 ^ 59
def prefixEnd_1400285 : Nat := 4983230072969 + 3 ^ 40 * 1400285 * 2
def baseEnd_1400285 : Nat := 719019258281159112197713

theorem tailTrace_1400285 : CollatzResearch.WordTrace tailWord_1400285 prefixEnd_1400285 719019258281159112197713 := by
  unfold tailWord_1400285
  simp only [CollatzResearch.WordTrace]
  refine ⟨51072589732014069483434309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34048393154676046322289539 51072589732014069483434309)
  ·
    refine ⟨9576110574752638028143933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51072589732014069483434309 9576110574752638028143933)
    ·
      refine ⟨3591041465532239260553975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9576110574752638028143933 3591041465532239260553975)
      ·
        refine ⟨5386562198298358890830963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591041465532239260553975 5386562198298358890830963)
        ·
          refine ⟨8079843297447538336246445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5386562198298358890830963 8079843297447538336246445)
          ·
            refine ⟨3029941236542826876092417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8079843297447538336246445 3029941236542826876092417)
            ·
              refine ⟨2272455927407120157069313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029941236542826876092417 2272455927407120157069313)
              ·
                refine ⟨1704341945555340117801985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272455927407120157069313 1704341945555340117801985)
                ·
                  refine ⟨1278256459166505088351489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1704341945555340117801985 1278256459166505088351489)
                  ·
                    refine ⟨958692344374878816263617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1278256459166505088351489 958692344374878816263617)
                    ·
                      refine ⟨719019258281159112197713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958692344374878816263617 719019258281159112197713)
                      ·
                        rfl

theorem cell23_1400285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_1400285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400285 prefixEnd_1400285 := by exact prefixLift 1400285
  have htrace : WordTrace (prefixWord ++ tailWord_1400285) baseStart_1400285 baseEnd_1400285 := by
    simpa [prefixWord, tailWord_1400285, baseEnd_1400285] using wordTrace_append hprefix tailTrace_1400285
  have hstable : (prefixWord ++ tailWord_1400285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400285).length < 2 ^ (prefixWord ++ tailWord_1400285).sum := by decide
  have hdescent : baseEnd_1400285 < baseStart_1400285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400291 : List Nat := [1, 1, 1, 6, 2, 2, 1, 4, 5]
def baseStart_1400291 : Nat := 118140960795 + 1400291 * 2 ^ 59
def prefixEnd_1400291 : Nat := 4983230072969 + 3 ^ 40 * 1400291 * 2
def baseEnd_1400291 : Nat := 79891371018342898746965

theorem tailTrace_1400291 : CollatzResearch.WordTrace tailWord_1400291 prefixEnd_1400291 79891371018342898746965 := by
  unfold tailWord_1400291
  simp only [CollatzResearch.WordTrace]
  refine ⟨51072808569992332508152727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34048539046661555005435151 51072808569992332508152727)
  ·
    refine ⟨76609212854988498762229091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51072808569992332508152727 76609212854988498762229091)
    ·
      refine ⟨114913819282482748143343637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76609212854988498762229091 114913819282482748143343637)
      ·
        refine ⟨5386585278866378819219233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114913819282482748143343637 5386585278866378819219233)
        ·
          refine ⟨4039938959149784114414425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5386585278866378819219233 4039938959149784114414425)
          ·
            refine ⟨3029954219362338085810819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4039938959149784114414425 3029954219362338085810819)
            ·
              refine ⟨4544931329043507128716229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3029954219362338085810819 4544931329043507128716229)
              ·
                refine ⟨852174624195657586634293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4544931329043507128716229 852174624195657586634293)
                ·
                  refine ⟨79891371018342898746965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852174624195657586634293 79891371018342898746965)
                  ·
                    rfl

theorem cell23_1400291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 5].length) (baseStart_1400291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400291 prefixEnd_1400291 := by exact prefixLift 1400291
  have htrace : WordTrace (prefixWord ++ tailWord_1400291) baseStart_1400291 baseEnd_1400291 := by
    simpa [prefixWord, tailWord_1400291, baseEnd_1400291] using wordTrace_append hprefix tailTrace_1400291
  have hstable : (prefixWord ++ tailWord_1400291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400291).length < 2 ^ (prefixWord ++ tailWord_1400291).sum := by decide
  have hdescent : baseEnd_1400291 < baseStart_1400291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400337 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_1400337 : Nat := 118140960795 + 1400337 * 2 ^ 59
def prefixEnd_1400337 : Nat := 4983230072969 + 3 ^ 40 * 1400337 * 2
def baseEnd_1400337 : Nat := 719045959275192908747473

theorem tailTrace_1400337 : CollatzResearch.WordTrace tailWord_1400337 prefixEnd_1400337 719045959275192908747473 := by
  unfold tailWord_1400337
  simp only [CollatzResearch.WordTrace]
  refine ⟨51074486327825682364327265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34049657551883788242884843 51074486327825682364327265)
  ·
    refine ⟨38305864745869261773245449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51074486327825682364327265 38305864745869261773245449)
    ·
      refine ⟨28729398559401946329934087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38305864745869261773245449 28729398559401946329934087)
      ·
        refine ⟨43094097839102919494901131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28729398559401946329934087 43094097839102919494901131)
        ·
          refine ⟨64641146758654379242351697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43094097839102919494901131 64641146758654379242351697)
          ·
            refine ⟨48480860068990784431763773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64641146758654379242351697 48480860068990784431763773)
            ·
              refine ⟨18180322525871544161911415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48480860068990784431763773 18180322525871544161911415)
              ·
                refine ⟨27270483788807316242867123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18180322525871544161911415 27270483788807316242867123)
                ·
                  refine ⟨40905725683210974364300685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27270483788807316242867123 40905725683210974364300685)
                  ·
                    refine ⟨15339647131204115386612757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40905725683210974364300685 15339647131204115386612757)
                    ·
                      refine ⟨719045959275192908747473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15339647131204115386612757 719045959275192908747473)
                      ·
                        rfl

theorem cell23_1400337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_1400337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400337 prefixEnd_1400337 := by exact prefixLift 1400337
  have htrace : WordTrace (prefixWord ++ tailWord_1400337) baseStart_1400337 baseEnd_1400337 := by
    simpa [prefixWord, tailWord_1400337, baseEnd_1400337] using wordTrace_append hprefix tailTrace_1400337
  have hstable : (prefixWord ++ tailWord_1400337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400337).length < 2 ^ (prefixWord ++ tailWord_1400337).sum := by decide
  have hdescent : baseEnd_1400337 < baseStart_1400337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400341 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_1400341 : Nat := 118140960795 + 1400341 * 2 ^ 59
def prefixEnd_1400341 : Nat := 4983230072969 + 3 ^ 40 * 1400341 * 2
def baseEnd_1400341 : Nat := 719048013197810893097455

theorem tailTrace_1400341 : CollatzResearch.WordTrace tailWord_1400341 prefixEnd_1400341 719048013197810893097455 := by
  unfold tailWord_1400341
  simp only [CollatzResearch.WordTrace]
  refine ⟨51074632219811191047472877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34049754813207460698315251 51074632219811191047472877)
  ·
    refine ⟨19152987082429196642802329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51074632219811191047472877 19152987082429196642802329)
    ·
      refine ⟨14364740311821897482101747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19152987082429196642802329 14364740311821897482101747)
      ·
        refine ⟨21547110467732846223152621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14364740311821897482101747 21547110467732846223152621)
        ·
          refine ⟨8080166425399817333682233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21547110467732846223152621 8080166425399817333682233)
          ·
            refine ⟨6060124819049863000261675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8080166425399817333682233 6060124819049863000261675)
            ·
              refine ⟨9090187228574794500392513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060124819049863000261675 9090187228574794500392513)
              ·
                refine ⟨6817640421431095875294385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9090187228574794500392513 6817640421431095875294385)
                ·
                  refine ⟨5113230316073321906470789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6817640421431095875294385 5113230316073321906470789)
                  ·
                    refine ⟨958730684263747857463273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5113230316073321906470789 958730684263747857463273)
                    ·
                      refine ⟨719048013197810893097455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958730684263747857463273 719048013197810893097455)
                      ·
                        rfl

theorem cell23_1400341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_1400341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400341 prefixEnd_1400341 := by exact prefixLift 1400341
  have htrace : WordTrace (prefixWord ++ tailWord_1400341) baseStart_1400341 baseEnd_1400341 := by
    simpa [prefixWord, tailWord_1400341, baseEnd_1400341] using wordTrace_append hprefix tailTrace_1400341
  have hstable : (prefixWord ++ tailWord_1400341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400341).length < 2 ^ (prefixWord ++ tailWord_1400341).sum := by decide
  have hdescent : baseEnd_1400341 < baseStart_1400341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400448 : List Nat := [2, 1, 1, 2, 1, 4, 5, 1, 1, 1, 4]
def baseStart_1400448 : Nat := 118140960795 + 1400448 * 2 ^ 59
def prefixEnd_1400448 : Nat := 4983230072969 + 3 ^ 40 * 1400448 * 2
def baseEnd_1400448 : Nat := 719102955627841974459463

theorem tailTrace_1400448 : CollatzResearch.WordTrace tailWord_1400448 prefixEnd_1400448 719102955627841974459463 := by
  unfold tailWord_1400448
  simp only [CollatzResearch.WordTrace]
  refine ⟨25539267415211774160808999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34052356553615698881078665 25539267415211774160808999)
  ·
    refine ⟨38308901122817661241213499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25539267415211774160808999 38308901122817661241213499)
    ·
      refine ⟨57463351684226491861820249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38308901122817661241213499 57463351684226491861820249)
      ·
        refine ⟨43097513763169868896365187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57463351684226491861820249 43097513763169868896365187)
        ·
          refine ⟨64646270644754803344547781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43097513763169868896365187 64646270644754803344547781)
          ·
            refine ⟨12121175745891525627102709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64646270644754803344547781 12121175745891525627102709)
            ·
              refine ⟨1136360226177330527540879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12121175745891525627102709 1136360226177330527540879)
              ·
                refine ⟨1704540339265995791311319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136360226177330527540879 1704540339265995791311319)
                ·
                  refine ⟨2556810508898993686966979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704540339265995791311319 2556810508898993686966979)
                  ·
                    refine ⟨3835215763348490530450469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2556810508898993686966979 3835215763348490530450469)
                    ·
                      refine ⟨719102955627841974459463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3835215763348490530450469 719102955627841974459463)
                      ·
                        rfl

theorem cell23_1400448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_1400448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400448 prefixEnd_1400448 := by exact prefixLift 1400448
  have htrace : WordTrace (prefixWord ++ tailWord_1400448) baseStart_1400448 baseEnd_1400448 := by
    simpa [prefixWord, tailWord_1400448, baseEnd_1400448] using wordTrace_append hprefix tailTrace_1400448
  have hstable : (prefixWord ++ tailWord_1400448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400448).length < 2 ^ (prefixWord ++ tailWord_1400448).sum := by decide
  have hdescent : baseEnd_1400448 < baseStart_1400448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400454 : List Nat := [6, 17]
def baseStart_1400454 : Nat := 118140960795 + 1400454 * 2 ^ 59
def prefixEnd_1400454 : Nat := 4983230072969 + 3 ^ 40 * 1400454 * 2
def baseEnd_1400454 : Nat := 36534371615697248945

theorem tailTrace_1400454 : CollatzResearch.WordTrace tailWord_1400454 prefixEnd_1400454 36534371615697248945 := by
  unfold tailWord_1400454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596211052137556604573013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34052502445601207564224277 1596211052137556604573013)
  ·
    refine ⟨36534371615697248945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 17 1596211052137556604573013 36534371615697248945)
    ·
      rfl

theorem cell23_1400454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 17].length) (baseStart_1400454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400454 prefixEnd_1400454 := by exact prefixLift 1400454
  have htrace : WordTrace (prefixWord ++ tailWord_1400454) baseStart_1400454 baseEnd_1400454 := by
    simpa [prefixWord, tailWord_1400454, baseEnd_1400454] using wordTrace_append hprefix tailTrace_1400454
  have hstable : (prefixWord ++ tailWord_1400454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400454).length < 2 ^ (prefixWord ++ tailWord_1400454).sum := by decide
  have hdescent : baseEnd_1400454 < baseStart_1400454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400458 : List Nat := [3, 1, 2, 3, 2, 1, 1, 4, 2, 4]
def baseStart_1400458 : Nat := 118140960795 + 1400458 * 2 ^ 59
def prefixEnd_1400458 : Nat := 4983230072969 + 3 ^ 40 * 1400458 * 2
def baseEnd_1400458 : Nat := 239702696811462311778139

theorem tailTrace_1400458 : CollatzResearch.WordTrace tailWord_1400458 prefixEnd_1400458 239702696811462311778139 := by
  unfold tailWord_1400458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12769724890096830007370507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34052599706924880019654685 12769724890096830007370507)
  ·
    refine ⟨19154587335145245011055761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12769724890096830007370507 19154587335145245011055761)
    ·
      refine ⟨14365940501358933758291821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19154587335145245011055761 14365940501358933758291821)
      ·
        refine ⟨5387227688009600159359433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14365940501358933758291821 5387227688009600159359433)
        ·
          refine ⟨4040420766007200119519575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5387227688009600159359433 4040420766007200119519575)
          ·
            refine ⟨6060631149010800179279363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4040420766007200119519575 6060631149010800179279363)
            ·
              refine ⟨9090946723516200268919045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060631149010800179279363 9090946723516200268919045)
              ·
                refine ⟨1704552510659287550422321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9090946723516200268919045 1704552510659287550422321)
                ·
                  refine ⟨1278414382994465662816741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1704552510659287550422321 1278414382994465662816741)
                  ·
                    refine ⟨239702696811462311778139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1278414382994465662816741 239702696811462311778139)
                    ·
                      rfl

theorem cell23_1400458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_1400458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400458 prefixEnd_1400458 := by exact prefixLift 1400458
  have htrace : WordTrace (prefixWord ++ tailWord_1400458) baseStart_1400458 baseEnd_1400458 := by
    simpa [prefixWord, tailWord_1400458, baseEnd_1400458] using wordTrace_append hprefix tailTrace_1400458
  have hstable : (prefixWord ++ tailWord_1400458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400458).length < 2 ^ (prefixWord ++ tailWord_1400458).sum := by decide
  have hdescent : baseEnd_1400458 < baseStart_1400458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400471 : List Nat := [1, 1, 3, 3, 2, 4, 1, 8]
def baseStart_1400471 : Nat := 118140960795 + 1400471 * 2 ^ 59
def prefixEnd_1400471 : Nat := 4983230072969 + 3 ^ 40 * 1400471 * 2
def baseEnd_1400471 : Nat := 26633880210477606832291

theorem tailTrace_1400471 : CollatzResearch.WordTrace tailWord_1400471 prefixEnd_1400471 26633880210477606832291 := by
  unfold tailWord_1400471
  simp only [CollatzResearch.WordTrace]
  refine ⟨51079373709340223249705267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34052915806226815499803511 51079373709340223249705267)
  ·
    refine ⟨76619060564010334874557901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51079373709340223249705267 76619060564010334874557901)
    ·
      refine ⟨28732147711503875577959213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76619060564010334874557901 28732147711503875577959213)
      ·
        refine ⟨10774555391813953341734705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28732147711503875577959213 10774555391813953341734705)
        ·
          refine ⟨8080916543860465006301029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10774555391813953341734705 8080916543860465006301029)
          ·
            refine ⟨1515171851973837188681443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8080916543860465006301029 1515171851973837188681443)
            ·
              refine ⟨2272757777960755783022165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515171851973837188681443 2272757777960755783022165)
              ·
                refine ⟨26633880210477606832291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2272757777960755783022165 26633880210477606832291)
                ·
                  rfl

theorem cell23_1400471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 8].length) (baseStart_1400471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400471 prefixEnd_1400471 := by exact prefixLift 1400471
  have htrace : WordTrace (prefixWord ++ tailWord_1400471) baseStart_1400471 baseEnd_1400471 := by
    simpa [prefixWord, tailWord_1400471, baseEnd_1400471] using wordTrace_append hprefix tailTrace_1400471
  have hstable : (prefixWord ++ tailWord_1400471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400471).length < 2 ^ (prefixWord ++ tailWord_1400471).sum := by decide
  have hdescent : baseEnd_1400471 < baseStart_1400471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400478 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1400478 : Nat := 118140960795 + 1400478 * 2 ^ 59
def prefixEnd_1400478 : Nat := 4983230072969 + 3 ^ 40 * 1400478 * 2
def baseEnd_1400478 : Nat := 719118360047476857084325

theorem tailTrace_1400478 : CollatzResearch.WordTrace tailWord_1400478 prefixEnd_1400478 719118360047476857084325 := by
  unfold tailWord_1400478
  simp only [CollatzResearch.WordTrace]
  refine ⟨6384953627539357930651261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34053086013543242296806725 6384953627539357930651261)
  ·
    refine ⟨2394357610327259223994223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6384953627539357930651261 2394357610327259223994223)
    ·
      refine ⟨3591536415490888835991335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2394357610327259223994223 3591536415490888835991335)
      ·
        refine ⟨5387304623236333253987003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3591536415490888835991335 5387304623236333253987003)
        ·
          refine ⟨8080956934854499880980505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5387304623236333253987003 8080956934854499880980505)
          ·
            refine ⟨6060717701140874910735379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8080956934854499880980505 6060717701140874910735379)
            ·
              refine ⟨9091076551711312366103069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6060717701140874910735379 9091076551711312366103069)
              ·
                refine ⟨3409153706891742137288651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9091076551711312366103069 3409153706891742137288651)
                ·
                  refine ⟨5113730560337613205932977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3409153706891742137288651 5113730560337613205932977)
                  ·
                    refine ⟨3835297920253209904449733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5113730560337613205932977 3835297920253209904449733)
                    ·
                      refine ⟨719118360047476857084325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3835297920253209904449733 719118360047476857084325)
                      ·
                        rfl

theorem cell23_1400478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1400478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400478 prefixEnd_1400478 := by exact prefixLift 1400478
  have htrace : WordTrace (prefixWord ++ tailWord_1400478) baseStart_1400478 baseEnd_1400478 := by
    simpa [prefixWord, tailWord_1400478, baseEnd_1400478] using wordTrace_append hprefix tailTrace_1400478
  have hstable : (prefixWord ++ tailWord_1400478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400478).length < 2 ^ (prefixWord ++ tailWord_1400478).sum := by decide
  have hdescent : baseEnd_1400478 < baseStart_1400478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400502 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1400502 : Nat := 118140960795 + 1400502 * 2 ^ 59
def prefixEnd_1400502 : Nat := 4983230072969 + 3 ^ 40 * 1400502 * 2
def baseEnd_1400502 : Nat := 719130683583184763184215

theorem tailTrace_1400502 : CollatzResearch.WordTrace tailWord_1400502 prefixEnd_1400502 719130683583184763184215 := by
  unfold tailWord_1400502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192531523264244721505235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34053669581485277029389173 3192531523264244721505235)
  ·
    refine ⟨4788797284896367082257853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3192531523264244721505235 4788797284896367082257853)
    ·
      refine ⟨1795798981836137655846695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4788797284896367082257853 1795798981836137655846695)
      ·
        refine ⟨2693698472754206483770043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795798981836137655846695 2693698472754206483770043)
        ·
          refine ⟨4040547709131309725655065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2693698472754206483770043 4040547709131309725655065)
          ·
            refine ⟨3030410781848482294241299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4040547709131309725655065 3030410781848482294241299)
            ·
              refine ⟨4545616172772723441361949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3030410781848482294241299 4545616172772723441361949)
              ·
                refine ⟨1704606064789771290510731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4545616172772723441361949 1704606064789771290510731)
                ·
                  refine ⟨2556909097184656935766097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704606064789771290510731 2556909097184656935766097)
                  ·
                    refine ⟨1917681822888492701824573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2556909097184656935766097 1917681822888492701824573)
                    ·
                      refine ⟨719130683583184763184215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1917681822888492701824573 719130683583184763184215)
                      ·
                        rfl

theorem cell23_1400502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1400502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400502 prefixEnd_1400502 := by exact prefixLift 1400502
  have htrace : WordTrace (prefixWord ++ tailWord_1400502) baseStart_1400502 baseEnd_1400502 := by
    simpa [prefixWord, tailWord_1400502, baseEnd_1400502] using wordTrace_append hprefix tailTrace_1400502
  have hstable : (prefixWord ++ tailWord_1400502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400502).length < 2 ^ (prefixWord ++ tailWord_1400502).sum := by decide
  have hdescent : baseEnd_1400502 < baseStart_1400502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400521 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 10, 2]
def baseStart_1400521 : Nat := 118140960795 + 1400521 * 2 ^ 59
def prefixEnd_1400521 : Nat := 4983230072969 + 3 ^ 40 * 1400521 * 2
def baseEnd_1400521 : Nat := 719140439715620188846627

theorem tailTrace_1400521 : CollatzResearch.WordTrace tailWord_1400521 prefixEnd_1400521 719140439715620188846627 := by
  unfold tailWord_1400521
  simp only [CollatzResearch.WordTrace]
  refine ⟨51081197359159081789025417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34054131572772721192683611 51081197359159081789025417)
  ·
    refine ⟨38310898019369311341769063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51081197359159081789025417 38310898019369311341769063)
    ·
      refine ⟨57466347029053967012653595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38310898019369311341769063 57466347029053967012653595)
      ·
        refine ⟨86199520543580950518980393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57466347029053967012653595 86199520543580950518980393)
        ·
          refine ⟨64649640407685712889235295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86199520543580950518980393 64649640407685712889235295)
          ·
            refine ⟨96974460611528569333852943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64649640407685712889235295 96974460611528569333852943)
            ·
              refine ⟨145461690917292854000779415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96974460611528569333852943 145461690917292854000779415)
              ·
                refine ⟨218192536375939281001169123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145461690917292854000779415 218192536375939281001169123)
                ·
                  refine ⟨327288804563908921501753685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218192536375939281001169123 327288804563908921501753685)
                  ·
                    refine ⟨958853919620826918462169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 327288804563908921501753685 958853919620826918462169)
                    ·
                      refine ⟨719140439715620188846627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958853919620826918462169 719140439715620188846627)
                      ·
                        rfl

theorem cell23_1400521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 10, 2].length) (baseStart_1400521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400521 prefixEnd_1400521 := by exact prefixLift 1400521
  have htrace : WordTrace (prefixWord ++ tailWord_1400521) baseStart_1400521 baseEnd_1400521 := by
    simpa [prefixWord, tailWord_1400521, baseEnd_1400521] using wordTrace_append hprefix tailTrace_1400521
  have hstable : (prefixWord ++ tailWord_1400521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400521).length < 2 ^ (prefixWord ++ tailWord_1400521).sum := by decide
  have hdescent : baseEnd_1400521 < baseStart_1400521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400571 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 3]
def baseStart_1400571 : Nat := 118140960795 + 1400571 * 2 ^ 59
def prefixEnd_1400571 : Nat := 4983230072969 + 3 ^ 40 * 1400571 * 2
def baseEnd_1400571 : Nat := 719166113748344993221397

theorem tailTrace_1400571 : CollatzResearch.WordTrace tailWord_1400571 prefixEnd_1400571 719166113748344993221397 := by
  unfold tailWord_1400571
  simp only [CollatzResearch.WordTrace]
  refine ⟨51083021008977940328345567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34055347339318626885563711 51083021008977940328345567)
  ·
    refine ⟨76624531513466910492518351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51083021008977940328345567 76624531513466910492518351)
    ·
      refine ⟨114936797270200365738777527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76624531513466910492518351 114936797270200365738777527)
      ·
        refine ⟨172405195905300548608166291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114936797270200365738777527 172405195905300548608166291)
        ·
          refine ⟨258607793857950822912249437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172405195905300548608166291 258607793857950822912249437)
          ·
            refine ⟨96977922696731558592093539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258607793857950822912249437 96977922696731558592093539)
            ·
              refine ⟨145466884045097337888140309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96977922696731558592093539 145466884045097337888140309)
              ·
                refine ⟨6818760189613937713506577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 145466884045097337888140309 6818760189613937713506577)
                ·
                  refine ⟨5114070142210453285129933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6818760189613937713506577 5114070142210453285129933)
                  ·
                    refine ⟨1917776303328919981923725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5114070142210453285129933 1917776303328919981923725)
                    ·
                      refine ⟨719166113748344993221397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1917776303328919981923725 719166113748344993221397)
                      ·
                        rfl

theorem cell23_1400571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 3].length) (baseStart_1400571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400571 prefixEnd_1400571 := by exact prefixLift 1400571
  have htrace : WordTrace (prefixWord ++ tailWord_1400571) baseStart_1400571 baseEnd_1400571 := by
    simpa [prefixWord, tailWord_1400571, baseEnd_1400571] using wordTrace_append hprefix tailTrace_1400571
  have hstable : (prefixWord ++ tailWord_1400571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400571).length < 2 ^ (prefixWord ++ tailWord_1400571).sum := by decide
  have hdescent : baseEnd_1400571 < baseStart_1400571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400608 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 2, 5]
def baseStart_1400608 : Nat := 118140960795 + 1400608 * 2 ^ 59
def prefixEnd_1400608 : Nat := 4983230072969 + 3 ^ 40 * 1400608 * 2
def baseEnd_1400608 : Nat := 239728370844187116152909

theorem tailTrace_1400608 : CollatzResearch.WordTrace tailWord_1400608 prefixEnd_1400608 239728370844187116152909 := by
  unfold tailWord_1400608
  simp only [CollatzResearch.WordTrace]
  refine ⟨25542185254921947823721239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34056247006562597098294985 25542185254921947823721239)
  ·
    refine ⟨38313277882382921735581859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25542185254921947823721239 38313277882382921735581859)
    ·
      refine ⟨57469916823574382603372789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38313277882382921735581859 57469916823574382603372789)
      ·
        refine ⟨5387804702210098369066199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57469916823574382603372789 5387804702210098369066199)
        ·
          refine ⟨8081707053315147553599299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5387804702210098369066199 8081707053315147553599299)
          ·
            refine ⟨12122560579972721330398949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8081707053315147553599299 12122560579972721330398949)
            ·
              refine ⟨2272980108744885249449803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12122560579972721330398949 2272980108744885249449803)
              ·
                refine ⟨3409470163117327874174705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272980108744885249449803 3409470163117327874174705)
                ·
                  refine ⟨2557102622337995905631029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3409470163117327874174705 2557102622337995905631029)
                  ·
                    refine ⟨239728370844187116152909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2557102622337995905631029 239728370844187116152909)
                    ·
                      rfl

theorem cell23_1400608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_1400608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400608 prefixEnd_1400608 := by exact prefixLift 1400608
  have htrace : WordTrace (prefixWord ++ tailWord_1400608) baseStart_1400608 baseEnd_1400608 := by
    simpa [prefixWord, tailWord_1400608, baseEnd_1400608] using wordTrace_append hprefix tailTrace_1400608
  have hstable : (prefixWord ++ tailWord_1400608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400608).length < 2 ^ (prefixWord ++ tailWord_1400608).sum := by decide
  have hdescent : baseEnd_1400608 < baseStart_1400608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400611 : List Nat := [1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1400611 : Nat := 118140960795 + 1400611 * 2 ^ 59
def prefixEnd_1400611 : Nat := 4983230072969 + 3 ^ 40 * 1400611 * 2
def baseEnd_1400611 : Nat := 719186652974524836721213

theorem tailTrace_1400611 : CollatzResearch.WordTrace tailWord_1400611 prefixEnd_1400611 719186652974524836721213 := by
  unfold tailWord_1400611
  simp only [CollatzResearch.WordTrace]
  refine ⟨51084479928833027159801687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34056319952555351439867791 51084479928833027159801687)
  ·
    refine ⟨76626719893249540739702531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51084479928833027159801687 76626719893249540739702531)
    ·
      refine ⟨114940079839874311109553797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76626719893249540739702531 114940079839874311109553797)
      ·
        refine ⟨21551264969976433333041337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 114940079839874311109553797 21551264969976433333041337)
        ·
          refine ⟨16163448727482324999781003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21551264969976433333041337 16163448727482324999781003)
          ·
            refine ⟨24245173091223487499671505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16163448727482324999781003 24245173091223487499671505)
            ·
              refine ⟨18183879818417615624753629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24245173091223487499671505 18183879818417615624753629)
              ·
                refine ⟨6818954931906605859282611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18183879818417615624753629 6818954931906605859282611)
                ·
                  refine ⟨10228432397859908788923917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6818954931906605859282611 10228432397859908788923917)
                  ·
                    refine ⟨3835662149197465795846469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10228432397859908788923917 3835662149197465795846469)
                    ·
                      refine ⟨719186652974524836721213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3835662149197465795846469 719186652974524836721213)
                      ·
                        rfl

theorem cell23_1400611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1400611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400611 prefixEnd_1400611 := by exact prefixLift 1400611
  have htrace : WordTrace (prefixWord ++ tailWord_1400611) baseStart_1400611 baseEnd_1400611 := by
    simpa [prefixWord, tailWord_1400611, baseEnd_1400611] using wordTrace_append hprefix tailTrace_1400611
  have hstable : (prefixWord ++ tailWord_1400611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400611).length < 2 ^ (prefixWord ++ tailWord_1400611).sum := by decide
  have hdescent : baseEnd_1400611 < baseStart_1400611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400629 : List Nat := [1, 3, 3, 1, 5, 1, 2, 2, 5]
def baseStart_1400629 : Nat := 118140960795 + 1400629 * 2 ^ 59
def prefixEnd_1400629 : Nat := 4983230072969 + 3 ^ 40 * 1400629 * 2
def baseEnd_1400629 : Nat := 79910655069589529588459

theorem tailTrace_1400629 : CollatzResearch.WordTrace tailWord_1400629 prefixEnd_1400629 79910655069589529588459 := by
  unfold tailWord_1400629
  simp only [CollatzResearch.WordTrace]
  refine ⟨51085136442767816233956941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34056757628511877489304627 51085136442767816233956941)
  ·
    refine ⟨19156926166037931087733853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51085136442767816233956941 19156926166037931087733853)
    ·
      refine ⟨7183847312264224157900195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19156926166037931087733853 7183847312264224157900195)
      ·
        refine ⟨10775770968396336236850293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7183847312264224157900195 10775770968396336236850293)
        ·
          refine ⟨1010228528287156522204715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10775770968396336236850293 1010228528287156522204715)
          ·
            refine ⟨1515342792430734783307073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010228528287156522204715 1515342792430734783307073)
            ·
              refine ⟨1136507094323051087480305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515342792430734783307073 1136507094323051087480305)
              ·
                refine ⟨852380320742288315610229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136507094323051087480305 852380320742288315610229)
                ·
                  refine ⟨79910655069589529588459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852380320742288315610229 79910655069589529588459)
                  ·
                    rfl

theorem cell23_1400629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_1400629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400629 prefixEnd_1400629 := by exact prefixLift 1400629
  have htrace : WordTrace (prefixWord ++ tailWord_1400629) baseStart_1400629 baseEnd_1400629 := by
    simpa [prefixWord, tailWord_1400629, baseEnd_1400629] using wordTrace_append hprefix tailTrace_1400629
  have hstable : (prefixWord ++ tailWord_1400629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400629).length < 2 ^ (prefixWord ++ tailWord_1400629).sum := by decide
  have hdescent : baseEnd_1400629 < baseStart_1400629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400672 : List Nat := [2, 1, 1, 3, 3, 3, 2, 3, 1, 4]
def baseStart_1400672 : Nat := 118140960795 + 1400672 * 2 ^ 59
def prefixEnd_1400672 : Nat := 4983230072969 + 3 ^ 40 * 1400672 * 2
def baseEnd_1400672 : Nat := 239739325098149699352811

theorem tailTrace_1400672 : CollatzResearch.WordTrace tailWord_1400672 prefixEnd_1400672 239739325098149699352811 := by
  unfold tailWord_1400672
  simp only [CollatzResearch.WordTrace]
  refine ⟨25543352390806017288886135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34057803187741356385181513 25543352390806017288886135)
  ·
    refine ⟨38315028586209025933329203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25543352390806017288886135 38315028586209025933329203)
    ·
      refine ⟨57472542879313538899993805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38315028586209025933329203 57472542879313538899993805)
      ·
        refine ⟨21552203579742577087497677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57472542879313538899993805 21552203579742577087497677)
        ·
          refine ⟨8082076342403466407811629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21552203579742577087497677 8082076342403466407811629)
          ·
            refine ⟨3030778628401299902929361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8082076342403466407811629 3030778628401299902929361)
            ·
              refine ⟨2273083971300974927197021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3030778628401299902929361 2273083971300974927197021)
              ·
                refine ⟨852406489237865597698883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2273083971300974927197021 852406489237865597698883)
                ·
                  refine ⟨1278609733856798396548325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852406489237865597698883 1278609733856798396548325)
                  ·
                    refine ⟨239739325098149699352811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1278609733856798396548325 239739325098149699352811)
                    ·
                      rfl

theorem cell23_1400672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 3, 1, 4].length) (baseStart_1400672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400672 prefixEnd_1400672 := by exact prefixLift 1400672
  have htrace : WordTrace (prefixWord ++ tailWord_1400672) baseStart_1400672 baseEnd_1400672 := by
    simpa [prefixWord, tailWord_1400672, baseEnd_1400672] using wordTrace_append hprefix tailTrace_1400672
  have hstable : (prefixWord ++ tailWord_1400672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400672).length < 2 ^ (prefixWord ++ tailWord_1400672).sum := by decide
  have hdescent : baseEnd_1400672 < baseStart_1400672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400722 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1400722 : Nat := 118140960795 + 1400722 * 2 ^ 59
def prefixEnd_1400722 : Nat := 4983230072969 + 3 ^ 40 * 1400722 * 2
def baseEnd_1400722 : Nat := 719243649327173902433203

theorem tailTrace_1400722 : CollatzResearch.WordTrace tailWord_1400722 prefixEnd_1400722 719243649327173902433203 := by
  unfold tailWord_1400722
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772132107857723279273105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34059018954287262078061613 12772132107857723279273105)
  ·
    refine ⟨9579099080893292459454829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12772132107857723279273105 9579099080893292459454829)
    ·
      refine ⟨3592162155334984672295561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9579099080893292459454829 3592162155334984672295561)
      ·
        refine ⟨2694121616501238504221671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3592162155334984672295561 2694121616501238504221671)
        ·
          refine ⟨4041182424751857756332507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694121616501238504221671 4041182424751857756332507)
          ·
            refine ⟨6061773637127786634498761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4041182424751857756332507 6061773637127786634498761)
            ·
              refine ⟨4546330227845839975874071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6061773637127786634498761 4546330227845839975874071)
              ·
                refine ⟨6819495341768759963811107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4546330227845839975874071 6819495341768759963811107)
                ·
                  refine ⟨10229243012653139945716661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6819495341768759963811107 10229243012653139945716661)
                  ·
                    refine ⟨958991532436231869910937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10229243012653139945716661 958991532436231869910937)
                    ·
                      refine ⟨719243649327173902433203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 958991532436231869910937 719243649327173902433203)
                      ·
                        rfl

theorem cell23_1400722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1400722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400722 prefixEnd_1400722 := by exact prefixLift 1400722
  have htrace : WordTrace (prefixWord ++ tailWord_1400722) baseStart_1400722 baseEnd_1400722 := by
    simpa [prefixWord, tailWord_1400722, baseEnd_1400722] using wordTrace_append hprefix tailTrace_1400722
  have hstable : (prefixWord ++ tailWord_1400722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400722).length < 2 ^ (prefixWord ++ tailWord_1400722).sum := by decide
  have hdescent : baseEnd_1400722 < baseStart_1400722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400785 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_1400785 : Nat := 118140960795 + 1400785 * 2 ^ 59
def prefixEnd_1400785 : Nat := 4983230072969 + 3 ^ 40 * 1400785 * 2
def baseEnd_1400785 : Nat := 719275998608407155945413

theorem tailTrace_1400785 : CollatzResearch.WordTrace tailWord_1400785 prefixEnd_1400785 719275998608407155945413 := by
  unfold tailWord_1400785
  simp only [CollatzResearch.WordTrace]
  refine ⟨51090826230202654876635809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34060550820135103251090539 51090826230202654876635809)
  ·
    refine ⟨38318119672651991157476857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51090826230202654876635809 38318119672651991157476857)
    ·
      refine ⟨28738589754488993368107643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38318119672651991157476857 28738589754488993368107643)
      ·
        refine ⟨43107884631733490052161465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28738589754488993368107643 43107884631733490052161465)
        ·
          refine ⟨32330913473800117539121099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43107884631733490052161465 32330913473800117539121099)
          ·
            refine ⟨48496370210700176308681649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32330913473800117539121099 48496370210700176308681649)
            ·
              refine ⟨36372277658025132231511237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48496370210700176308681649 36372277658025132231511237)
              ·
                refine ⟨6819802060879712293408357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36372277658025132231511237 6819802060879712293408357)
                ·
                  refine ⟨1278712886414946055014067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6819802060879712293408357 1278712886414946055014067)
                  ·
                    refine ⟨1918069329622419082521101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1278712886414946055014067 1918069329622419082521101)
                    ·
                      refine ⟨719275998608407155945413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918069329622419082521101 719275998608407155945413)
                      ·
                        rfl

theorem cell23_1400785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_1400785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400785 prefixEnd_1400785 := by exact prefixLift 1400785
  have htrace : WordTrace (prefixWord ++ tailWord_1400785) baseStart_1400785 baseEnd_1400785 := by
    simpa [prefixWord, tailWord_1400785, baseEnd_1400785] using wordTrace_append hprefix tailTrace_1400785
  have hstable : (prefixWord ++ tailWord_1400785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400785).length < 2 ^ (prefixWord ++ tailWord_1400785).sum := by decide
  have hdescent : baseEnd_1400785 < baseStart_1400785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400789 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1400789 : Nat := 118140960795 + 1400789 * 2 ^ 59
def prefixEnd_1400789 : Nat := 4983230072969 + 3 ^ 40 * 1400789 * 2
def baseEnd_1400789 : Nat := 719278052531025140295395

theorem tailTrace_1400789 : CollatzResearch.WordTrace tailWord_1400789 prefixEnd_1400789 719278052531025140295395 := by
  unfold tailWord_1400789
  simp only [CollatzResearch.WordTrace]
  refine ⟨51090972122188163559781421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34060648081458775706520947 51090972122188163559781421)
  ·
    refine ⟨19159114545820561334918033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51090972122188163559781421 19159114545820561334918033)
    ·
      refine ⟨14369335909365421001188525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19159114545820561334918033 14369335909365421001188525)
      ·
        refine ⟨5388500966012032875445697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14369335909365421001188525 5388500966012032875445697)
        ·
          refine ⟨4041375724509024656584273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5388500966012032875445697 4041375724509024656584273)
          ·
            refine ⟨3031031793381768492438205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041375724509024656584273 3031031793381768492438205)
            ·
              refine ⟨1136636922518163184664327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3031031793381768492438205 1136636922518163184664327)
              ·
                refine ⟨1704955383777244776996491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136636922518163184664327 1704955383777244776996491)
                ·
                  refine ⟨2557433075665867165494737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1704955383777244776996491 2557433075665867165494737)
                  ·
                    refine ⟨1918074806749400374121053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2557433075665867165494737 1918074806749400374121053)
                    ·
                      refine ⟨719278052531025140295395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918074806749400374121053 719278052531025140295395)
                      ·
                        rfl

theorem cell23_1400789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1400789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400789 prefixEnd_1400789 := by exact prefixLift 1400789
  have htrace : WordTrace (prefixWord ++ tailWord_1400789) baseStart_1400789 baseEnd_1400789 := by
    simpa [prefixWord, tailWord_1400789, baseEnd_1400789] using wordTrace_append hprefix tailTrace_1400789
  have hstable : (prefixWord ++ tailWord_1400789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400789).length < 2 ^ (prefixWord ++ tailWord_1400789).sum := by decide
  have hdescent : baseEnd_1400789 < baseStart_1400789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400803 : List Nat := [1, 1, 1, 6, 1, 4, 2, 2, 1, 2, 2]
def baseStart_1400803 : Nat := 118140960795 + 1400803 * 2 ^ 59
def prefixEnd_1400803 : Nat := 4983230072969 + 3 ^ 40 * 1400803 * 2
def baseEnd_1400803 : Nat := 719285241260188085520331

theorem tailTrace_1400803 : CollatzResearch.WordTrace tailWord_1400803 prefixEnd_1400803 719285241260188085520331 := by
  unfold tailWord_1400803
  simp only [CollatzResearch.WordTrace]
  refine ⟨51091482744137443950791063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34060988496091629300527375 51091482744137443950791063)
  ·
    refine ⟨76637224116206165926186595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51091482744137443950791063 76637224116206165926186595)
    ·
      refine ⟨114955836174309248889279893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76637224116206165926186595 114955836174309248889279893)
      ·
        refine ⟨5388554820670746041684995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114955836174309248889279893 5388554820670746041684995)
        ·
          refine ⟨8082832231006119062527493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5388554820670746041684995 8082832231006119062527493)
          ·
            refine ⟨1515531043313647324223905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8082832231006119062527493 1515531043313647324223905)
            ·
              refine ⟨1136648282485235493167929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1515531043313647324223905 1136648282485235493167929)
              ·
                refine ⟨852486211863926619875947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136648282485235493167929 852486211863926619875947)
                ·
                  refine ⟨1278729317795889929813921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852486211863926619875947 1278729317795889929813921)
                  ·
                    refine ⟨959046988346917447360441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1278729317795889929813921 959046988346917447360441)
                    ·
                      refine ⟨719285241260188085520331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959046988346917447360441 719285241260188085520331)
                      ·
                        rfl

theorem cell23_1400803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_1400803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400803 prefixEnd_1400803 := by exact prefixLift 1400803
  have htrace : WordTrace (prefixWord ++ tailWord_1400803) baseStart_1400803 baseEnd_1400803 := by
    simpa [prefixWord, tailWord_1400803, baseEnd_1400803] using wordTrace_append hprefix tailTrace_1400803
  have hstable : (prefixWord ++ tailWord_1400803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400803).length < 2 ^ (prefixWord ++ tailWord_1400803).sum := by decide
  have hdescent : baseEnd_1400803 < baseStart_1400803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400932 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 2, 4, 2]
def baseStart_1400932 : Nat := 118140960795 + 1400932 * 2 ^ 59
def prefixEnd_1400932 : Nat := 4983230072969 + 3 ^ 40 * 1400932 * 2
def baseEnd_1400932 : Nat := 719351480264618080807237

theorem tailTrace_1400932 : CollatzResearch.WordTrace tailWord_1400932 prefixEnd_1400932 719351480264618080807237 := by
  unfold tailWord_1400932
  simp only [CollatzResearch.WordTrace]
  refine ⟨25548093880335049491118525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34064125173780065988158033 25548093880335049491118525)
  ·
    refine ⟨9580535205125643559169447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25548093880335049491118525 9580535205125643559169447)
    ·
      refine ⟨14370802807688465338754171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9580535205125643559169447 14370802807688465338754171)
      ·
        refine ⟨21556204211532698008131257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14370802807688465338754171 21556204211532698008131257)
        ·
          refine ⟨16167153158649523506098443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21556204211532698008131257 16167153158649523506098443)
          ·
            refine ⟨24250729737974285259147665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16167153158649523506098443 24250729737974285259147665)
            ·
              refine ⟨18188047303480713944360749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24250729737974285259147665 18188047303480713944360749)
              ·
                refine ⟨6820517738805267729135281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18188047303480713944360749 6820517738805267729135281)
                ·
                  refine ⟨5115388304103950796851461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6820517738805267729135281 5115388304103950796851461)
                  ·
                    refine ⟨959135307019490774409649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5115388304103950796851461 959135307019490774409649)
                    ·
                      refine ⟨719351480264618080807237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959135307019490774409649 719351480264618080807237)
                      ·
                        rfl

theorem cell23_1400932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 4, 2].length) (baseStart_1400932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400932 prefixEnd_1400932 := by exact prefixLift 1400932
  have htrace : WordTrace (prefixWord ++ tailWord_1400932) baseStart_1400932 baseEnd_1400932 := by
    simpa [prefixWord, tailWord_1400932, baseEnd_1400932] using wordTrace_append hprefix tailTrace_1400932
  have hstable : (prefixWord ++ tailWord_1400932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400932).length < 2 ^ (prefixWord ++ tailWord_1400932).sum := by decide
  have hdescent : baseEnd_1400932 < baseStart_1400932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1400942 : List Nat := [4, 1, 2, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1400942 : Nat := 118140960795 + 1400942 * 2 ^ 59
def prefixEnd_1400942 : Nat := 4983230072969 + 3 ^ 40 * 1400942 * 2
def baseEnd_1400942 : Nat := 239785538357054347227397

theorem tailTrace_1400942 : CollatzResearch.WordTrace tailWord_1400942 prefixEnd_1400942 239785538357054347227397 := by
  unfold tailWord_1400942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6387069061329233836262635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34064368327089247126734053 6387069061329233836262635)
  ·
    refine ⟨9580603591993850754393953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6387069061329233836262635 9580603591993850754393953)
    ·
      refine ⟨7185452693995388065795465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9580603591993850754393953 7185452693995388065795465)
      ·
        refine ⟨5389089520496541049346599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7185452693995388065795465 5389089520496541049346599)
        ·
          refine ⟨8083634280744811574019899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389089520496541049346599 8083634280744811574019899)
          ·
            refine ⟨12125451421117217361029849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8083634280744811574019899 12125451421117217361029849)
            ·
              refine ⟨9094088565837913020772387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12125451421117217361029849 9094088565837913020772387)
              ·
                refine ⟨13641132848756869531158581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9094088565837913020772387 13641132848756869531158581)
                ·
                  refine ⟨1278856204570956518546117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13641132848756869531158581 1278856204570956518546117)
                  ·
                    refine ⟨239785538357054347227397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1278856204570956518546117 239785538357054347227397)
                    ·
                      rfl

theorem cell23_1400942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1400942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1400942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1400942 prefixEnd_1400942 := by exact prefixLift 1400942
  have htrace : WordTrace (prefixWord ++ tailWord_1400942) baseStart_1400942 baseEnd_1400942 := by
    simpa [prefixWord, tailWord_1400942, baseEnd_1400942] using wordTrace_append hprefix tailTrace_1400942
  have hstable : (prefixWord ++ tailWord_1400942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1400942).length < 2 ^ (prefixWord ++ tailWord_1400942).sum := by decide
  have hdescent : baseEnd_1400942 < baseStart_1400942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1400942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401016 : List Nat := [2, 1, 2, 1, 2, 1, 6, 3, 1, 1, 3]
def baseStart_1401016 : Nat := 118140960795 + 1401016 * 2 ^ 59
def prefixEnd_1401016 : Nat := 4983230072969 + 3 ^ 40 * 1401016 * 2
def baseEnd_1401016 : Nat := 719394612639595752156851

theorem tailTrace_1401016 : CollatzResearch.WordTrace tailWord_1401016 prefixEnd_1401016 719394612639595752156851 := by
  unfold tailWord_1401016
  simp only [CollatzResearch.WordTrace]
  refine ⟨25549625746182890664147451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34066167661577187552196601 25549625746182890664147451)
  ·
    refine ⟨38324438619274335996221177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25549625746182890664147451 38324438619274335996221177)
    ·
      refine ⟨28743328964455751997165883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38324438619274335996221177 28743328964455751997165883)
      ·
        refine ⟨43114993446683627995748825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28743328964455751997165883 43114993446683627995748825)
        ·
          refine ⟨32336245085012720996811619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43114993446683627995748825 32336245085012720996811619)
          ·
            refine ⟨48504367627519081495217429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32336245085012720996811619 48504367627519081495217429)
            ·
              refine ⟨2273642232539956945088317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48504367627519081495217429 2273642232539956945088317)
              ·
                refine ⟨852615837202483854408119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2273642232539956945088317 852615837202483854408119)
                ·
                  refine ⟨1278923755803725781612179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852615837202483854408119 1278923755803725781612179)
                  ·
                    refine ⟨1918385633705588672418269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1278923755803725781612179 1918385633705588672418269)
                    ·
                      refine ⟨719394612639595752156851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918385633705588672418269 719394612639595752156851)
                      ·
                        rfl

theorem cell23_1401016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 1, 3].length) (baseStart_1401016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401016 prefixEnd_1401016 := by exact prefixLift 1401016
  have htrace : WordTrace (prefixWord ++ tailWord_1401016) baseStart_1401016 baseEnd_1401016 := by
    simpa [prefixWord, tailWord_1401016, baseEnd_1401016] using wordTrace_append hprefix tailTrace_1401016
  have hstable : (prefixWord ++ tailWord_1401016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401016).length < 2 ^ (prefixWord ++ tailWord_1401016).sum := by decide
  have hdescent : baseEnd_1401016 < baseStart_1401016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401035 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6]
def baseStart_1401035 : Nat := 118140960795 + 1401035 * 2 ^ 59
def prefixEnd_1401035 : Nat := 4983230072969 + 3 ^ 40 * 1401035 * 2
def baseEnd_1401035 : Nat := 719404368772031177819263

theorem tailTrace_1401035 : CollatzResearch.WordTrace tailWord_1401035 prefixEnd_1401035 719404368772031177819263 := by
  unfold tailWord_1401035
  simp only [CollatzResearch.WordTrace]
  refine ⟨51099944479296947573236559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34066629652864631715491039 51099944479296947573236559)
  ·
    refine ⟨76649916718945421359854839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51099944479296947573236559 76649916718945421359854839)
    ·
      refine ⟨114974875078418132039782259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76649916718945421359854839 114974875078418132039782259)
      ·
        refine ⟨172462312617627198059673389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114974875078418132039782259 172462312617627198059673389)
        ·
          refine ⟨64673367231610199272377521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172462312617627198059673389 64673367231610199272377521)
          ·
            refine ⟨48505025423707649454283141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64673367231610199272377521 48505025423707649454283141)
            ·
              refine ⟨9094692266945184272678089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48505025423707649454283141 9094692266945184272678089)
              ·
                refine ⟨6821019200208888204508567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9094692266945184272678089 6821019200208888204508567)
                ·
                  refine ⟨10231528800313332306762851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6821019200208888204508567 10231528800313332306762851)
                  ·
                    refine ⟨15347293200469998460144277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10231528800313332306762851 15347293200469998460144277)
                    ·
                      refine ⟨719404368772031177819263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15347293200469998460144277 719404368772031177819263)
                      ·
                        rfl

theorem cell23_1401035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_1401035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401035 prefixEnd_1401035 := by exact prefixLift 1401035
  have htrace : WordTrace (prefixWord ++ tailWord_1401035) baseStart_1401035 baseEnd_1401035 := by
    simpa [prefixWord, tailWord_1401035, baseEnd_1401035] using wordTrace_append hprefix tailTrace_1401035
  have hstable : (prefixWord ++ tailWord_1401035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401035).length < 2 ^ (prefixWord ++ tailWord_1401035).sum := by decide
  have hdescent : baseEnd_1401035 < baseStart_1401035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401042 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1401042 : Nat := 118140960795 + 1401042 * 2 ^ 59
def prefixEnd_1401042 : Nat := 4983230072969 + 3 ^ 40 * 1401042 * 2
def baseEnd_1401042 : Nat := 719407963136612650431731

theorem tailTrace_1401042 : CollatzResearch.WordTrace tailWord_1401042 prefixEnd_1401042 719407963136612650431731 := by
  unfold tailWord_1401042
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775049947567896942185345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34066799860181058512494253 12775049947567896942185345)
  ·
    refine ⟨9581287460675922706639009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12775049947567896942185345 9581287460675922706639009)
    ·
      refine ⟨7185965595506942029979257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9581287460675922706639009 7185965595506942029979257)
      ·
        refine ⟨5389474196630206522484443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7185965595506942029979257 5389474196630206522484443)
        ·
          refine ⟨8084211294945309783726665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5389474196630206522484443 8084211294945309783726665)
          ·
            refine ⟨6063158471208982337794999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8084211294945309783726665 6063158471208982337794999)
            ·
              refine ⟨9094737706813473506692499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6063158471208982337794999 9094737706813473506692499)
              ·
                refine ⟨13642106560220210260038749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9094737706813473506692499 13642106560220210260038749)
                ·
                  refine ⟨5115789960082578847514531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13642106560220210260038749 5115789960082578847514531)
                  ·
                    refine ⟨7673684940123868271271797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5115789960082578847514531 7673684940123868271271797)
                    ·
                      refine ⟨719407963136612650431731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7673684940123868271271797 719407963136612650431731)
                      ·
                        rfl

theorem cell23_1401042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1401042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401042 prefixEnd_1401042 := by exact prefixLift 1401042
  have htrace : WordTrace (prefixWord ++ tailWord_1401042) baseStart_1401042 baseEnd_1401042 := by
    simpa [prefixWord, tailWord_1401042, baseEnd_1401042] using wordTrace_append hprefix tailTrace_1401042
  have hstable : (prefixWord ++ tailWord_1401042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401042).length < 2 ^ (prefixWord ++ tailWord_1401042).sum := by decide
  have hdescent : baseEnd_1401042 < baseStart_1401042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401072 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3]
def baseStart_1401072 : Nat := 118140960795 + 1401072 * 2 ^ 59
def prefixEnd_1401072 : Nat := 4983230072969 + 3 ^ 40 * 1401072 * 2
def baseEnd_1401072 : Nat := 719423367556247533056593

theorem tailTrace_1401072 : CollatzResearch.WordTrace tailWord_1401072 prefixEnd_1401072 719423367556247533056593 := by
  unfold tailWord_1401072
  simp only [CollatzResearch.WordTrace]
  refine ⟨25550646990081451446166735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34067529320108601928222313 25550646990081451446166735)
  ·
    refine ⟨38325970485122177169250103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25550646990081451446166735 38325970485122177169250103)
    ·
      refine ⟨57488955727683265753875155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38325970485122177169250103 57488955727683265753875155)
      ·
        refine ⟨86233433591524898630812733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57488955727683265753875155 86233433591524898630812733)
        ·
          refine ⟨32337537596821836986554775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86233433591524898630812733 32337537596821836986554775)
          ·
            refine ⟨48506306395232755479832163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32337537596821836986554775 48506306395232755479832163)
            ·
              refine ⟨72759459592849133219748245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48506306395232755479832163 72759459592849133219748245)
              ·
                refine ⟨3410599668414803119675699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72759459592849133219748245 3410599668414803119675699)
                ·
                  refine ⟨5115899502622204679513549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3410599668414803119675699 5115899502622204679513549)
                  ·
                    refine ⟨1918462313483326754817581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5115899502622204679513549 1918462313483326754817581)
                    ·
                      refine ⟨719423367556247533056593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918462313483326754817581 719423367556247533056593)
                      ·
                        rfl

theorem cell23_1401072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_1401072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401072 prefixEnd_1401072 := by exact prefixLift 1401072
  have htrace : WordTrace (prefixWord ++ tailWord_1401072) baseStart_1401072 baseEnd_1401072 := by
    simpa [prefixWord, tailWord_1401072, baseEnd_1401072] using wordTrace_append hprefix tailTrace_1401072
  have hstable : (prefixWord ++ tailWord_1401072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401072).length < 2 ^ (prefixWord ++ tailWord_1401072).sum := by decide
  have hdescent : baseEnd_1401072 < baseStart_1401072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401073 : List Nat := [1, 2, 2, 2, 2, 1, 5, 3, 1, 2, 2]
def baseStart_1401073 : Nat := 118140960795 + 1401073 * 2 ^ 59
def prefixEnd_1401073 : Nat := 4983230072969 + 3 ^ 40 * 1401073 * 2
def baseEnd_1401073 : Nat := 719423881036902029144089

theorem tailTrace_1401073 : CollatzResearch.WordTrace tailWord_1401073 prefixEnd_1401073 719423881036902029144089 := by
  unfold tailWord_1401073
  simp only [CollatzResearch.WordTrace]
  refine ⟨51101330453159280063119873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34067553635439520042079915 51101330453159280063119873)
  ·
    refine ⟨38325997839869460047339905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51101330453159280063119873 38325997839869460047339905)
    ·
      refine ⟨28744498379902095035504929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38325997839869460047339905 28744498379902095035504929)
      ·
        refine ⟨21558373784926571276628697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28744498379902095035504929 21558373784926571276628697)
        ·
          refine ⟨16168780338694928457471523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21558373784926571276628697 16168780338694928457471523)
          ·
            refine ⟨24253170508042392686207285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16168780338694928457471523 24253170508042392686207285)
            ·
              refine ⟨2273734735128974314331933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24253170508042392686207285 2273734735128974314331933)
              ·
                refine ⟨852650525673365367874475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2273734735128974314331933 852650525673365367874475)
                ·
                  refine ⟨1278975788510048051811713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852650525673365367874475 1278975788510048051811713)
                  ·
                    refine ⟨959231841382536038858785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1278975788510048051811713 959231841382536038858785)
                    ·
                      refine ⟨719423881036902029144089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959231841382536038858785 719423881036902029144089)
                      ·
                        rfl

theorem cell23_1401073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_1401073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401073 prefixEnd_1401073 := by exact prefixLift 1401073
  have htrace : WordTrace (prefixWord ++ tailWord_1401073) baseStart_1401073 baseEnd_1401073 := by
    simpa [prefixWord, tailWord_1401073, baseEnd_1401073] using wordTrace_append hprefix tailTrace_1401073
  have hstable : (prefixWord ++ tailWord_1401073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401073).length < 2 ^ (prefixWord ++ tailWord_1401073).sum := by decide
  have hdescent : baseEnd_1401073 < baseStart_1401073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401089 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1401089 : Nat := 118140960795 + 1401089 * 2 ^ 59
def prefixEnd_1401089 : Nat := 4983230072969 + 3 ^ 40 * 1401089 * 2
def baseEnd_1401089 : Nat := 719432096727373966544015

theorem tailTrace_1401089 : CollatzResearch.WordTrace tailWord_1401089 prefixEnd_1401089 719432096727373966544015 := by
  unfold tailWord_1401089
  simp only [CollatzResearch.WordTrace]
  refine ⟨51101914021101314795702321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34067942680734209863801547 51101914021101314795702321)
  ·
    refine ⟨38326435515825986096776741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51101914021101314795702321 38326435515825986096776741)
    ·
      refine ⟨7186206659217372393145639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38326435515825986096776741 7186206659217372393145639)
      ·
        refine ⟨10779309988826058589718459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7186206659217372393145639 10779309988826058589718459)
        ·
          refine ⟨16168964983239087884577689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10779309988826058589718459 16168964983239087884577689)
          ·
            refine ⟨12126723737429315913433267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16168964983239087884577689 12126723737429315913433267)
            ·
              refine ⟨18190085606143973870149901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12126723737429315913433267 18190085606143973870149901)
              ·
                refine ⟨6821282102303990201306213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18190085606143973870149901 6821282102303990201306213)
                ·
                  refine ⟨1278990394181998162744915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6821282102303990201306213 1278990394181998162744915)
                  ·
                    refine ⟨1918485591272997244117373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1278990394181998162744915 1918485591272997244117373)
                    ·
                      refine ⟨719432096727373966544015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918485591272997244117373 719432096727373966544015)
                      ·
                        rfl

theorem cell23_1401089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1401089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401089 prefixEnd_1401089 := by exact prefixLift 1401089
  have htrace : WordTrace (prefixWord ++ tailWord_1401089) baseStart_1401089 baseEnd_1401089 := by
    simpa [prefixWord, tailWord_1401089, baseEnd_1401089] using wordTrace_append hprefix tailTrace_1401089
  have hstable : (prefixWord ++ tailWord_1401089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401089).length < 2 ^ (prefixWord ++ tailWord_1401089).sum := by decide
  have hdescent : baseEnd_1401089 < baseStart_1401089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401090 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_1401090 : Nat := 118140960795 + 1401090 * 2 ^ 59
def prefixEnd_1401090 : Nat := 4983230072969 + 3 ^ 40 * 1401090 * 2
def baseEnd_1401090 : Nat := 719432610208028462631511

theorem tailTrace_1401090 : CollatzResearch.WordTrace tailWord_1401090 prefixEnd_1401090 719432610208028462631511 := by
  unfold tailWord_1401090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775487623524422991622181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34067966996065127977659149 12775487623524422991622181)
  ·
    refine ⟨2395403929410829310929159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12775487623524422991622181 2395403929410829310929159)
    ·
      refine ⟨3593105894116243966393739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395403929410829310929159 3593105894116243966393739)
      ·
        refine ⟨5389658841174365949590609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593105894116243966393739 5389658841174365949590609)
        ·
          refine ⟨4042244130880774462192957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5389658841174365949590609 4042244130880774462192957)
          ·
            refine ⟨1515841549080290423322359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4042244130880774462192957 1515841549080290423322359)
            ·
              refine ⟨2273762323620435634983539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515841549080290423322359 2273762323620435634983539)
              ·
                refine ⟨3410643485430653452475309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273762323620435634983539 3410643485430653452475309)
                ·
                  refine ⟨1278991307036495044678241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3410643485430653452475309 1278991307036495044678241)
                  ·
                    refine ⟨959243480277371283508681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1278991307036495044678241 959243480277371283508681)
                    ·
                      refine ⟨719432610208028462631511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959243480277371283508681 719432610208028462631511)
                      ·
                        rfl

theorem cell23_1401090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_1401090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401090 prefixEnd_1401090 := by exact prefixLift 1401090
  have htrace : WordTrace (prefixWord ++ tailWord_1401090) baseStart_1401090 baseEnd_1401090 := by
    simpa [prefixWord, tailWord_1401090, baseEnd_1401090] using wordTrace_append hprefix tailTrace_1401090
  have hstable : (prefixWord ++ tailWord_1401090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401090).length < 2 ^ (prefixWord ++ tailWord_1401090).sum := by decide
  have hdescent : baseEnd_1401090 < baseStart_1401090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401099 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 3, 3, 2]
def baseStart_1401099 : Nat := 118140960795 + 1401099 * 2 ^ 59
def prefixEnd_1401099 : Nat := 4983230072969 + 3 ^ 40 * 1401099 * 2
def baseEnd_1401099 : Nat := 719437231533918927418969

theorem tailTrace_1401099 : CollatzResearch.WordTrace tailWord_1401099 prefixEnd_1401099 719437231533918927418969 := by
  unfold tailWord_1401099
  simp only [CollatzResearch.WordTrace]
  refine ⟨51102278751065086503566351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34068185834043391002377567 51102278751065086503566351)
  ·
    refine ⟨76653418126597629755349527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51102278751065086503566351 76653418126597629755349527)
    ·
      refine ⟨114980127189896444633024291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76653418126597629755349527 114980127189896444633024291)
      ·
        refine ⟨172470190784844666949536437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114980127189896444633024291 172470190784844666949536437)
        ·
          refine ⟨16169080386079187526519041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172470190784844666949536437 16169080386079187526519041)
          ·
            refine ⟨12126810289559390644889281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16169080386079187526519041 12126810289559390644889281)
            ·
              refine ⟨9095107717169542983666961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12126810289559390644889281 9095107717169542983666961)
              ·
                refine ⟨6821330787877157237750221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9095107717169542983666961 6821330787877157237750221)
                ·
                  refine ⟨2557999045453933964156333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6821330787877157237750221 2557999045453933964156333)
                  ·
                    refine ⟨959249642045225236558625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2557999045453933964156333 959249642045225236558625)
                    ·
                      refine ⟨719437231533918927418969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959249642045225236558625 719437231533918927418969)
                      ·
                        rfl

theorem cell23_1401099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 3, 2].length) (baseStart_1401099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401099 prefixEnd_1401099 := by exact prefixLift 1401099
  have htrace : WordTrace (prefixWord ++ tailWord_1401099) baseStart_1401099 baseEnd_1401099 := by
    simpa [prefixWord, tailWord_1401099, baseEnd_1401099] using wordTrace_append hprefix tailTrace_1401099
  have hstable : (prefixWord ++ tailWord_1401099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401099).length < 2 ^ (prefixWord ++ tailWord_1401099).sum := by decide
  have hdescent : baseEnd_1401099 < baseStart_1401099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401127 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1401127 : Nat := 118140960795 + 1401127 * 2 ^ 59
def prefixEnd_1401127 : Nat := 4983230072969 + 3 ^ 40 * 1401127 * 2
def baseEnd_1401127 : Nat := 719451608992244817868841

theorem tailTrace_1401127 : CollatzResearch.WordTrace tailWord_1401127 prefixEnd_1401127 719451608992244817868841 := by
  unfold tailWord_1401127
  simp only [CollatzResearch.WordTrace]
  refine ⟨51103299994963647285585635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34068866663309098190390423 51103299994963647285585635)
  ·
    refine ⟨76654949992445470928378453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51103299994963647285585635 76654949992445470928378453)
    ·
      refine ⟨898300195223970362441935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 76654949992445470928378453 898300195223970362441935)
      ·
        refine ⟨1347450292835955543662903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898300195223970362441935 1347450292835955543662903)
        ·
          refine ⟨2021175439253933315494355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347450292835955543662903 2021175439253933315494355)
          ·
            refine ⟨3031763158880899973241533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021175439253933315494355 3031763158880899973241533)
            ·
              refine ⟨1136911184580337489965575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3031763158880899973241533 1136911184580337489965575)
              ·
                refine ⟨1705366776870506234948363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136911184580337489965575 1705366776870506234948363)
                ·
                  refine ⟨2558050165305759352422545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705366776870506234948363 2558050165305759352422545)
                  ·
                    refine ⟨1918537623979319514316909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2558050165305759352422545 1918537623979319514316909)
                    ·
                      refine ⟨719451608992244817868841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918537623979319514316909 719451608992244817868841)
                      ·
                        rfl

theorem cell23_1401127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1401127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401127 prefixEnd_1401127 := by exact prefixLift 1401127
  have htrace : WordTrace (prefixWord ++ tailWord_1401127) baseStart_1401127 baseEnd_1401127 := by
    simpa [prefixWord, tailWord_1401127, baseEnd_1401127] using wordTrace_append hprefix tailTrace_1401127
  have hstable : (prefixWord ++ tailWord_1401127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401127).length < 2 ^ (prefixWord ++ tailWord_1401127).sum := by decide
  have hdescent : baseEnd_1401127 < baseStart_1401127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401132 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_1401132 : Nat := 118140960795 + 1401132 * 2 ^ 59
def prefixEnd_1401132 : Nat := 4983230072969 + 3 ^ 40 * 1401132 * 2
def baseEnd_1401132 : Nat := 719454176395517298306317

theorem tailTrace_1401132 : CollatzResearch.WordTrace tailWord_1401132 prefixEnd_1401132 719454176395517298306317 := by
  unfold tailWord_1401132
  simp only [CollatzResearch.WordTrace]
  refine ⟨25551741179972766569758825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34068988239963688759678433 25551741179972766569758825)
  ·
    refine ⟨19163805884979574927319119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25551741179972766569758825 19163805884979574927319119)
    ·
      refine ⟨28745708827469362390978679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19163805884979574927319119 28745708827469362390978679)
      ·
        refine ⟨43118563241204043586468019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28745708827469362390978679 43118563241204043586468019)
        ·
          refine ⟨64677844861806065379702029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43118563241204043586468019 64677844861806065379702029)
          ·
            refine ⟨24254191823177274517388261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64677844861806065379702029 24254191823177274517388261)
            ·
              refine ⟨4547660966845738972010299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24254191823177274517388261 4547660966845738972010299)
              ·
                refine ⟨6821491450268608458015449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4547660966845738972010299 6821491450268608458015449)
                ·
                  refine ⟨5116118587701456343511587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6821491450268608458015449 5116118587701456343511587)
                  ·
                    refine ⟨7674177881552184515267381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5116118587701456343511587 7674177881552184515267381)
                    ·
                      refine ⟨719454176395517298306317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7674177881552184515267381 719454176395517298306317)
                      ·
                        rfl

theorem cell23_1401132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_1401132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401132 prefixEnd_1401132 := by exact prefixLift 1401132
  have htrace : WordTrace (prefixWord ++ tailWord_1401132) baseStart_1401132 baseEnd_1401132 := by
    simpa [prefixWord, tailWord_1401132, baseEnd_1401132] using wordTrace_append hprefix tailTrace_1401132
  have hstable : (prefixWord ++ tailWord_1401132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401132).length < 2 ^ (prefixWord ++ tailWord_1401132).sum := by decide
  have hdescent : baseEnd_1401132 < baseStart_1401132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401156 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_1401156 : Nat := 118140960795 + 1401156 * 2 ^ 59
def prefixEnd_1401156 : Nat := 4983230072969 + 3 ^ 40 * 1401156 * 2
def baseEnd_1401156 : Nat := 239822166643741734802069

theorem tailTrace_1401156 : CollatzResearch.WordTrace tailWord_1401156 prefixEnd_1401156 239822166643741734802069 := by
  unfold tailWord_1401156
  simp only [CollatzResearch.WordTrace]
  refine ⟨25552178855929292619195661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34069571807905723492260881 25552178855929292619195661)
  ·
    refine ⟨9582067070973484732198373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25552178855929292619195661 9582067070973484732198373)
    ·
      refine ⟨1796637575807528387287195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9582067070973484732198373 1796637575807528387287195)
      ·
        refine ⟨2694956363711292580930793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796637575807528387287195 2694956363711292580930793)
        ·
          refine ⟨2021217272783469435698095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2694956363711292580930793 2021217272783469435698095)
          ·
            refine ⟨3031825909175204153547143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021217272783469435698095 3031825909175204153547143)
            ·
              refine ⟨4547738863762806230320715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3031825909175204153547143 4547738863762806230320715)
              ·
                refine ⟨6821608295644209345481073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4547738863762806230320715 6821608295644209345481073)
                ·
                  refine ⟨5116206221733157009110805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6821608295644209345481073 5116206221733157009110805)
                  ·
                    refine ⟨239822166643741734802069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5116206221733157009110805 239822166643741734802069)
                    ·
                      rfl

theorem cell23_1401156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_1401156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401156 prefixEnd_1401156 := by exact prefixLift 1401156
  have htrace : WordTrace (prefixWord ++ tailWord_1401156) baseStart_1401156 baseEnd_1401156 := by
    simpa [prefixWord, tailWord_1401156, baseEnd_1401156] using wordTrace_append hprefix tailTrace_1401156
  have hstable : (prefixWord ++ tailWord_1401156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401156).length < 2 ^ (prefixWord ++ tailWord_1401156).sum := by decide
  have hdescent : baseEnd_1401156 < baseStart_1401156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401186 : List Nat := [3, 3, 2, 1, 1, 2, 1, 5, 5]
def baseStart_1401186 : Nat := 118140960795 + 1401186 * 2 ^ 59
def prefixEnd_1401186 : Nat := 4983230072969 + 3 ^ 40 * 1401186 * 2
def baseEnd_1401186 : Nat := 79942433816762231892341

theorem tailTrace_1401186 : CollatzResearch.WordTrace tailWord_1401186 prefixEnd_1401186 79942433816762231892341 := by
  unfold tailWord_1401186
  simp only [CollatzResearch.WordTrace]
  refine ⟨12776362975437475090495853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34070301267833266907988941 12776362975437475090495853)
  ·
    refine ⟨4791136115789053158935945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12776362975437475090495853 4791136115789053158935945)
    ·
      refine ⟨3593352086841789869201959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4791136115789053158935945 3593352086841789869201959)
      ·
        refine ⟨5390028130262684803802939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593352086841789869201959 5390028130262684803802939)
        ·
          refine ⟨8085042195394027205704409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390028130262684803802939 8085042195394027205704409)
          ·
            refine ⟨6063781646545520404278307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8085042195394027205704409 6063781646545520404278307)
            ·
              refine ⟨9095672469818280606417461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6063781646545520404278307 9095672469818280606417461)
              ·
                refine ⟨852719294045463806851637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9095672469818280606417461 852719294045463806851637)
                ·
                  refine ⟨79942433816762231892341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852719294045463806851637 79942433816762231892341)
                  ·
                    rfl

theorem cell23_1401186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_1401186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401186 prefixEnd_1401186 := by exact prefixLift 1401186
  have htrace : WordTrace (prefixWord ++ tailWord_1401186) baseStart_1401186 baseEnd_1401186 := by
    simpa [prefixWord, tailWord_1401186, baseEnd_1401186] using wordTrace_append hprefix tailTrace_1401186
  have hstable : (prefixWord ++ tailWord_1401186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401186).length < 2 ^ (prefixWord ++ tailWord_1401186).sum := by decide
  have hdescent : baseEnd_1401186 < baseStart_1401186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401239 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1401239 : Nat := 118140960795 + 1401239 * 2 ^ 59
def prefixEnd_1401239 : Nat := 4983230072969 + 3 ^ 40 * 1401239 * 2
def baseEnd_1401239 : Nat := 719509118825548379668325

theorem tailTrace_1401239 : CollatzResearch.WordTrace tailWord_1401239 prefixEnd_1401239 719509118825548379668325 := by
  unfold tailWord_1401239
  simp only [CollatzResearch.WordTrace]
  refine ⟨51107384970557890413662771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34071589980371926942441847 51107384970557890413662771)
  ·
    refine ⟨76661077455836835620494157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51107384970557890413662771 76661077455836835620494157)
    ·
      refine ⟨28747904045938813357685309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76661077455836835620494157 28747904045938813357685309)
      ·
        refine ⟨10780464017227055009131991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28747904045938813357685309 10780464017227055009131991)
        ·
          refine ⟨16170696025840582513697987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10780464017227055009131991 16170696025840582513697987)
          ·
            refine ⟨24256044038760873770546981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16170696025840582513697987 24256044038760873770546981)
            ·
              refine ⟨4548008257267663831977559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24256044038760873770546981 4548008257267663831977559)
              ·
                refine ⟨6822012385901495747966339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548008257267663831977559 6822012385901495747966339)
                ·
                  refine ⟨10233018578852243621949509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6822012385901495747966339 10233018578852243621949509)
                  ·
                    refine ⟨1918690983534795679115533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10233018578852243621949509 1918690983534795679115533)
                    ·
                      refine ⟨719509118825548379668325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918690983534795679115533 719509118825548379668325)
                      ·
                        rfl

theorem cell23_1401239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1401239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401239 prefixEnd_1401239 := by exact prefixLift 1401239
  have htrace : WordTrace (prefixWord ++ tailWord_1401239) baseStart_1401239 baseEnd_1401239 := by
    simpa [prefixWord, tailWord_1401239, baseEnd_1401239] using wordTrace_append hprefix tailTrace_1401239
  have hstable : (prefixWord ++ tailWord_1401239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401239).length < 2 ^ (prefixWord ++ tailWord_1401239).sum := by decide
  have hdescent : baseEnd_1401239 < baseStart_1401239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401272 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 2, 9]
def baseStart_1401272 : Nat := 118140960795 + 1401272 * 2 ^ 59
def prefixEnd_1401272 : Nat := 4983230072969 + 3 ^ 40 * 1401272 * 2
def baseEnd_1401272 : Nat := 239842021229048916851891

theorem tailTrace_1401272 : CollatzResearch.WordTrace tailWord_1401272 prefixEnd_1401272 239842021229048916851891 := by
  unfold tailWord_1401272
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554294289719168524807035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34072392386292224699742713 25554294289719168524807035)
  ·
    refine ⟨38331441434578752787210553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25554294289719168524807035 38331441434578752787210553)
    ·
      refine ⟨28748581075934064590407915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38331441434578752787210553 28748581075934064590407915)
      ·
        refine ⟨43122871613901096885611873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28748581075934064590407915 43122871613901096885611873)
        ·
          refine ⟨32342153710425822664208905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43122871613901096885611873 32342153710425822664208905)
          ·
            refine ⟨24256615282819366998156679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32342153710425822664208905 24256615282819366998156679)
            ·
              refine ⟨36384922924229050497235019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24256615282819366998156679 36384922924229050497235019)
              ·
                refine ⟨54577384386343575745852529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36384922924229050497235019 54577384386343575745852529)
                ·
                  refine ⟨40933038289757681809389397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54577384386343575745852529 40933038289757681809389397)
                  ·
                    refine ⟨239842021229048916851891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 40933038289757681809389397 239842021229048916851891)
                    ·
                      rfl

theorem cell23_1401272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_1401272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401272 prefixEnd_1401272 := by exact prefixLift 1401272
  have htrace : WordTrace (prefixWord ++ tailWord_1401272) baseStart_1401272 baseEnd_1401272 := by
    simpa [prefixWord, tailWord_1401272, baseEnd_1401272] using wordTrace_append hprefix tailTrace_1401272
  have hstable : (prefixWord ++ tailWord_1401272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401272).length < 2 ^ (prefixWord ++ tailWord_1401272).sum := by decide
  have hdescent : baseEnd_1401272 < baseStart_1401272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401276 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 6]
def baseStart_1401276 : Nat := 118140960795 + 1401276 * 2 ^ 59
def prefixEnd_1401276 : Nat := 4983230072969 + 3 ^ 40 * 1401276 * 2
def baseEnd_1401276 : Nat := 79947568623307192767295

theorem tailTrace_1401276 : CollatzResearch.WordTrace tailWord_1401276 prefixEnd_1401276 79947568623307192767295 := by
  unfold tailWord_1401276
  simp only [CollatzResearch.WordTrace]
  refine ⟨25554367235711922866379841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34072489647615897155173121 25554367235711922866379841)
  ·
    refine ⟨19165775426783942149784881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25554367235711922866379841 19165775426783942149784881)
    ·
      refine ⟨14374331570087956612338661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19165775426783942149784881 14374331570087956612338661)
      ·
        refine ⟨2695187169391491864813499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14374331570087956612338661 2695187169391491864813499)
        ·
          refine ⟨4042780754087237797220249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695187169391491864813499 4042780754087237797220249)
          ·
            refine ⟨3032085565565428347915187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4042780754087237797220249 3032085565565428347915187)
            ·
              refine ⟨4548128348348142521872781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032085565565428347915187 4548128348348142521872781)
              ·
                refine ⟨1705548130630553445702293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4548128348348142521872781 1705548130630553445702293)
                ·
                  refine ⟨79947568623307192767295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1705548130630553445702293 79947568623307192767295)
                  ·
                    rfl

theorem cell23_1401276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_1401276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401276 prefixEnd_1401276 := by exact prefixLift 1401276
  have htrace : WordTrace (prefixWord ++ tailWord_1401276) baseStart_1401276 baseEnd_1401276 := by
    simpa [prefixWord, tailWord_1401276, baseEnd_1401276] using wordTrace_append hprefix tailTrace_1401276
  have hstable : (prefixWord ++ tailWord_1401276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401276).length < 2 ^ (prefixWord ++ tailWord_1401276).sum := by decide
  have hdescent : baseEnd_1401276 < baseStart_1401276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401319 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 3, 6]
def baseStart_1401319 : Nat := 118140960795 + 1401319 * 2 ^ 59
def prefixEnd_1401319 : Nat := 4983230072969 + 3 ^ 40 * 1401319 * 2
def baseEnd_1401319 : Nat := 239850065759302688889319

theorem tailTrace_1401319 : CollatzResearch.WordTrace tailWord_1401319 prefixEnd_1401319 239850065759302688889319 := by
  unfold tailWord_1401319
  simp only [CollatzResearch.WordTrace]
  refine ⟨51110302810268064076575011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34073535206845376051050007 51110302810268064076575011)
  ·
    refine ⟨76665454215402096114862517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51110302810268064076575011 76665454215402096114862517)
    ·
      refine ⟨7187386332693946510768361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76665454215402096114862517 7187386332693946510768361)
      ·
        refine ⟨5390539749520459883076271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7187386332693946510768361 5390539749520459883076271)
        ·
          refine ⟨8085809624280689824614407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390539749520459883076271 8085809624280689824614407)
          ·
            refine ⟨12128714436421034736921611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085809624280689824614407 12128714436421034736921611)
            ·
              refine ⟨18193071654631552105382417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12128714436421034736921611 18193071654631552105382417)
              ·
                refine ⟨13644803740973664079036813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18193071654631552105382417 13644803740973664079036813)
                ·
                  refine ⟨5116801402865124029638805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13644803740973664079036813 5116801402865124029638805)
                  ·
                    refine ⟨239850065759302688889319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5116801402865124029638805 239850065759302688889319)
                    ·
                      rfl

theorem cell23_1401319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_1401319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401319 prefixEnd_1401319 := by exact prefixLift 1401319
  have htrace : WordTrace (prefixWord ++ tailWord_1401319) baseStart_1401319 baseEnd_1401319 := by
    simpa [prefixWord, tailWord_1401319, baseEnd_1401319] using wordTrace_append hprefix tailTrace_1401319
  have hstable : (prefixWord ++ tailWord_1401319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401319).length < 2 ^ (prefixWord ++ tailWord_1401319).sum := by decide
  have hdescent : baseEnd_1401319 < baseStart_1401319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401320 : List Nat := [2, 1, 4, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_1401320 : Nat := 118140960795 + 1401320 * 2 ^ 59
def prefixEnd_1401320 : Nat := 4983230072969 + 3 ^ 40 * 1401320 * 2
def baseEnd_1401320 : Nat := 719550710758562562755453

theorem tailTrace_1401320 : CollatzResearch.WordTrace tailWord_1401320 prefixEnd_1401320 719550710758562562755453 := by
  unfold tailWord_1401320
  simp only [CollatzResearch.WordTrace]
  refine ⟨25555169641632220623680707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34073559522176294164907609 25555169641632220623680707)
  ·
    refine ⟨38332754462448330935521061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25555169641632220623680707 38332754462448330935521061)
    ·
      refine ⟨7187391461709062050410199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38332754462448330935521061 7187391461709062050410199)
      ·
        refine ⟨10781087192563593075615299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7187391461709062050410199 10781087192563593075615299)
        ·
          refine ⟨16171630788845389613422949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781087192563593075615299 16171630788845389613422949)
          ·
            refine ⟨3032180772908510552516803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16171630788845389613422949 3032180772908510552516803)
            ·
              refine ⟨4548271159362765828775205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032180772908510552516803 4548271159362765828775205)
              ·
                refine ⟨852800842380518592895351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4548271159362765828775205 852800842380518592895351)
                ·
                  refine ⟨1279201263570777889343027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852800842380518592895351 1279201263570777889343027)
                  ·
                    refine ⟨1918801895356166834014541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1279201263570777889343027 1918801895356166834014541)
                    ·
                      refine ⟨719550710758562562755453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918801895356166834014541 719550710758562562755453)
                      ·
                        rfl

theorem cell23_1401320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_1401320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401320 prefixEnd_1401320 := by exact prefixLift 1401320
  have htrace : WordTrace (prefixWord ++ tailWord_1401320) baseStart_1401320 baseEnd_1401320 := by
    simpa [prefixWord, tailWord_1401320, baseEnd_1401320] using wordTrace_append hprefix tailTrace_1401320
  have hstable : (prefixWord ++ tailWord_1401320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401320).length < 2 ^ (prefixWord ++ tailWord_1401320).sum := by decide
  have hdescent : baseEnd_1401320 < baseStart_1401320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401326 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1401326 : Nat := 118140960795 + 1401326 * 2 ^ 59
def prefixEnd_1401326 : Nat := 4983230072969 + 3 ^ 40 * 1401326 * 2
def baseEnd_1401326 : Nat := 719553791642489539280425

theorem tailTrace_1401326 : CollatzResearch.WordTrace tailWord_1401326 prefixEnd_1401326 719553791642489539280425 := by
  unfold tailWord_1401326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388819765155338034009979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34073705414161802848053221 6388819765155338034009979)
  ·
    refine ⟨9583229647733007051014969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6388819765155338034009979 9583229647733007051014969)
    ·
      refine ⟨7187422235799755288261227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9583229647733007051014969 7187422235799755288261227)
      ·
        refine ⟨10781133353699632932391841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7187422235799755288261227 10781133353699632932391841)
        ·
          refine ⟨8085850015274724699293881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10781133353699632932391841 8085850015274724699293881)
          ·
            refine ⟨6064387511456043524470411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8085850015274724699293881 6064387511456043524470411)
            ·
              refine ⟨9096581267184065286705617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6064387511456043524470411 9096581267184065286705617)
              ·
                refine ⟨6822435950388048965029213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9096581267184065286705617 6822435950388048965029213)
                ·
                  refine ⟨2558413481395518361885955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6822435950388048965029213 2558413481395518361885955)
                  ·
                    refine ⟨3837620222093277542828933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558413481395518361885955 3837620222093277542828933)
                    ·
                      refine ⟨719553791642489539280425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3837620222093277542828933 719553791642489539280425)
                      ·
                        rfl

theorem cell23_1401326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1401326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401326 prefixEnd_1401326 := by exact prefixLift 1401326
  have htrace : WordTrace (prefixWord ++ tailWord_1401326) baseStart_1401326 baseEnd_1401326 := by
    simpa [prefixWord, tailWord_1401326, baseEnd_1401326] using wordTrace_append hprefix tailTrace_1401326
  have hstable : (prefixWord ++ tailWord_1401326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401326).length < 2 ^ (prefixWord ++ tailWord_1401326).sum := by decide
  have hdescent : baseEnd_1401326 < baseStart_1401326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401329 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_1401329 : Nat := 118140960795 + 1401329 * 2 ^ 59
def prefixEnd_1401329 : Nat := 4983230072969 + 3 ^ 40 * 1401329 * 2
def baseEnd_1401329 : Nat := 719555332084453027542911

theorem tailTrace_1401329 : CollatzResearch.WordTrace tailWord_1401329 prefixEnd_1401329 719555332084453027542911 := by
  unfold tailWord_1401329
  simp only [CollatzResearch.WordTrace]
  refine ⟨51110667540231835784439041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34073778360154557189626027 51110667540231835784439041)
  ·
    refine ⟨38333000655173876838329281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51110667540231835784439041 38333000655173876838329281)
    ·
      refine ⟨28749750491380407628746961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38333000655173876838329281 28749750491380407628746961)
      ·
        refine ⟨21562312868535305721560221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28749750491380407628746961 21562312868535305721560221)
        ·
          refine ⟨8085867325700739645585083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21562312868535305721560221 8085867325700739645585083)
          ·
            refine ⟨12128800988551109468377625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085867325700739645585083 12128800988551109468377625)
            ·
              refine ⟨9096600741413332101283219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12128800988551109468377625 9096600741413332101283219)
              ·
                refine ⟨13644901112119998151924829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9096600741413332101283219 13644901112119998151924829)
                ·
                  refine ⟨5116837917044999306971811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13644901112119998151924829 5116837917044999306971811)
                  ·
                    refine ⟨7675256875567498960457717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5116837917044999306971811 7675256875567498960457717)
                    ·
                      refine ⟨719555332084453027542911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7675256875567498960457717 719555332084453027542911)
                      ·
                        rfl

theorem cell23_1401329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_1401329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401329 prefixEnd_1401329 := by exact prefixLift 1401329
  have htrace : WordTrace (prefixWord ++ tailWord_1401329) baseStart_1401329 baseEnd_1401329 := by
    simpa [prefixWord, tailWord_1401329, baseEnd_1401329] using wordTrace_append hprefix tailTrace_1401329
  have hstable : (prefixWord ++ tailWord_1401329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401329).length < 2 ^ (prefixWord ++ tailWord_1401329).sum := by decide
  have hdescent : baseEnd_1401329 < baseStart_1401329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401336 : List Nat := [2, 1, 2, 1, 1, 4, 1, 5, 2, 4]
def baseStart_1401336 : Nat := 118140960795 + 1401336 * 2 ^ 59
def prefixEnd_1401336 : Nat := 4983230072969 + 3 ^ 40 * 1401336 * 2
def baseEnd_1401336 : Nat := 239852975483011500051793

theorem tailTrace_1401336 : CollatzResearch.WordTrace tailWord_1401336 prefixEnd_1401336 239852975483011500051793 := by
  unfold tailWord_1401336
  simp only [CollatzResearch.WordTrace]
  refine ⟨25555461425603237989971931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34073948567470983986629241 25555461425603237989971931)
  ·
    refine ⟨38333192138404856984957897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25555461425603237989971931 38333192138404856984957897)
    ·
      refine ⟨28749894103803642738718423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38333192138404856984957897 28749894103803642738718423)
      ·
        refine ⟨43124841155705464108077635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28749894103803642738718423 43124841155705464108077635)
        ·
          refine ⟨64687261733558196162116453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43124841155705464108077635 64687261733558196162116453)
          ·
            refine ⟨12128861575042161780396835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64687261733558196162116453 12128861575042161780396835)
            ·
              refine ⟨18193292362563242670595253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12128861575042161780396835 18193292362563242670595253)
              ·
                refine ⟨1705621158990304000368305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18193292362563242670595253 1705621158990304000368305)
                ·
                  refine ⟨1279215869242728000276229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1705621158990304000368305 1279215869242728000276229)
                  ·
                    refine ⟨239852975483011500051793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1279215869242728000276229 239852975483011500051793)
                    ·
                      rfl

theorem cell23_1401336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_1401336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401336 prefixEnd_1401336 := by exact prefixLift 1401336
  have htrace : WordTrace (prefixWord ++ tailWord_1401336) baseStart_1401336 baseEnd_1401336 := by
    simpa [prefixWord, tailWord_1401336, baseEnd_1401336] using wordTrace_append hprefix tailTrace_1401336
  have hstable : (prefixWord ++ tailWord_1401336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401336).length < 2 ^ (prefixWord ++ tailWord_1401336).sum := by decide
  have hdescent : baseEnd_1401336 < baseStart_1401336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401343 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 3, 2, 2]
def baseStart_1401343 : Nat := 118140960795 + 1401343 * 2 ^ 59
def prefixEnd_1401343 : Nat := 4983230072969 + 3 ^ 40 * 1401343 * 2
def baseEnd_1401343 : Nat := 719562520813615972767847

theorem tailTrace_1401343 : CollatzResearch.WordTrace tailWord_1401343 prefixEnd_1401343 719562520813615972767847 := by
  unfold tailWord_1401343
  simp only [CollatzResearch.WordTrace]
  refine ⟨51111178162181116175448683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34074118774787410783632455 51111178162181116175448683)
  ·
    refine ⟨76666767243271674263173025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51111178162181116175448683 76666767243271674263173025)
    ·
      refine ⟨57500075432453755697379769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76666767243271674263173025 57500075432453755697379769)
      ·
        refine ⟨43125056574340316773034827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57500075432453755697379769 43125056574340316773034827)
        ·
          refine ⟨64687584861510475159552241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43125056574340316773034827 64687584861510475159552241)
          ·
            refine ⟨48515688646132856369664181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64687584861510475159552241 48515688646132856369664181)
            ·
              refine ⟨4548345810574955284656017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48515688646132856369664181 4548345810574955284656017)
              ·
                refine ⟨3411259357931216463492013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4548345810574955284656017 3411259357931216463492013)
                ·
                  refine ⟨1279222259224206173809505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3411259357931216463492013 1279222259224206173809505)
                  ·
                    refine ⟨959416694418154630357129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1279222259224206173809505 959416694418154630357129)
                    ·
                      refine ⟨719562520813615972767847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959416694418154630357129 719562520813615972767847)
                      ·
                        rfl

theorem cell23_1401343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_1401343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401343 prefixEnd_1401343 := by exact prefixLift 1401343
  have htrace : WordTrace (prefixWord ++ tailWord_1401343) baseStart_1401343 baseEnd_1401343 := by
    simpa [prefixWord, tailWord_1401343, baseEnd_1401343] using wordTrace_append hprefix tailTrace_1401343
  have hstable : (prefixWord ++ tailWord_1401343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401343).length < 2 ^ (prefixWord ++ tailWord_1401343).sum := by decide
  have hdescent : baseEnd_1401343 < baseStart_1401343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401356 : List Nat := [2, 2, 1, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1401356 : Nat := 118140960795 + 1401356 * 2 ^ 59
def prefixEnd_1401356 : Nat := 4983230072969 + 3 ^ 40 * 1401356 * 2
def baseEnd_1401356 : Nat := 719569196062124421905287

theorem tailTrace_1401356 : CollatzResearch.WordTrace tailWord_1401356 prefixEnd_1401356 719569196062124421905287 := by
  unfold tailWord_1401356
  simp only [CollatzResearch.WordTrace]
  refine ⟨25555826155567009697835961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34074434874089346263781281 25555826155567009697835961)
  ·
    refine ⟨19166869616675257273376971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25555826155567009697835961 19166869616675257273376971)
    ·
      refine ⟨28750304425012885910065457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19166869616675257273376971 28750304425012885910065457)
      ·
        refine ⟨21562728318759664432549093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28750304425012885910065457 21562728318759664432549093)
        ·
          refine ⟨4043011559767437081102955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21562728318759664432549093 4043011559767437081102955)
          ·
            refine ⟨6064517339651155621654433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043011559767437081102955 6064517339651155621654433)
            ·
              refine ⟨4548388004738366716240825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6064517339651155621654433 4548388004738366716240825)
              ·
                refine ⟨3411291003553775037180619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4548388004738366716240825 3411291003553775037180619)
                ·
                  refine ⟨5116936505330662555770929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411291003553775037180619 5116936505330662555770929)
                  ·
                    refine ⟨3837702378997996916828197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5116936505330662555770929 3837702378997996916828197)
                    ·
                      refine ⟨719569196062124421905287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3837702378997996916828197 719569196062124421905287)
                      ·
                        rfl

theorem cell23_1401356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1401356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401356 prefixEnd_1401356 := by exact prefixLift 1401356
  have htrace : WordTrace (prefixWord ++ tailWord_1401356) baseStart_1401356 baseEnd_1401356 := by
    simpa [prefixWord, tailWord_1401356, baseEnd_1401356] using wordTrace_append hprefix tailTrace_1401356
  have hstable : (prefixWord ++ tailWord_1401356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401356).length < 2 ^ (prefixWord ++ tailWord_1401356).sum := by decide
  have hdescent : baseEnd_1401356 < baseStart_1401356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401357 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1401357 : Nat := 118140960795 + 1401357 * 2 ^ 59
def prefixEnd_1401357 : Nat := 4983230072969 + 3 ^ 40 * 1401357 * 2
def baseEnd_1401357 : Nat := 239856569847592972664261

theorem tailTrace_1401357 : CollatzResearch.WordTrace tailWord_1401357 prefixEnd_1401357 239856569847592972664261 := by
  unfold tailWord_1401357
  simp only [CollatzResearch.WordTrace]
  refine ⟨51111688784130396566458325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34074459189420264377638883 51111688784130396566458325)
  ·
    refine ⟨1197930205878056169526367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 51111688784130396566458325 1197930205878056169526367)
    ·
      refine ⟨1796895308817084254289551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197930205878056169526367 1796895308817084254289551)
      ·
        refine ⟨2695342963225626381434327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796895308817084254289551 2695342963225626381434327)
        ·
          refine ⟨4043014444838439572151491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695342963225626381434327 4043014444838439572151491)
          ·
            refine ⟨6064521667257659358227237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043014444838439572151491 6064521667257659358227237)
            ·
              refine ⟨1137097812610811129667607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6064521667257659358227237 1137097812610811129667607)
              ·
                refine ⟨1705646718916216694501411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137097812610811129667607 1705646718916216694501411)
                ·
                  refine ⟨2558470078374325041752117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705646718916216694501411 2558470078374325041752117)
                  ·
                    refine ⟨239856569847592972664261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2558470078374325041752117 239856569847592972664261)
                    ·
                      rfl

theorem cell23_1401357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1401357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401357 prefixEnd_1401357 := by exact prefixLift 1401357
  have htrace : WordTrace (prefixWord ++ tailWord_1401357) baseStart_1401357 baseEnd_1401357 := by
    simpa [prefixWord, tailWord_1401357, baseEnd_1401357] using wordTrace_append hprefix tailTrace_1401357
  have hstable : (prefixWord ++ tailWord_1401357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401357).length < 2 ^ (prefixWord ++ tailWord_1401357).sum := by decide
  have hdescent : baseEnd_1401357 < baseStart_1401357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401390 : List Nat := [4, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1401390 : Nat := 118140960795 + 1401390 * 2 ^ 59
def prefixEnd_1401390 : Nat := 4983230072969 + 3 ^ 40 * 1401390 * 2
def baseEnd_1401390 : Nat := 719586654404377288880131

theorem tailTrace_1401390 : CollatzResearch.WordTrace tailWord_1401390 prefixEnd_1401390 719586654404377288880131 := by
  unfold tailWord_1401390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389111549126355400301203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34075261595340562134939749 6389111549126355400301203)
  ·
    refine ⟨9583667323689533100451805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6389111549126355400301203 9583667323689533100451805)
    ·
      refine ⟨3593875246383574912669427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9583667323689533100451805 3593875246383574912669427)
      ·
        refine ⟨5390812869575362369004141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3593875246383574912669427 5390812869575362369004141)
        ·
          refine ⟨2021554826090760888376553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5390812869575362369004141 2021554826090760888376553)
          ·
            refine ⟨1516166119568070666282415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2021554826090760888376553 1516166119568070666282415)
            ·
              refine ⟨2274249179352105999423623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516166119568070666282415 2274249179352105999423623)
              ·
                refine ⟨3411373769028158999135435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274249179352105999423623 3411373769028158999135435)
                ·
                  refine ⟨5117060653542238498703153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3411373769028158999135435 5117060653542238498703153)
                  ·
                    refine ⟨3837795490156678874027365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5117060653542238498703153 3837795490156678874027365)
                    ·
                      refine ⟨719586654404377288880131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3837795490156678874027365 719586654404377288880131)
                      ·
                        rfl

theorem cell23_1401390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1401390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401390 prefixEnd_1401390 := by exact prefixLift 1401390
  have htrace : WordTrace (prefixWord ++ tailWord_1401390) baseStart_1401390 baseEnd_1401390 := by
    simpa [prefixWord, tailWord_1401390, baseEnd_1401390] using wordTrace_append hprefix tailTrace_1401390
  have hstable : (prefixWord ++ tailWord_1401390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401390).length < 2 ^ (prefixWord ++ tailWord_1401390).sum := by decide
  have hdescent : baseEnd_1401390 < baseStart_1401390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401393 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_1401393 : Nat := 118140960795 + 1401393 * 2 ^ 59
def prefixEnd_1401393 : Nat := 4983230072969 + 3 ^ 40 * 1401393 * 2
def baseEnd_1401393 : Nat := 719588194846340777142617

theorem tailTrace_1401393 : CollatzResearch.WordTrace tailWord_1401393 prefixEnd_1401393 719588194846340777142617 := by
  unfold tailWord_1401393
  simp only [CollatzResearch.WordTrace]
  refine ⟨51113001811999974714768833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34075334541333316476512555 51113001811999974714768833)
  ·
    refine ⟨38334751358999981036076625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51113001811999974714768833 38334751358999981036076625)
    ·
      refine ⟨28751063519249985777057469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38334751358999981036076625 28751063519249985777057469)
      ·
        refine ⟨10781648819718744666396551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28751063519249985777057469 10781648819718744666396551)
        ·
          refine ⟨16172473229578116999594827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10781648819718744666396551 16172473229578116999594827)
          ·
            refine ⟨24258709844367175499392241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16172473229578116999594827 24258709844367175499392241)
            ·
              refine ⟨18194032383275381624544181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24258709844367175499392241 18194032383275381624544181)
              ·
                refine ⟨1705690535932067027301017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18194032383275381624544181 1705690535932067027301017)
                ·
                  refine ⟨1279267901949050270475763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1705690535932067027301017 1279267901949050270475763)
                  ·
                    refine ⟨1918901852923575405713645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1279267901949050270475763 1918901852923575405713645)
                    ·
                      refine ⟨719588194846340777142617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1918901852923575405713645 719588194846340777142617)
                      ·
                        rfl

theorem cell23_1401393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_1401393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401393 prefixEnd_1401393 := by exact prefixLift 1401393
  have htrace : WordTrace (prefixWord ++ tailWord_1401393) baseStart_1401393 baseEnd_1401393 := by
    simpa [prefixWord, tailWord_1401393, baseEnd_1401393] using wordTrace_append hprefix tailTrace_1401393
  have hstable : (prefixWord ++ tailWord_1401393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401393).length < 2 ^ (prefixWord ++ tailWord_1401393).sum := by decide
  have hdescent : baseEnd_1401393 < baseStart_1401393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401419 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5]
def baseStart_1401419 : Nat := 118140960795 + 1401419 * 2 ^ 59
def prefixEnd_1401419 : Nat := 4983230072969 + 3 ^ 40 * 1401419 * 2
def baseEnd_1401419 : Nat := 719601545343357675417497

theorem tailTrace_1401419 : CollatzResearch.WordTrace tailWord_1401419 prefixEnd_1401419 719601545343357675417497 := by
  unfold tailWord_1401419
  simp only [CollatzResearch.WordTrace]
  refine ⟨51113950109905781155215311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34075966739937187436810207 51113950109905781155215311)
  ·
    refine ⟨76670925164858671732822967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51113950109905781155215311 76670925164858671732822967)
    ·
      refine ⟨115006387747288007599234451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76670925164858671732822967 115006387747288007599234451)
      ·
        refine ⟨172509581620932011398851677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115006387747288007599234451 172509581620932011398851677)
        ·
          refine ⟨64691093107849504274569379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172509581620932011398851677 64691093107849504274569379)
          ·
            refine ⟨97036639661774256411854069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64691093107849504274569379 97036639661774256411854069)
            ·
              refine ⟨9097184968291336538611319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97036639661774256411854069 9097184968291336538611319)
              ·
                refine ⟨13645777452437004807916979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9097184968291336538611319 13645777452437004807916979)
                ·
                  refine ⟨20468666178655507211875469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13645777452437004807916979 20468666178655507211875469)
                  ·
                    refine ⟨7675749816995815204453301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20468666178655507211875469 7675749816995815204453301)
                    ·
                      refine ⟨719601545343357675417497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7675749816995815204453301 719601545343357675417497)
                      ·
                        rfl

theorem cell23_1401419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_1401419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401419 prefixEnd_1401419 := by exact prefixLift 1401419
  have htrace : WordTrace (prefixWord ++ tailWord_1401419) baseStart_1401419 baseEnd_1401419 := by
    simpa [prefixWord, tailWord_1401419, baseEnd_1401419] using wordTrace_append hprefix tailTrace_1401419
  have hstable : (prefixWord ++ tailWord_1401419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401419).length < 2 ^ (prefixWord ++ tailWord_1401419).sum := by decide
  have hdescent : baseEnd_1401419 < baseStart_1401419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401438 : List Nat := [4, 4, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1401438 : Nat := 118140960795 + 1401438 * 2 ^ 59
def prefixEnd_1401438 : Nat := 4983230072969 + 3 ^ 40 * 1401438 * 2
def baseEnd_1401438 : Nat := 239870433825264367026637

theorem tailTrace_1401438 : CollatzResearch.WordTrace tailWord_1401438 prefixEnd_1401438 239870433825264367026637 := by
  unfold tailWord_1401438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389330387104618425019621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34076428731224631600104645 6389330387104618425019621)
  ·
    refine ⟨1197999447582115954691179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6389330387104618425019621 1197999447582115954691179)
    ·
      refine ⟨1796999171373173932036769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197999447582115954691179 1796999171373173932036769)
      ·
        refine ⟨1347749378529880449027577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1796999171373173932036769 1347749378529880449027577)
        ·
          refine ⟨1010812033897410336770683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1347749378529880449027577 1010812033897410336770683)
          ·
            refine ⟨1516218050846115505156025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010812033897410336770683 1516218050846115505156025)
            ·
              refine ⟨1137163538134586628867019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516218050846115505156025 1137163538134586628867019)
              ·
                refine ⟨1705745307201879943300529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137163538134586628867019 1705745307201879943300529)
                ·
                  refine ⟨1279308980401409957475397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1705745307201879943300529 1279308980401409957475397)
                  ·
                    refine ⟨239870433825264367026637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1279308980401409957475397 239870433825264367026637)
                    ·
                      rfl

theorem cell23_1401438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1401438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401438 prefixEnd_1401438 := by exact prefixLift 1401438
  have htrace : WordTrace (prefixWord ++ tailWord_1401438) baseStart_1401438 baseEnd_1401438 := by
    simpa [prefixWord, tailWord_1401438, baseEnd_1401438] using wordTrace_append hprefix tailTrace_1401438
  have hstable : (prefixWord ++ tailWord_1401438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401438).length < 2 ^ (prefixWord ++ tailWord_1401438).sum := by decide
  have hdescent : baseEnd_1401438 < baseStart_1401438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401473 : List Nat := [1, 2, 4, 2, 1, 1, 2, 5, 5]
def baseStart_1401473 : Nat := 118140960795 + 1401473 * 2 ^ 59
def prefixEnd_1401473 : Nat := 4983230072969 + 3 ^ 40 * 1401473 * 2
def baseEnd_1401473 : Nat := 79958808144300051571361

theorem tailTrace_1401473 : CollatzResearch.WordTrace tailWord_1401473 prefixEnd_1401473 79958808144300051571361 := by
  unfold tailWord_1401473
  simp only [CollatzResearch.WordTrace]
  refine ⟨51115919651710148377681073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34077279767806765585120715 51115919651710148377681073)
  ·
    refine ⟨38336939738782611283260805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51115919651710148377681073 38336939738782611283260805)
    ·
      refine ⟨7188176201021739615611401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38336939738782611283260805 7188176201021739615611401)
      ·
        refine ⟨5391132150766304711708551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7188176201021739615611401 5391132150766304711708551)
        ·
          refine ⟨8086698226149457067562827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391132150766304711708551 8086698226149457067562827)
          ·
            refine ⟨12130047339224185601344241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8086698226149457067562827 12130047339224185601344241)
            ·
              refine ⟨9097535504418139201008181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12130047339224185601344241 9097535504418139201008181)
              ·
                refine ⟨852893953539200550094517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9097535504418139201008181 852893953539200550094517)
                ·
                  refine ⟨79958808144300051571361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852893953539200550094517 79958808144300051571361)
                  ·
                    rfl

theorem cell23_1401473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 5].length) (baseStart_1401473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401473 prefixEnd_1401473 := by exact prefixLift 1401473
  have htrace : WordTrace (prefixWord ++ tailWord_1401473) baseStart_1401473 baseEnd_1401473 := by
    simpa [prefixWord, tailWord_1401473, baseEnd_1401473] using wordTrace_append hprefix tailTrace_1401473
  have hstable : (prefixWord ++ tailWord_1401473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401473).length < 2 ^ (prefixWord ++ tailWord_1401473).sum := by decide
  have hdescent : baseEnd_1401473 < baseStart_1401473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401490 : List Nat := [3, 2, 3, 1, 2, 2, 1, 4, 5]
def baseStart_1401490 : Nat := 118140960795 + 1401490 * 2 ^ 59
def prefixEnd_1401490 : Nat := 4983230072969 + 3 ^ 40 * 1401490 * 2
def baseEnd_1401490 : Nat := 79959778052202988625519

theorem tailTrace_1401490 : CollatzResearch.WordTrace tailWord_1401490 prefixEnd_1401490 79959778052202988625519 := by
  unfold tailWord_1401490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779134923162140070262481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34077693128432373520699949 12779134923162140070262481)
  ·
    refine ⟨9584351192371605052696861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12779134923162140070262481 9584351192371605052696861)
    ·
      refine ⟨3594131697139351894761323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9584351192371605052696861 3594131697139351894761323)
      ·
        refine ⟨5391197545709027842141985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594131697139351894761323 5391197545709027842141985)
        ·
          refine ⟨4043398159281770881606489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5391197545709027842141985 4043398159281770881606489)
          ·
            refine ⟨3032548619461328161204867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043398159281770881606489 3032548619461328161204867)
            ·
              refine ⟨4548822929191992241807301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032548619461328161204867 4548822929191992241807301)
              ·
                refine ⟨852904299223498545338869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4548822929191992241807301 852904299223498545338869)
                ·
                  refine ⟨79959778052202988625519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852904299223498545338869 79959778052202988625519)
                  ·
                    rfl

theorem cell23_1401490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_1401490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401490 prefixEnd_1401490 := by exact prefixLift 1401490
  have htrace : WordTrace (prefixWord ++ tailWord_1401490) baseStart_1401490 baseEnd_1401490 := by
    simpa [prefixWord, tailWord_1401490, baseEnd_1401490] using wordTrace_append hprefix tailTrace_1401490
  have hstable : (prefixWord ++ tailWord_1401490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401490).length < 2 ^ (prefixWord ++ tailWord_1401490).sum := by decide
  have hdescent : baseEnd_1401490 < baseStart_1401490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401496 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1401496 : Nat := 118140960795 + 1401496 * 2 ^ 59
def prefixEnd_1401496 : Nat := 4983230072969 + 3 ^ 40 * 1401496 * 2
def baseEnd_1401496 : Nat := 719641083353753874154643

theorem tailTrace_1401496 : CollatzResearch.WordTrace tailWord_1401496 prefixEnd_1401496 719641083353753874154643 := by
  unfold tailWord_1401496
  simp only [CollatzResearch.WordTrace]
  refine ⟨25558379265313411652884171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34077839020417882203845561 25558379265313411652884171)
  ·
    refine ⟨38337568897970117479326257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25558379265313411652884171 38337568897970117479326257)
    ·
      refine ⟨28753176673477588109494693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38337568897970117479326257 28753176673477588109494693)
      ·
        refine ⟨5391220626277047770530255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28753176673477588109494693 5391220626277047770530255)
        ·
          refine ⟨8086830939415571655795383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391220626277047770530255 8086830939415571655795383)
          ·
            refine ⟨12130246409123357483693075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8086830939415571655795383 12130246409123357483693075)
            ·
              refine ⟨18195369613685036225539613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12130246409123357483693075 18195369613685036225539613)
              ·
                refine ⟨6823263605131888584577355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18195369613685036225539613 6823263605131888584577355)
                ·
                  refine ⟨10234895407697832876866033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6823263605131888584577355 10234895407697832876866033)
                  ·
                    refine ⟨7676171555773374657649525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10234895407697832876866033 7676171555773374657649525)
                    ·
                      refine ⟨719641083353753874154643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7676171555773374657649525 719641083353753874154643)
                      ·
                        rfl

theorem cell23_1401496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1401496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401496 prefixEnd_1401496 := by exact prefixLift 1401496
  have htrace : WordTrace (prefixWord ++ tailWord_1401496) baseStart_1401496 baseEnd_1401496 := by
    simpa [prefixWord, tailWord_1401496, baseEnd_1401496] using wordTrace_append hprefix tailTrace_1401496
  have hstable : (prefixWord ++ tailWord_1401496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401496).length < 2 ^ (prefixWord ++ tailWord_1401496).sum := by decide
  have hdescent : baseEnd_1401496 < baseStart_1401496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401499 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 10]
def baseStart_1401499 : Nat := 118140960795 + 1401499 * 2 ^ 59
def prefixEnd_1401499 : Nat := 4983230072969 + 3 ^ 40 * 1401499 * 2
def baseEnd_1401499 : Nat := 239880874598572454139043

theorem tailTrace_1401499 : CollatzResearch.WordTrace tailWord_1401499 prefixEnd_1401499 239880874598572454139043 := by
  unfold tailWord_1401499
  simp only [CollatzResearch.WordTrace]
  refine ⟨51116867949615954818127551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34077911966410636545418367 51116867949615954818127551)
  ·
    refine ⟨76675301924423932227191327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51116867949615954818127551 76675301924423932227191327)
    ·
      refine ⟨115012952886635898340786991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76675301924423932227191327 115012952886635898340786991)
      ·
        refine ⟨172519429329953847511180487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115012952886635898340786991 172519429329953847511180487)
        ·
          refine ⟨258779143994930771266770731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172519429329953847511180487 258779143994930771266770731)
          ·
            refine ⟨388168715992396156900156097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258779143994930771266770731 388168715992396156900156097)
            ·
              refine ⟨291126536994297117675117073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388168715992396156900156097 291126536994297117675117073)
              ·
                refine ⟨218344902745722838256337805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291126536994297117675117073 218344902745722838256337805)
                ·
                  refine ⟨81879338529646064346126677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 218344902745722838256337805 81879338529646064346126677)
                  ·
                    refine ⟨239880874598572454139043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 81879338529646064346126677 239880874598572454139043)
                    ·
                      rfl

theorem cell23_1401499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_1401499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401499 prefixEnd_1401499 := by exact prefixLift 1401499
  have htrace : WordTrace (prefixWord ++ tailWord_1401499) baseStart_1401499 baseEnd_1401499 := by
    simpa [prefixWord, tailWord_1401499, baseEnd_1401499] using wordTrace_append hprefix tailTrace_1401499
  have hstable : (prefixWord ++ tailWord_1401499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401499).length < 2 ^ (prefixWord ++ tailWord_1401499).sum := by decide
  have hdescent : baseEnd_1401499 < baseStart_1401499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401523 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 4]
def baseStart_1401523 : Nat := 118140960795 + 1401523 * 2 ^ 59
def prefixEnd_1401523 : Nat := 4983230072969 + 3 ^ 40 * 1401523 * 2
def baseEnd_1401523 : Nat := 719654947331425268517019

theorem tailTrace_1401523 : CollatzResearch.WordTrace tailWord_1401523 prefixEnd_1401523 719654947331425268517019 := by
  unfold tailWord_1401523
  simp only [CollatzResearch.WordTrace]
  refine ⟨51117743301529006917001223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34078495534352671278000815 51117743301529006917001223)
  ·
    refine ⟨76676614952293510375501835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51117743301529006917001223 76676614952293510375501835)
    ·
      refine ⟨115014922428440265563252753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76676614952293510375501835 115014922428440265563252753)
      ·
        refine ⟨86261191821330199172439565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115014922428440265563252753 86261191821330199172439565)
        ·
          refine ⟨32347946932998824689664837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86261191821330199172439565 32347946932998824689664837)
          ·
            refine ⟨6065240049937279629312157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32347946932998824689664837 6065240049937279629312157)
            ·
              refine ⟨2274465018726479860992059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6065240049937279629312157 2274465018726479860992059)
              ·
                refine ⟨3411697528089719791488089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274465018726479860992059 3411697528089719791488089)
                ·
                  refine ⟨2558773146067289843616067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3411697528089719791488089 2558773146067289843616067)
                  ·
                    refine ⟨3838159719100934765424101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2558773146067289843616067 3838159719100934765424101)
                    ·
                      refine ⟨719654947331425268517019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3838159719100934765424101 719654947331425268517019)
                      ·
                        rfl

theorem cell23_1401523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_1401523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401523 prefixEnd_1401523 := by exact prefixLift 1401523
  have htrace : WordTrace (prefixWord ++ tailWord_1401523) baseStart_1401523 baseEnd_1401523 := by
    simpa [prefixWord, tailWord_1401523, baseEnd_1401523] using wordTrace_append hprefix tailTrace_1401523
  have hstable : (prefixWord ++ tailWord_1401523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401523).length < 2 ^ (prefixWord ++ tailWord_1401523).sum := by decide
  have hdescent : baseEnd_1401523 < baseStart_1401523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401536 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_1401536 : Nat := 118140960795 + 1401536 * 2 ^ 59
def prefixEnd_1401536 : Nat := 4983230072969 + 3 ^ 40 * 1401536 * 2
def baseEnd_1401536 : Nat := 719661622579933717654459

theorem tailTrace_1401536 : CollatzResearch.WordTrace tailWord_1401536 prefixEnd_1401536 719661622579933717654459 := by
  unfold tailWord_1401536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25559108725240955068612231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34078811633654606758149641 25559108725240955068612231)
  ·
    refine ⟨38338663087861432602918347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25559108725240955068612231 38338663087861432602918347)
    ·
      refine ⟨57507994631792148904377521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38338663087861432602918347 57507994631792148904377521)
      ·
        refine ⟨43130995973844111678283141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57507994631792148904377521 43130995973844111678283141)
        ·
          refine ⟨8087061745095770939678089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43130995973844111678283141 8087061745095770939678089)
          ·
            refine ⟨6065296308821828204758567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8087061745095770939678089 6065296308821828204758567)
            ·
              refine ⟨9097944463232742307137851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065296308821828204758567 9097944463232742307137851)
              ·
                refine ⟨13646916694849113460706777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9097944463232742307137851 13646916694849113460706777)
                ·
                  refine ⟨10235187521136835095530083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13646916694849113460706777 10235187521136835095530083)
                  ·
                    refine ⟨15352781281705252643295125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10235187521136835095530083 15352781281705252643295125)
                    ·
                      refine ⟨719661622579933717654459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15352781281705252643295125 719661622579933717654459)
                      ·
                        rfl

theorem cell23_1401536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_1401536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401536 prefixEnd_1401536 := by exact prefixLift 1401536
  have htrace : WordTrace (prefixWord ++ tailWord_1401536) baseStart_1401536 baseEnd_1401536 := by
    simpa [prefixWord, tailWord_1401536, baseEnd_1401536] using wordTrace_append hprefix tailTrace_1401536
  have hstable : (prefixWord ++ tailWord_1401536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401536).length < 2 ^ (prefixWord ++ tailWord_1401536).sum := by decide
  have hdescent : baseEnd_1401536 < baseStart_1401536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401540 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_1401540 : Nat := 118140960795 + 1401540 * 2 ^ 59
def prefixEnd_1401540 : Nat := 4983230072969 + 3 ^ 40 * 1401540 * 2
def baseEnd_1401540 : Nat := 719663676502551702004441

theorem tailTrace_1401540 : CollatzResearch.WordTrace tailWord_1401540 prefixEnd_1401540 719663676502551702004441 := by
  unfold tailWord_1401540
  simp only [CollatzResearch.WordTrace]
  refine ⟨25559181671233709410185037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34078908894978279213580049 25559181671233709410185037)
  ·
    refine ⟨9584693126712641028819389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25559181671233709410185037 9584693126712641028819389)
    ·
      refine ⟨3594259922517240385807271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9584693126712641028819389 3594259922517240385807271)
      ·
        refine ⟨5391389883775860578710907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594259922517240385807271 5391389883775860578710907)
        ·
          refine ⟨8087084825663790868066361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5391389883775860578710907 8087084825663790868066361)
          ·
            refine ⟨6065313619247843151049771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8087084825663790868066361 6065313619247843151049771)
            ·
              refine ⟨9097970428871764726574657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065313619247843151049771 9097970428871764726574657)
              ·
                refine ⟨6823477821653823544930993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9097970428871764726574657 6823477821653823544930993)
                ·
                  refine ⟨5117608366240367658698245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6823477821653823544930993 5117608366240367658698245)
                  ·
                    refine ⟨959551568670068936005921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5117608366240367658698245 959551568670068936005921)
                    ·
                      refine ⟨719663676502551702004441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959551568670068936005921 719663676502551702004441)
                      ·
                        rfl

theorem cell23_1401540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_1401540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401540 prefixEnd_1401540 := by exact prefixLift 1401540
  have htrace : WordTrace (prefixWord ++ tailWord_1401540) baseStart_1401540 baseEnd_1401540 := by
    simpa [prefixWord, tailWord_1401540, baseEnd_1401540] using wordTrace_append hprefix tailTrace_1401540
  have hstable : (prefixWord ++ tailWord_1401540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401540).length < 2 ^ (prefixWord ++ tailWord_1401540).sum := by decide
  have hdescent : baseEnd_1401540 < baseStart_1401540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401550 : List Nat := [4, 1, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_1401550 : Nat := 118140960795 + 1401550 * 2 ^ 59
def prefixEnd_1401550 : Nat := 4983230072969 + 3 ^ 40 * 1401550 * 2
def baseEnd_1401550 : Nat := 239889603769698887626465

theorem tailTrace_1401550 : CollatzResearch.WordTrace tailWord_1401550 prefixEnd_1401550 239889603769698887626465 := by
  unfold tailWord_1401550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389841009053898816029263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34079152048287460352156069 6389841009053898816029263)
  ·
    refine ⟨9584761513580848224043895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6389841009053898816029263 9584761513580848224043895)
    ·
      refine ⟨14377142270371272336065843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9584761513580848224043895 14377142270371272336065843)
      ·
        refine ⟨21565713405556908504098765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14377142270371272336065843 21565713405556908504098765)
        ·
          refine ⟨8087142527083840689037037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21565713405556908504098765 8087142527083840689037037)
          ·
            refine ⟨3032678447656440258388889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8087142527083840689037037 3032678447656440258388889)
            ·
              refine ⟨2274508835742330193791667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032678447656440258388889 2274508835742330193791667)
              ·
                refine ⟨3411763253613495290687501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274508835742330193791667 3411763253613495290687501)
                ·
                  refine ⟨1279411220105060734007813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3411763253613495290687501 1279411220105060734007813)
                  ·
                    refine ⟨239889603769698887626465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1279411220105060734007813 239889603769698887626465)
                    ·
                      rfl

theorem cell23_1401550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_1401550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401550 prefixEnd_1401550 := by exact prefixLift 1401550
  have htrace : WordTrace (prefixWord ++ tailWord_1401550) baseStart_1401550 baseEnd_1401550 := by
    simpa [prefixWord, tailWord_1401550, baseEnd_1401550] using wordTrace_append hprefix tailTrace_1401550
  have hstable : (prefixWord ++ tailWord_1401550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401550).length < 2 ^ (prefixWord ++ tailWord_1401550).sum := by decide
  have hdescent : baseEnd_1401550 < baseStart_1401550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401607 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1401607 : Nat := 118140960795 + 1401607 * 2 ^ 59
def prefixEnd_1401607 : Nat := 4983230072969 + 3 ^ 40 * 1401607 * 2
def baseEnd_1401607 : Nat := 719698079706402939866633

theorem tailTrace_1401607 : CollatzResearch.WordTrace tailWord_1401607 prefixEnd_1401607 719698079706402939866633 := by
  unfold tailWord_1401607
  simp only [CollatzResearch.WordTrace]
  refine ⟨51120807033224689263059075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34080538022149792842039383 51120807033224689263059075)
  ·
    refine ⟨76681210549837033894588613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51120807033224689263059075 76681210549837033894588613)
    ·
      refine ⟨14377726978094443855235365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76681210549837033894588613 14377726978094443855235365)
      ·
        refine ⟨2695823808392708222856631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14377726978094443855235365 2695823808392708222856631)
        ·
          refine ⟨4043735712589062334284947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695823808392708222856631 4043735712589062334284947)
          ·
            refine ⟨6065603568883593501427421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4043735712589062334284947 6065603568883593501427421)
            ·
              refine ⟨2274601338331347563035283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6065603568883593501427421 2274601338331347563035283)
              ·
                refine ⟨3411902007497021344552925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274601338331347563035283 3411902007497021344552925)
                ·
                  refine ⟨1279463252811383004207347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3411902007497021344552925 1279463252811383004207347)
                  ·
                    refine ⟨1919194879217074506311021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1279463252811383004207347 1919194879217074506311021)
                    ·
                      refine ⟨719698079706402939866633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1919194879217074506311021 719698079706402939866633)
                      ·
                        rfl

theorem cell23_1401607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1401607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401607 prefixEnd_1401607 := by exact prefixLift 1401607
  have htrace : WordTrace (prefixWord ++ tailWord_1401607) baseStart_1401607 baseEnd_1401607 := by
    simpa [prefixWord, tailWord_1401607, baseEnd_1401607] using wordTrace_append hprefix tailTrace_1401607
  have hstable : (prefixWord ++ tailWord_1401607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401607).length < 2 ^ (prefixWord ++ tailWord_1401607).sum := by decide
  have hdescent : baseEnd_1401607 < baseStart_1401607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401658 : List Nat := [3, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3]
def baseStart_1401658 : Nat := 118140960795 + 1401658 * 2 ^ 59
def prefixEnd_1401658 : Nat := 4983230072969 + 3 ^ 40 * 1401658 * 2
def baseEnd_1401658 : Nat := 719724267219782240328899

theorem tailTrace_1401658 : CollatzResearch.WordTrace tailWord_1401658 prefixEnd_1401658 719724267219782240328899 := by
  unfold tailWord_1401658
  simp only [CollatzResearch.WordTrace]
  refine ⟨12780666789009981243291407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34081778104026616648777085 12780666789009981243291407)
  ·
    refine ⟨19171000183514971864937111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12780666789009981243291407 19171000183514971864937111)
    ·
      refine ⟨28756500275272457797405667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19171000183514971864937111 28756500275272457797405667)
      ·
        refine ⟨43134750412908686696108501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28756500275272457797405667 43134750412908686696108501)
        ·
          refine ⟨1010970712802547344440043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43134750412908686696108501 1010970712802547344440043)
          ·
            refine ⟨1516456069203821016660065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010970712802547344440043 1516456069203821016660065)
            ·
              refine ⟨1137342051902865762495049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516456069203821016660065 1137342051902865762495049)
              ·
                refine ⟨853006538927149321871287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137342051902865762495049 853006538927149321871287)
                ·
                  refine ⟨1279509808390723982806931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853006538927149321871287 1279509808390723982806931)
                  ·
                    refine ⟨1919264712586085974210397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1279509808390723982806931 1919264712586085974210397)
                    ·
                      refine ⟨719724267219782240328899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1919264712586085974210397 719724267219782240328899)
                      ·
                        rfl

theorem cell23_1401658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_1401658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401658 prefixEnd_1401658 := by exact prefixLift 1401658
  have htrace : WordTrace (prefixWord ++ tailWord_1401658) baseStart_1401658 baseEnd_1401658 := by
    simpa [prefixWord, tailWord_1401658, baseEnd_1401658] using wordTrace_append hprefix tailTrace_1401658
  have hstable : (prefixWord ++ tailWord_1401658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401658).length < 2 ^ (prefixWord ++ tailWord_1401658).sum := by decide
  have hdescent : baseEnd_1401658 < baseStart_1401658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401698 : List Nat := [3, 3, 2, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_1401698 : Nat := 118140960795 + 1401698 * 2 ^ 59
def prefixEnd_1401698 : Nat := 4983230072969 + 3 ^ 40 * 1401698 * 2
def baseEnd_1401698 : Nat := 719744806445962083828715

theorem tailTrace_1401698 : CollatzResearch.WordTrace tailWord_1401698 prefixEnd_1401698 719744806445962083828715 := by
  unfold tailWord_1401698
  simp only [CollatzResearch.WordTrace]
  refine ⟨12781031518973752951155437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34082750717263341203081165 12781031518973752951155437)
  ·
    refine ⟨4792886819615157356683289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12781031518973752951155437 4792886819615157356683289)
    ·
      refine ⟨3594665114711368017512467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4792886819615157356683289 3594665114711368017512467)
      ·
        refine ⟨5391997672067052026268701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594665114711368017512467 5391997672067052026268701)
        ·
          refine ⟨2021999127025144509850763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5391997672067052026268701 2021999127025144509850763)
          ·
            refine ⟨3032998690537716764776145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021999127025144509850763 3032998690537716764776145)
            ·
              refine ⟨2274749017903287573582109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032998690537716764776145 2274749017903287573582109)
              ·
                refine ⟨853030881713732840093291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2274749017903287573582109 853030881713732840093291)
                ·
                  refine ⟨1279546322570599260139937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853030881713732840093291 1279546322570599260139937)
                  ·
                    refine ⟨959659741927949445104953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1279546322570599260139937 959659741927949445104953)
                    ·
                      refine ⟨719744806445962083828715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959659741927949445104953 719744806445962083828715)
                      ·
                        rfl

theorem cell23_1401698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_1401698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401698 prefixEnd_1401698 := by exact prefixLift 1401698
  have htrace : WordTrace (prefixWord ++ tailWord_1401698) baseStart_1401698 baseEnd_1401698 := by
    simpa [prefixWord, tailWord_1401698, baseEnd_1401698] using wordTrace_append hprefix tailTrace_1401698
  have hstable : (prefixWord ++ tailWord_1401698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401698).length < 2 ^ (prefixWord ++ tailWord_1401698).sum := by decide
  have hdescent : baseEnd_1401698 < baseStart_1401698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401713 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 2, 6]
def baseStart_1401713 : Nat := 118140960795 + 1401713 * 2 ^ 59
def prefixEnd_1401713 : Nat := 4983230072969 + 3 ^ 40 * 1401713 * 2
def baseEnd_1401713 : Nat := 239917502885259841713715

theorem tailTrace_1401713 : CollatzResearch.WordTrace tailWord_1401713 prefixEnd_1401713 239917502885259841713715 := by
  unfold tailWord_1401713
  simp only [CollatzResearch.WordTrace]
  refine ⟨51124673170840669366417793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34083115447227112910945195 51124673170840669366417793)
  ·
    refine ⟨38343504878130502024813345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51124673170840669366417793 38343504878130502024813345)
    ·
      refine ⟨28757628658597876518610009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38343504878130502024813345 28757628658597876518610009)
      ·
        refine ⟨21568221493948407388957507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28757628658597876518610009 21568221493948407388957507)
        ·
          refine ⟨32352332240922611083436261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21568221493948407388957507 32352332240922611083436261)
          ·
            refine ⟨6066062295172989578144299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32352332240922611083436261 6066062295172989578144299)
            ·
              refine ⟨9099093442759484367216449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066062295172989578144299 9099093442759484367216449)
              ·
                refine ⟨6824320082069613275412337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9099093442759484367216449 6824320082069613275412337)
                ·
                  refine ⟨5118240061552209956559253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6824320082069613275412337 5118240061552209956559253)
                  ·
                    refine ⟨239917502885259841713715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5118240061552209956559253 239917502885259841713715)
                    ·
                      rfl

theorem cell23_1401713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_1401713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401713 prefixEnd_1401713 := by exact prefixLift 1401713
  have htrace : WordTrace (prefixWord ++ tailWord_1401713) baseStart_1401713 baseEnd_1401713 := by
    simpa [prefixWord, tailWord_1401713, baseEnd_1401713] using wordTrace_append hprefix tailTrace_1401713
  have hstable : (prefixWord ++ tailWord_1401713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401713).length < 2 ^ (prefixWord ++ tailWord_1401713).sum := by decide
  have hdescent : baseEnd_1401713 < baseStart_1401713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401723 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 3]
def baseStart_1401723 : Nat := 118140960795 + 1401723 * 2 ^ 59
def prefixEnd_1401723 : Nat := 4983230072969 + 3 ^ 40 * 1401723 * 2
def baseEnd_1401723 : Nat := 719757643462324486016099

theorem tailTrace_1401723 : CollatzResearch.WordTrace tailWord_1401723 prefixEnd_1401723 719757643462324486016099 := by
  unfold tailWord_1401723
  simp only [CollatzResearch.WordTrace]
  refine ⟨51125037900804441074281823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34083358600536294049521215 51125037900804441074281823)
  ·
    refine ⟨76687556851206661611422735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51125037900804441074281823 76687556851206661611422735)
    ·
      refine ⟨115031335276809992417134103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76687556851206661611422735 115031335276809992417134103)
      ·
        refine ⟨172547002915214988625701155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115031335276809992417134103 172547002915214988625701155)
        ·
          refine ⟨258820504372822482938551733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172547002915214988625701155 258820504372822482938551733)
          ·
            refine ⟨24264422284952107775489225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 258820504372822482938551733 24264422284952107775489225)
            ·
              refine ⟨18198316713714080831616919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24264422284952107775489225 18198316713714080831616919)
              ·
                refine ⟨27297475070571121247425379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18198316713714080831616919 27297475070571121247425379)
                ·
                  refine ⟨40946212605856681871138069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27297475070571121247425379 40946212605856681871138069)
                  ·
                    refine ⟨1919353715899531962709597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40946212605856681871138069 1919353715899531962709597)
                    ·
                      refine ⟨719757643462324486016099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1919353715899531962709597 719757643462324486016099)
                      ·
                        rfl

theorem cell23_1401723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 3].length) (baseStart_1401723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401723 prefixEnd_1401723 := by exact prefixLift 1401723
  have htrace : WordTrace (prefixWord ++ tailWord_1401723) baseStart_1401723 baseEnd_1401723 := by
    simpa [prefixWord, tailWord_1401723, baseEnd_1401723] using wordTrace_append hprefix tailTrace_1401723
  have hstable : (prefixWord ++ tailWord_1401723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401723).length < 2 ^ (prefixWord ++ tailWord_1401723).sum := by decide
  have hdescent : baseEnd_1401723 < baseStart_1401723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401737 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 1, 4, 2]
def baseStart_1401737 : Nat := 118140960795 + 1401737 * 2 ^ 59
def prefixEnd_1401737 : Nat := 4983230072969 + 3 ^ 40 * 1401737 * 2
def baseEnd_1401737 : Nat := 719764832191487431241035

theorem tailTrace_1401737 : CollatzResearch.WordTrace tailWord_1401737 prefixEnd_1401737 719764832191487431241035 := by
  unfold tailWord_1401737
  simp only [CollatzResearch.WordTrace]
  refine ⟨51125548522753721465291465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34083699015169147643527643 51125548522753721465291465)
  ·
    refine ⟨38344161392065291098968599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51125548522753721465291465 38344161392065291098968599)
    ·
      refine ⟨57516242088097936648452899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38344161392065291098968599 57516242088097936648452899)
      ·
        refine ⟨86274363132146904972679349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57516242088097936648452899 86274363132146904972679349)
        ·
          refine ⟨8088221543638772341188689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86274363132146904972679349 8088221543638772341188689)
          ·
            refine ⟨6066166157729079255891517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8088221543638772341188689 6066166157729079255891517)
            ·
              refine ⟨2274812309148404720959319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6066166157729079255891517 2274812309148404720959319)
              ·
                refine ⟨3412218463722607081438979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274812309148404720959319 3412218463722607081438979)
                ·
                  refine ⟨5118327695583910622158469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412218463722607081438979 5118327695583910622158469)
                  ·
                    refine ⟨959686442921983241654713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118327695583910622158469 959686442921983241654713)
                    ·
                      refine ⟨719764832191487431241035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959686442921983241654713 719764832191487431241035)
                      ·
                        rfl

theorem cell23_1401737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 4, 2].length) (baseStart_1401737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401737 prefixEnd_1401737 := by exact prefixLift 1401737
  have htrace : WordTrace (prefixWord ++ tailWord_1401737) baseStart_1401737 baseEnd_1401737 := by
    simpa [prefixWord, tailWord_1401737, baseEnd_1401737] using wordTrace_append hprefix tailTrace_1401737
  have hstable : (prefixWord ++ tailWord_1401737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401737).length < 2 ^ (prefixWord ++ tailWord_1401737).sum := by decide
  have hdescent : baseEnd_1401737 < baseStart_1401737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401777 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 7]
def baseStart_1401777 : Nat := 118140960795 + 1401777 * 2 ^ 59
def prefixEnd_1401777 : Nat := 4983230072969 + 3 ^ 40 * 1401777 * 2
def baseEnd_1401777 : Nat := 79976152379740808304539

theorem tailTrace_1401777 : CollatzResearch.WordTrace tailWord_1401777 prefixEnd_1401777 79976152379740808304539 := by
  unfold tailWord_1401777
  simp only [CollatzResearch.WordTrace]
  refine ⟨51127007442608808296747585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34084671628405872197831723 51127007442608808296747585)
  ·
    refine ⟨38345255581956606222560689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51127007442608808296747585 38345255581956606222560689)
    ·
      refine ⟨28758941686467454666920517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38345255581956606222560689 28758941686467454666920517)
      ·
        refine ⟨5392301566212647750047597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28758941686467454666920517 5392301566212647750047597)
        ·
          refine ⟨2022113087329742906267849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5392301566212647750047597 2022113087329742906267849)
          ·
            refine ⟨1516584815497307179700887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022113087329742906267849 1516584815497307179700887)
            ·
              refine ⟨2274877223245960769551331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516584815497307179700887 2274877223245960769551331)
              ·
                refine ⟨3412315834868941154326997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274877223245960769551331 3412315834868941154326997)
                ·
                  refine ⟨79976152379740808304539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3412315834868941154326997 79976152379740808304539)
                  ·
                    rfl

theorem cell23_1401777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 7].length) (baseStart_1401777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401777 prefixEnd_1401777 := by exact prefixLift 1401777
  have htrace : WordTrace (prefixWord ++ tailWord_1401777) baseStart_1401777 baseEnd_1401777 := by
    simpa [prefixWord, tailWord_1401777, baseEnd_1401777] using wordTrace_append hprefix tailTrace_1401777
  have hstable : (prefixWord ++ tailWord_1401777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401777).length < 2 ^ (prefixWord ++ tailWord_1401777).sum := by decide
  have hdescent : baseEnd_1401777 < baseStart_1401777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401782 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1401782 : Nat := 118140960795 + 1401782 * 2 ^ 59
def prefixEnd_1401782 : Nat := 4983230072969 + 3 ^ 40 * 1401782 * 2
def baseEnd_1401782 : Nat := 719787938820939755178329

theorem tailTrace_1401782 : CollatzResearch.WordTrace tailWord_1401782 prefixEnd_1401782 719787938820939755178329 := by
  unfold tailWord_1401782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195449362974418384417475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34084793205060462767119733 3195449362974418384417475)
  ·
    refine ⟨4793174044461627576626213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3195449362974418384417475 4793174044461627576626213)
    ·
      refine ⟨898720133336555170617415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4793174044461627576626213 898720133336555170617415)
      ·
        refine ⟨1348080200004832755926123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898720133336555170617415 1348080200004832755926123)
        ·
          refine ⟨2022120300007249133889185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348080200004832755926123 2022120300007249133889185)
          ·
            refine ⟨1516590225005436850416889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022120300007249133889185 1516590225005436850416889)
            ·
              refine ⟨1137442668754077637812667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516590225005436850416889 1137442668754077637812667)
              ·
                refine ⟨1706164003131116456719001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137442668754077637812667 1706164003131116456719001)
                ·
                  refine ⟨1279623002348337342539251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706164003131116456719001 1279623002348337342539251)
                  ·
                    refine ⟨1919434503522506013808877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1279623002348337342539251 1919434503522506013808877)
                    ·
                      refine ⟨719787938820939755178329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1919434503522506013808877 719787938820939755178329)
                      ·
                        rfl

theorem cell23_1401782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1401782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401782 prefixEnd_1401782 := by exact prefixLift 1401782
  have htrace : WordTrace (prefixWord ++ tailWord_1401782) baseStart_1401782 baseEnd_1401782 := by
    simpa [prefixWord, tailWord_1401782, baseEnd_1401782] using wordTrace_append hprefix tailTrace_1401782
  have hstable : (prefixWord ++ tailWord_1401782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401782).length < 2 ^ (prefixWord ++ tailWord_1401782).sum := by decide
  have hdescent : baseEnd_1401782 < baseStart_1401782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401783 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_1401783 : Nat := 118140960795 + 1401783 * 2 ^ 59
def prefixEnd_1401783 : Nat := 4983230072969 + 3 ^ 40 * 1401783 * 2
def baseEnd_1401783 : Nat := 719788452301594251265823

theorem tailTrace_1401783 : CollatzResearch.WordTrace tailWord_1401783 prefixEnd_1401783 719788452301594251265823 := by
  unfold tailWord_1401783
  simp only [CollatzResearch.WordTrace]
  refine ⟨51127226280587071321466003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34084817520391380880977335 51127226280587071321466003)
  ·
    refine ⟨76690839420880606982199005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51127226280587071321466003 76690839420880606982199005)
    ·
      refine ⟨28759064782830227618324627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76690839420880606982199005 28759064782830227618324627)
      ·
        refine ⟨43138597174245341427486941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28759064782830227618324627 43138597174245341427486941)
        ·
          refine ⟨16176973940342003035307603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43138597174245341427486941 16176973940342003035307603)
          ·
            refine ⟨24265460910513004552961405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16176973940342003035307603 24265460910513004552961405)
            ·
              refine ⟨9099547841442376707360527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24265460910513004552961405 9099547841442376707360527)
              ·
                refine ⟨13649321762163565061040791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9099547841442376707360527 13649321762163565061040791)
                ·
                  refine ⟨20473982643245347591561187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13649321762163565061040791 20473982643245347591561187)
                  ·
                    refine ⟨30710973964868021387341781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20473982643245347591561187 30710973964868021387341781)
                    ·
                      refine ⟨719788452301594251265823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 30710973964868021387341781 719788452301594251265823)
                      ·
                        rfl

theorem cell23_1401783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_1401783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401783 prefixEnd_1401783 := by exact prefixLift 1401783
  have htrace : WordTrace (prefixWord ++ tailWord_1401783) baseStart_1401783 baseEnd_1401783 := by
    simpa [prefixWord, tailWord_1401783, baseEnd_1401783] using wordTrace_append hprefix tailTrace_1401783
  have hstable : (prefixWord ++ tailWord_1401783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401783).length < 2 ^ (prefixWord ++ tailWord_1401783).sum := by decide
  have hdescent : baseEnd_1401783 < baseStart_1401783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401790 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1401790 : Nat := 118140960795 + 1401790 * 2 ^ 59
def prefixEnd_1401790 : Nat := 4983230072969 + 3 ^ 40 * 1401790 * 2
def baseEnd_1401790 : Nat := 239930682222058574626097

theorem tailTrace_1401790 : CollatzResearch.WordTrace tailWord_1401790 prefixEnd_1401790 239930682222058574626097 := by
  unfold tailWord_1401790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390935198945213939621353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34084987727707807677980549 6390935198945213939621353)
  ·
    refine ⟨4793201399208910454716015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6390935198945213939621353 4793201399208910454716015)
    ·
      refine ⟨7189802098813365682074023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4793201399208910454716015 7189802098813365682074023)
      ·
        refine ⟨10784703148220048523111035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7189802098813365682074023 10784703148220048523111035)
        ·
          refine ⟨16177054722330072784666553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10784703148220048523111035 16177054722330072784666553)
          ·
            refine ⟨12132791041747554588499915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16177054722330072784666553 12132791041747554588499915)
            ·
              refine ⟨18199186562621331882749873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12132791041747554588499915 18199186562621331882749873)
              ·
                refine ⟨13649389921965998912062405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18199186562621331882749873 13649389921965998912062405)
                ·
                  refine ⟨2559260610368624796011701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13649389921965998912062405 2559260610368624796011701)
                  ·
                    refine ⟨239930682222058574626097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2559260610368624796011701 239930682222058574626097)
                    ·
                      rfl

theorem cell23_1401790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1401790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401790 prefixEnd_1401790 := by exact prefixLift 1401790
  have htrace : WordTrace (prefixWord ++ tailWord_1401790) baseStart_1401790 baseEnd_1401790 := by
    simpa [prefixWord, tailWord_1401790, baseEnd_1401790] using wordTrace_append hprefix tailTrace_1401790
  have hstable : (prefixWord ++ tailWord_1401790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401790).length < 2 ^ (prefixWord ++ tailWord_1401790).sum := by decide
  have hdescent : baseEnd_1401790 < baseStart_1401790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401827 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 2, 4, 2]
def baseStart_1401827 : Nat := 118140960795 + 1401827 * 2 ^ 59
def prefixEnd_1401827 : Nat := 4983230072969 + 3 ^ 40 * 1401827 * 2
def baseEnd_1401827 : Nat := 719811045450392079115621

theorem tailTrace_1401827 : CollatzResearch.WordTrace tailWord_1401827 prefixEnd_1401827 719811045450392079115621 := by
  unfold tailWord_1401827
  simp only [CollatzResearch.WordTrace]
  refine ⟨51128831092427666836067735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34085887394951777890711823 51128831092427666836067735)
  ·
    refine ⟨76693246638641500254101603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51128831092427666836067735 76693246638641500254101603)
    ·
      refine ⟨115039869957962250381152405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76693246638641500254101603 115039869957962250381152405)
      ·
        refine ⟨5392493904279480486616519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115039869957962250381152405 5392493904279480486616519)
        ·
          refine ⟨8088740856419220729924779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5392493904279480486616519 8088740856419220729924779)
          ·
            refine ⟨12133111284628831094887169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8088740856419220729924779 12133111284628831094887169)
            ·
              refine ⟨9099833463471623321165377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12133111284628831094887169 9099833463471623321165377)
              ·
                refine ⟨6824875097603717490874033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9099833463471623321165377 6824875097603717490874033)
                ·
                  refine ⟨5118656323202788118155525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6824875097603717490874033 5118656323202788118155525)
                  ·
                    refine ⟨959748060600522772154161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5118656323202788118155525 959748060600522772154161)
                    ·
                      refine ⟨719811045450392079115621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959748060600522772154161 719811045450392079115621)
                      ·
                        rfl

theorem cell23_1401827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_1401827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401827 prefixEnd_1401827 := by exact prefixLift 1401827
  have htrace : WordTrace (prefixWord ++ tailWord_1401827) baseStart_1401827 baseEnd_1401827 := by
    simpa [prefixWord, tailWord_1401827, baseEnd_1401827] using wordTrace_append hprefix tailTrace_1401827
  have hstable : (prefixWord ++ tailWord_1401827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401827).length < 2 ^ (prefixWord ++ tailWord_1401827).sum := by decide
  have hdescent : baseEnd_1401827 < baseStart_1401827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401858 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1401858 : Nat := 118140960795 + 1401858 * 2 ^ 59
def prefixEnd_1401858 : Nat := 4983230072969 + 3 ^ 40 * 1401858 * 2
def baseEnd_1401858 : Nat := 239942321116893819275993

theorem tailTrace_1401858 : CollatzResearch.WordTrace tailWord_1401858 prefixEnd_1401858 239942321116893819275993 := by
  unfold tailWord_1401858
  simp only [CollatzResearch.WordTrace]
  refine ⟨12782490438828839782611557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34086641170210239420297485 12782490438828839782611557)
  ·
    refine ⟨2396716957280407459239667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12782490438828839782611557 2396716957280407459239667)
    ·
      refine ⟨3595075435920611188859501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2396716957280407459239667 3595075435920611188859501)
      ·
        refine ⟨1348153288470229195822313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3595075435920611188859501 1348153288470229195822313)
        ·
          refine ⟨1011114966352671896866735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348153288470229195822313 1011114966352671896866735)
          ·
            refine ⟨1516672449529007845300103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011114966352671896866735 1516672449529007845300103)
            ·
              refine ⟨2275008674293511767950155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516672449529007845300103 2275008674293511767950155)
              ·
                refine ⟨3412513011440267651925233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275008674293511767950155 3412513011440267651925233)
                ·
                  refine ⟨2559384758580200738943925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3412513011440267651925233 2559384758580200738943925)
                  ·
                    refine ⟨239942321116893819275993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2559384758580200738943925 239942321116893819275993)
                    ·
                      rfl

theorem cell23_1401858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1401858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401858 prefixEnd_1401858 := by exact prefixLift 1401858
  have htrace : WordTrace (prefixWord ++ tailWord_1401858) baseStart_1401858 baseEnd_1401858 := by
    simpa [prefixWord, tailWord_1401858, baseEnd_1401858] using wordTrace_append hprefix tailTrace_1401858
  have hstable : (prefixWord ++ tailWord_1401858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401858).length < 2 ^ (prefixWord ++ tailWord_1401858).sum := by decide
  have hdescent : baseEnd_1401858 < baseStart_1401858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401864 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_1401864 : Nat := 118140960795 + 1401864 * 2 ^ 59
def prefixEnd_1401864 : Nat := 4983230072969 + 3 ^ 40 * 1401864 * 2
def baseEnd_1401864 : Nat := 719830044234608434352951

theorem tailTrace_1401864 : CollatzResearch.WordTrace tailWord_1401864 prefixEnd_1401864 719830044234608434352951 := by
  unfold tailWord_1401864
  simp only [CollatzResearch.WordTrace]
  refine ⟨25565090296646811077582323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34086787062195748103443097 25565090296646811077582323)
  ·
    refine ⟨38347635444970216616373485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25565090296646811077582323 38347635444970216616373485)
    ·
      refine ⟨14380363291863831231140057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38347635444970216616373485 14380363291863831231140057)
      ·
        refine ⟨10785272468897873423355043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14380363291863831231140057 10785272468897873423355043)
        ·
          refine ⟨16177908703346810135032565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10785272468897873423355043 16177908703346810135032565)
          ·
            refine ⟨1516678940938763450159303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16177908703346810135032565 1516678940938763450159303)
            ·
              refine ⟨2275018411408145175238955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516678940938763450159303 2275018411408145175238955)
              ·
                refine ⟨3412527617112217762858433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275018411408145175238955 3412527617112217762858433)
                ·
                  refine ⟨2559395712834163322143825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3412527617112217762858433 2559395712834163322143825)
                  ·
                    refine ⟨1919546784625622491607869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2559395712834163322143825 1919546784625622491607869)
                    ·
                      refine ⟨719830044234608434352951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1919546784625622491607869 719830044234608434352951)
                      ·
                        rfl

theorem cell23_1401864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_1401864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401864 prefixEnd_1401864 := by exact prefixLift 1401864
  have htrace : WordTrace (prefixWord ++ tailWord_1401864) baseStart_1401864 baseEnd_1401864 := by
    simpa [prefixWord, tailWord_1401864, baseEnd_1401864] using wordTrace_append hprefix tailTrace_1401864
  have hstable : (prefixWord ++ tailWord_1401864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401864).length < 2 ^ (prefixWord ++ tailWord_1401864).sum := by decide
  have hdescent : baseEnd_1401864 < baseStart_1401864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401884 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 6]
def baseStart_1401884 : Nat := 118140960795 + 1401884 * 2 ^ 59
def prefixEnd_1401884 : Nat := 4983230072969 + 3 ^ 40 * 1401884 * 2
def baseEnd_1401884 : Nat := 79982257094188706233651

theorem tailTrace_1401884 : CollatzResearch.WordTrace tailWord_1401884 prefixEnd_1401884 79982257094188706233651 := by
  unfold tailWord_1401884
  simp only [CollatzResearch.WordTrace]
  refine ⟨25565455026610582785446353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34087273368814110380595137 25565455026610582785446353)
  ·
    refine ⟨19174091269957937089084765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25565455026610582785446353 19174091269957937089084765)
    ·
      refine ⟨7190284226234226408406787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19174091269957937089084765 7190284226234226408406787)
      ·
        refine ⟨10785426339351339612610181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190284226234226408406787 10785426339351339612610181)
        ·
          refine ⟨2022267438628376177364409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10785426339351339612610181 2022267438628376177364409)
          ·
            refine ⟨1516700578971282133023307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022267438628376177364409 1516700578971282133023307)
            ·
              refine ⟨2275050868456923199534961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516700578971282133023307 2275050868456923199534961)
              ·
                refine ⟨1706288151342692399651221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275050868456923199534961 1706288151342692399651221)
                ·
                  refine ⟨79982257094188706233651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1706288151342692399651221 79982257094188706233651)
                  ·
                    rfl

theorem cell23_1401884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_1401884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401884 prefixEnd_1401884 := by exact prefixLift 1401884
  have htrace : WordTrace (prefixWord ++ tailWord_1401884) baseStart_1401884 baseEnd_1401884 := by
    simpa [prefixWord, tailWord_1401884, baseEnd_1401884] using wordTrace_append hprefix tailTrace_1401884
  have hstable : (prefixWord ++ tailWord_1401884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401884).length < 2 ^ (prefixWord ++ tailWord_1401884).sum := by decide
  have hdescent : baseEnd_1401884 < baseStart_1401884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401920 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_1401920 : Nat := 118140960795 + 1401920 * 2 ^ 59
def prefixEnd_1401920 : Nat := 4983230072969 + 3 ^ 40 * 1401920 * 2
def baseEnd_1401920 : Nat := 719858799151260215252693

theorem tailTrace_1401920 : CollatzResearch.WordTrace tailWord_1401920 prefixEnd_1401920 719858799151260215252693 := by
  unfold tailWord_1401920
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566111540545371859601607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34088148720727162479468809 25566111540545371859601607)
  ·
    refine ⟨38349167310818057789402411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25566111540545371859601607 38349167310818057789402411)
    ·
      refine ⟨57523750966227086684103617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38349167310818057789402411 57523750966227086684103617)
      ·
        refine ⟨43142813224670315013077713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57523750966227086684103617 43142813224670315013077713)
        ·
          refine ⟨32357109918502736259808285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43142813224670315013077713 32357109918502736259808285)
          ·
            refine ⟨12133916219438526097428107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32357109918502736259808285 12133916219438526097428107)
            ·
              refine ⟨18200874329157789146142161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12133916219438526097428107 18200874329157789146142161)
              ·
                refine ⟨13650655746868341859606621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18200874329157789146142161 13650655746868341859606621)
                ·
                  refine ⟨5118995905075628197352483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13650655746868341859606621 5118995905075628197352483)
                  ·
                    refine ⟨7678493857613442296028725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5118995905075628197352483 7678493857613442296028725)
                    ·
                      refine ⟨719858799151260215252693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7678493857613442296028725 719858799151260215252693)
                      ·
                        rfl

theorem cell23_1401920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_1401920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401920 prefixEnd_1401920 := by exact prefixLift 1401920
  have htrace : WordTrace (prefixWord ++ tailWord_1401920) baseStart_1401920 baseEnd_1401920 := by
    simpa [prefixWord, tailWord_1401920, baseEnd_1401920] using wordTrace_append hprefix tailTrace_1401920
  have hstable : (prefixWord ++ tailWord_1401920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401920).length < 2 ^ (prefixWord ++ tailWord_1401920).sum := by decide
  have hdescent : baseEnd_1401920 < baseStart_1401920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401927 : List Nat := [1, 1, 4, 1, 3, 2, 1, 2, 4, 4]
def baseStart_1401927 : Nat := 118140960795 + 1401927 * 2 ^ 59
def prefixEnd_1401927 : Nat := 4983230072969 + 3 ^ 40 * 1401927 * 2
def baseEnd_1401927 : Nat := 239954131171947229288387

theorem tailTrace_1401927 : CollatzResearch.WordTrace tailWord_1401927 prefixEnd_1401927 239954131171947229288387 := by
  unfold tailWord_1401927
  simp only [CollatzResearch.WordTrace]
  refine ⟨51132478392065383914708035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34088318928043589276472023 51132478392065383914708035)
  ·
    refine ⟨76698717588098075872062053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51132478392065383914708035 76698717588098075872062053)
    ·
      refine ⟨14381009547768389226011635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76698717588098075872062053 14381009547768389226011635)
      ·
        refine ⟨21571514321652583839017453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14381009547768389226011635 21571514321652583839017453)
        ·
          refine ⟨8089317870619718939631545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21571514321652583839017453 8089317870619718939631545)
          ·
            refine ⟨6066988402964789204723659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8089317870619718939631545 6066988402964789204723659)
            ·
              refine ⟨9100482604447183807085489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6066988402964789204723659 9100482604447183807085489)
              ·
                refine ⟨6825361953335387855314117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9100482604447183807085489 6825361953335387855314117)
                ·
                  refine ⟨1279755366250385222871397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6825361953335387855314117 1279755366250385222871397)
                  ·
                    refine ⟨239954131171947229288387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1279755366250385222871397 239954131171947229288387)
                    ·
                      rfl

theorem cell23_1401927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_1401927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401927 prefixEnd_1401927 := by exact prefixLift 1401927
  have htrace : WordTrace (prefixWord ++ tailWord_1401927) baseStart_1401927 baseEnd_1401927 := by
    simpa [prefixWord, tailWord_1401927, baseEnd_1401927] using wordTrace_append hprefix tailTrace_1401927
  have hstable : (prefixWord ++ tailWord_1401927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401927).length < 2 ^ (prefixWord ++ tailWord_1401927).sum := by decide
  have hdescent : baseEnd_1401927 < baseStart_1401927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401940 : List Nat := [2, 4, 1, 1, 1, 1, 13]
def baseStart_1401940 : Nat := 118140960795 + 1401940 * 2 ^ 59
def prefixEnd_1401940 : Nat := 4983230072969 + 3 ^ 40 * 1401940 * 2
def baseEnd_1401940 : Nat := 8887272453880865888921

theorem tailTrace_1401940 : CollatzResearch.WordTrace tailWord_1401940 prefixEnd_1401940 8887272453880865888921 := by
  unfold tailWord_1401940
  simp only [CollatzResearch.WordTrace]
  refine ⟨25566476270509143567465637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34088635027345524756620849 25566476270509143567465637)
  ·
    refine ⟨4793714300720464418899807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25566476270509143567465637 4793714300720464418899807)
    ·
      refine ⟨7190571451080696628349711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4793714300720464418899807 7190571451080696628349711)
      ·
        refine ⟨10785857176621044942524567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7190571451080696628349711 10785857176621044942524567)
        ·
          refine ⟨16178785764931567413786851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10785857176621044942524567 16178785764931567413786851)
          ·
            refine ⟨24268178647397351120680277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16178785764931567413786851 24268178647397351120680277)
            ·
              refine ⟨8887272453880865888921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 24268178647397351120680277 8887272453880865888921)
              ·
                rfl

theorem cell23_1401940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 13].length) (baseStart_1401940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401940 prefixEnd_1401940 := by exact prefixLift 1401940
  have htrace : WordTrace (prefixWord ++ tailWord_1401940) baseStart_1401940 baseEnd_1401940 := by
    simpa [prefixWord, tailWord_1401940, baseEnd_1401940] using wordTrace_append hprefix tailTrace_1401940
  have hstable : (prefixWord ++ tailWord_1401940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401940).length < 2 ^ (prefixWord ++ tailWord_1401940).sum := by decide
  have hdescent : baseEnd_1401940 < baseStart_1401940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401954 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1401954 : Nat := 118140960795 + 1401954 * 2 ^ 59
def prefixEnd_1401954 : Nat := 4983230072969 + 3 ^ 40 * 1401954 * 2
def baseEnd_1401954 : Nat := 719876257493513082227537

theorem tailTrace_1401954 : CollatzResearch.WordTrace tailWord_1401954 prefixEnd_1401954 719876257493513082227537 := by
  unfold tailWord_1401954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783365790741891881485229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34088975441978378350627277 12783365790741891881485229)
  ·
    refine ⟨4793762171528209455556961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12783365790741891881485229 4793762171528209455556961)
    ·
      refine ⟨3595321628646157091667721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4793762171528209455556961 3595321628646157091667721)
      ·
        refine ⟨2696491221484617818750791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3595321628646157091667721 2696491221484617818750791)
        ·
          refine ⟨4044736832226926728126187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696491221484617818750791 4044736832226926728126187)
          ·
            refine ⟨6067105248340390092189281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044736832226926728126187 6067105248340390092189281)
            ·
              refine ⟨4550328936255292569141961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6067105248340390092189281 4550328936255292569141961)
              ·
                refine ⟨3412746702191469426856471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4550328936255292569141961 3412746702191469426856471)
                ·
                  refine ⟨5119120053287204140284707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412746702191469426856471 5119120053287204140284707)
                  ·
                    refine ⟨7678680079930806210427061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5119120053287204140284707 7678680079930806210427061)
                    ·
                      refine ⟨719876257493513082227537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7678680079930806210427061 719876257493513082227537)
                      ·
                        rfl

theorem cell23_1401954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1401954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401954 prefixEnd_1401954 := by exact prefixLift 1401954
  have htrace : WordTrace (prefixWord ++ tailWord_1401954) baseStart_1401954 baseEnd_1401954 := by
    simpa [prefixWord, tailWord_1401954, baseEnd_1401954] using wordTrace_append hprefix tailTrace_1401954
  have hstable : (prefixWord ++ tailWord_1401954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401954).length < 2 ^ (prefixWord ++ tailWord_1401954).sum := by decide
  have hdescent : baseEnd_1401954 < baseStart_1401954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401961 : List Nat := [1, 2, 1, 1, 1, 8, 2, 1, 2, 4]
def baseStart_1401961 : Nat := 118140960795 + 1401961 * 2 ^ 59
def prefixEnd_1401961 : Nat := 4983230072969 + 3 ^ 40 * 1401961 * 2
def baseEnd_1401961 : Nat := 239959950619364851613335

theorem tailTrace_1401961 : CollatzResearch.WordTrace tailWord_1401961 prefixEnd_1401961 239959950619364851613335 := by
  unfold tailWord_1401961
  simp only [CollatzResearch.WordTrace]
  refine ⟨51133718473942207721445737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34089145649294805147630491 51133718473942207721445737)
  ·
    refine ⟨38350288855456655791084303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51133718473942207721445737 38350288855456655791084303)
    ·
      refine ⟨57525433283184983686626455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38350288855456655791084303 57525433283184983686626455)
      ·
        refine ⟨86288149924777475529939683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57525433283184983686626455 86288149924777475529939683)
        ·
          refine ⟨129432224887166213294909525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86288149924777475529939683 129432224887166213294909525)
          ·
            refine ⟨1516783885396479062049721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 129432224887166213294909525 1516783885396479062049721)
            ·
              refine ⟨1137587914047359296537291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516783885396479062049721 1137587914047359296537291)
              ·
                refine ⟨1706381871071038944805937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137587914047359296537291 1706381871071038944805937)
                ·
                  refine ⟨1279786403303279208604453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706381871071038944805937 1279786403303279208604453)
                  ·
                    refine ⟨239959950619364851613335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1279786403303279208604453 239959950619364851613335)
                    ·
                      rfl

theorem cell23_1401961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 1, 2, 4].length) (baseStart_1401961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401961 prefixEnd_1401961 := by exact prefixLift 1401961
  have htrace : WordTrace (prefixWord ++ tailWord_1401961) baseStart_1401961 baseEnd_1401961 := by
    simpa [prefixWord, tailWord_1401961, baseEnd_1401961] using wordTrace_append hprefix tailTrace_1401961
  have hstable : (prefixWord ++ tailWord_1401961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401961).length < 2 ^ (prefixWord ++ tailWord_1401961).sum := by decide
  have hdescent : baseEnd_1401961 < baseStart_1401961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1401967 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 3]
def baseStart_1401967 : Nat := 118140960795 + 1401967 * 2 ^ 59
def prefixEnd_1401967 : Nat := 4983230072969 + 3 ^ 40 * 1401967 * 2
def baseEnd_1401967 : Nat := 719882932742021531364977

theorem tailTrace_1401967 : CollatzResearch.WordTrace tailWord_1401967 prefixEnd_1401967 719882932742021531364977 := by
  unfold tailWord_1401967
  simp only [CollatzResearch.WordTrace]
  refine ⟨51133937311920470746164155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34089291541280313830776103 51133937311920470746164155)
  ·
    refine ⟨76700905967880706119246233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51133937311920470746164155 76700905967880706119246233)
    ·
      refine ⟨57525679475910529589434675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76700905967880706119246233 57525679475910529589434675)
      ·
        refine ⟨86288519213865794384152013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57525679475910529589434675 86288519213865794384152013)
        ·
          refine ⟨32358194705199672894057005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86288519213865794384152013 32358194705199672894057005)
          ·
            refine ⟨12134323014449877335271377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32358194705199672894057005 12134323014449877335271377)
            ·
              refine ⟨9100742260837408001453533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12134323014449877335271377 9100742260837408001453533)
              ·
                refine ⟨3412778347814028000545075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9100742260837408001453533 3412778347814028000545075)
                ·
                  refine ⟨5119167521721042000817613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3412778347814028000545075 5119167521721042000817613)
                  ·
                    refine ⟨1919687820645390750306605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5119167521721042000817613 1919687820645390750306605)
                    ·
                      refine ⟨719882932742021531364977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1919687820645390750306605 719882932742021531364977)
                      ·
                        rfl

theorem cell23_1401967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_1401967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1401967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1401967 prefixEnd_1401967 := by exact prefixLift 1401967
  have htrace : WordTrace (prefixWord ++ tailWord_1401967) baseStart_1401967 baseEnd_1401967 := by
    simpa [prefixWord, tailWord_1401967, baseEnd_1401967] using wordTrace_append hprefix tailTrace_1401967
  have hstable : (prefixWord ++ tailWord_1401967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1401967).length < 2 ^ (prefixWord ++ tailWord_1401967).sum := by decide
  have hdescent : baseEnd_1401967 < baseStart_1401967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1401967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402002 : List Nat := [3, 2, 3, 1, 1, 4, 2, 2, 1, 2, 2]
def baseStart_1402002 : Nat := 118140960795 + 1402002 * 2 ^ 59
def prefixEnd_1402002 : Nat := 4983230072969 + 3 ^ 40 * 1402002 * 2
def baseEnd_1402002 : Nat := 719900904564928894427317

theorem tailTrace_1402002 : CollatzResearch.WordTrace tailWord_1402002 prefixEnd_1402002 719900904564928894427317 := by
  unfold tailWord_1402002
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783803466698417930922065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34090142577862447815792173 12783803466698417930922065)
  ·
    refine ⟨9587852600023813448191549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12783803466698417930922065 9587852600023813448191549)
    ·
      refine ⟨3595444725008930043071831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9587852600023813448191549 3595444725008930043071831)
      ·
        refine ⟨5393167087513395064607747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595444725008930043071831 5393167087513395064607747)
        ·
          refine ⟨8089750631270092596911621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393167087513395064607747 8089750631270092596911621)
          ·
            refine ⟨1516828243363142361920929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8089750631270092596911621 1516828243363142361920929)
            ·
              refine ⟨1137621182522356771440697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516828243363142361920929 1137621182522356771440697)
              ·
                refine ⟨853215886891767578580523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137621182522356771440697 853215886891767578580523)
                ·
                  refine ⟨1279823830337651367870785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853215886891767578580523 1279823830337651367870785)
                  ·
                    refine ⟨959867872753238525903089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1279823830337651367870785 959867872753238525903089)
                    ·
                      refine ⟨719900904564928894427317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959867872753238525903089 719900904564928894427317)
                      ·
                        rfl

theorem cell23_1402002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_1402002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402002 prefixEnd_1402002 := by exact prefixLift 1402002
  have htrace : WordTrace (prefixWord ++ tailWord_1402002) baseStart_1402002 baseEnd_1402002 := by
    simpa [prefixWord, tailWord_1402002, baseEnd_1402002] using wordTrace_append hprefix tailTrace_1402002
  have hstable : (prefixWord ++ tailWord_1402002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402002).length < 2 ^ (prefixWord ++ tailWord_1402002).sum := by decide
  have hdescent : baseEnd_1402002 < baseStart_1402002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402007 : List Nat := [1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_1402007 : Nat := 118140960795 + 1402007 * 2 ^ 59
def prefixEnd_1402007 : Nat := 4983230072969 + 3 ^ 40 * 1402007 * 2
def baseEnd_1402007 : Nat := 719903471968201374864793

theorem tailTrace_1402007 : CollatzResearch.WordTrace tailWord_1402007 prefixEnd_1402007 719903471968201374864793 := by
  unfold tailWord_1402007
  simp only [CollatzResearch.WordTrace]
  refine ⟨51135396231775557577620275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34090264154517038385080183 51135396231775557577620275)
  ·
    refine ⟨76703094347663336366430413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51135396231775557577620275 76703094347663336366430413)
    ·
      refine ⟨28763660380373751137411405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76703094347663336366430413 28763660380373751137411405)
      ·
        refine ⟨10786372642640156676529277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28763660380373751137411405 10786372642640156676529277)
        ·
          refine ⟨4044889740990058753698479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10786372642640156676529277 4044889740990058753698479)
          ·
            refine ⟨6067334611485088130547719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044889740990058753698479 6067334611485088130547719)
            ·
              refine ⟨9101001917227632195821579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6067334611485088130547719 9101001917227632195821579)
              ·
                refine ⟨13651502875841448293732369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9101001917227632195821579 13651502875841448293732369)
                ·
                  refine ⟨10238627156881086220299277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13651502875841448293732369 10238627156881086220299277)
                  ·
                    refine ⟨3839485183830407332612229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10238627156881086220299277 3839485183830407332612229)
                    ·
                      refine ⟨719903471968201374864793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3839485183830407332612229 719903471968201374864793)
                      ·
                        rfl

theorem cell23_1402007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_1402007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402007 prefixEnd_1402007 := by exact prefixLift 1402007
  have htrace : WordTrace (prefixWord ++ tailWord_1402007) baseStart_1402007 baseEnd_1402007 := by
    simpa [prefixWord, tailWord_1402007, baseEnd_1402007] using wordTrace_append hprefix tailTrace_1402007
  have hstable : (prefixWord ++ tailWord_1402007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402007).length < 2 ^ (prefixWord ++ tailWord_1402007).sum := by decide
  have hdescent : baseEnd_1402007 < baseStart_1402007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402017 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 2, 6]
def baseStart_1402017 : Nat := 118140960795 + 1402017 * 2 ^ 59
def prefixEnd_1402017 : Nat := 4983230072969 + 3 ^ 40 * 1402017 * 2
def baseEnd_1402017 : Nat := 239969535591582111913249

theorem tailTrace_1402017 : CollatzResearch.WordTrace tailWord_1402017 prefixEnd_1402017 239969535591582111913249 := by
  unfold tailWord_1402017
  simp only [CollatzResearch.WordTrace]
  refine ⟨51135760961739329285484305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34090507307826219523656203 51135760961739329285484305)
  ·
    refine ⟨38351820721304496964113229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51135760961739329285484305 38351820721304496964113229)
    ·
      refine ⟨14381932770489186361542461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38351820721304496964113229 14381932770489186361542461)
      ·
        refine ⟨5393224788933444885578423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14381932770489186361542461 5393224788933444885578423)
        ·
          refine ⟨8089837183400167328367635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393224788933444885578423 8089837183400167328367635)
          ·
            refine ⟨12134755775100250992551453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8089837183400167328367635 12134755775100250992551453)
            ·
              refine ⟨4550533415662594122206795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12134755775100250992551453 4550533415662594122206795)
              ·
                refine ⟨6825800123493891183310193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4550533415662594122206795 6825800123493891183310193)
                ·
                  refine ⟨5119350092620418387482645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6825800123493891183310193 5119350092620418387482645)
                  ·
                    refine ⟨239969535591582111913249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5119350092620418387482645 239969535591582111913249)
                    ·
                      rfl

theorem cell23_1402017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_1402017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402017 prefixEnd_1402017 := by exact prefixLift 1402017
  have htrace : WordTrace (prefixWord ++ tailWord_1402017) baseStart_1402017 baseEnd_1402017 := by
    simpa [prefixWord, tailWord_1402017, baseEnd_1402017] using wordTrace_append hprefix tailTrace_1402017
  have hstable : (prefixWord ++ tailWord_1402017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402017).length < 2 ^ (prefixWord ++ tailWord_1402017).sum := by decide
  have hdescent : baseEnd_1402017 < baseStart_1402017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402058 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_1402058 : Nat := 118140960795 + 1402058 * 2 ^ 59
def prefixEnd_1402058 : Nat := 4983230072969 + 3 ^ 40 * 1402058 * 2
def baseEnd_1402058 : Nat := 719929659481580675327059

theorem tailTrace_1402058 : CollatzResearch.WordTrace tailWord_1402058 prefixEnd_1402058 719929659481580675327059 := by
  unfold tailWord_1402058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12784314088647698321931707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34091504236393862191817885 12784314088647698321931707)
  ·
    refine ⟨19176471132971547482897561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12784314088647698321931707 19176471132971547482897561)
    ·
      refine ⟨14382353349728660612173171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19176471132971547482897561 14382353349728660612173171)
      ·
        refine ⟨21573530024592990918259757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14382353349728660612173171 21573530024592990918259757)
        ·
          refine ⟨8090073759222371594347409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21573530024592990918259757 8090073759222371594347409)
          ·
            refine ⟨6067555319416778695760557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8090073759222371594347409 6067555319416778695760557)
            ·
              refine ⟨2275333244781292010910209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6067555319416778695760557 2275333244781292010910209)
              ·
                refine ⟨1706499933585969008182657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275333244781292010910209 1706499933585969008182657)
                ·
                  refine ⟨1279874950189476756136993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1706499933585969008182657 1279874950189476756136993)
                  ·
                    refine ⟨959906212642107567102745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1279874950189476756136993 959906212642107567102745)
                    ·
                      refine ⟨719929659481580675327059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959906212642107567102745 719929659481580675327059)
                      ·
                        rfl

theorem cell23_1402058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_1402058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402058 prefixEnd_1402058 := by exact prefixLift 1402058
  have htrace : WordTrace (prefixWord ++ tailWord_1402058) baseStart_1402058 baseEnd_1402058 := by
    simpa [prefixWord, tailWord_1402058, baseEnd_1402058] using wordTrace_append hprefix tailTrace_1402058
  have hstable : (prefixWord ++ tailWord_1402058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402058).length < 2 ^ (prefixWord ++ tailWord_1402058).sum := by decide
  have hdescent : baseEnd_1402058 < baseStart_1402058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402084 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_1402084 : Nat := 118140960795 + 1402084 * 2 ^ 59
def prefixEnd_1402084 : Nat := 4983230072969 + 3 ^ 40 * 1402084 * 2
def baseEnd_1402084 : Nat := 719943009978597573601939

theorem tailTrace_1402084 : CollatzResearch.WordTrace tailWord_1402084 prefixEnd_1402084 719943009978597573601939 := by
  unfold tailWord_1402084
  simp only [CollatzResearch.WordTrace]
  refine ⟨25569102326248299864086653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34092136434997733152115537 25569102326248299864086653)
  ·
    refine ⟨9588413372343112449032495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25569102326248299864086653 9588413372343112449032495)
    ·
      refine ⟨14382620058514668673548743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9588413372343112449032495 14382620058514668673548743)
      ·
        refine ⟨21573930087772003010323115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14382620058514668673548743 21573930087772003010323115)
        ·
          refine ⟨32360895131658004515484673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21573930087772003010323115 32360895131658004515484673)
          ·
            refine ⟨24270671348743503386613505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32360895131658004515484673 24270671348743503386613505)
            ·
              refine ⟨18203003511557627539960129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24270671348743503386613505 18203003511557627539960129)
              ·
                refine ⟨13652252633668220654970097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18203003511557627539960129 13652252633668220654970097)
                ·
                  refine ⟨10239189475251165491227573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13652252633668220654970097 10239189475251165491227573)
                  ·
                    refine ⟨959924013304796764802585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10239189475251165491227573 959924013304796764802585)
                    ·
                      refine ⟨719943009978597573601939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959924013304796764802585 719943009978597573601939)
                      ·
                        rfl

theorem cell23_1402084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_1402084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402084 prefixEnd_1402084 := by exact prefixLift 1402084
  have htrace : WordTrace (prefixWord ++ tailWord_1402084) baseStart_1402084 baseEnd_1402084 := by
    simpa [prefixWord, tailWord_1402084, baseEnd_1402084] using wordTrace_append hprefix tailTrace_1402084
  have hstable : (prefixWord ++ tailWord_1402084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402084).length < 2 ^ (prefixWord ++ tailWord_1402084).sum := by decide
  have hdescent : baseEnd_1402084 < baseStart_1402084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402098 : List Nat := [3, 2, 1, 3, 3, 2, 1, 3, 5]
def baseStart_1402098 : Nat := 118140960795 + 1402098 * 2 ^ 59
def prefixEnd_1402098 : Nat := 4983230072969 + 3 ^ 40 * 1402098 * 2
def baseEnd_1402098 : Nat := 79994466523084502091875

theorem tailTrace_1402098 : CollatzResearch.WordTrace tailWord_1402098 prefixEnd_1402098 79994466523084502091875 := by
  unfold tailWord_1402098
  simp only [CollatzResearch.WordTrace]
  refine ⟨12784678818611470029795737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34092476849630586746121965 12784678818611470029795737)
  ·
    refine ⟨9588509113958602522346803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12784678818611470029795737 9588509113958602522346803)
    ·
      refine ⟨14382763670937903783520205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9588509113958602522346803 14382763670937903783520205)
      ·
        refine ⟨5393536376601713918820077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14382763670937903783520205 5393536376601713918820077)
        ·
          refine ⟨2022576141225642719557529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5393536376601713918820077 2022576141225642719557529)
          ·
            refine ⟨1516932105919232039668147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022576141225642719557529 1516932105919232039668147)
            ·
              refine ⟨2275398158878848059502221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516932105919232039668147 2275398158878848059502221)
              ·
                refine ⟨853274309579568022313333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275398158878848059502221 853274309579568022313333)
                ·
                  refine ⟨79994466523084502091875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 853274309579568022313333 79994466523084502091875)
                  ·
                    rfl

theorem cell23_1402098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_1402098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402098 prefixEnd_1402098 := by exact prefixLift 1402098
  have htrace : WordTrace (prefixWord ++ tailWord_1402098) baseStart_1402098 baseEnd_1402098 := by
    simpa [prefixWord, tailWord_1402098, baseEnd_1402098] using wordTrace_append hprefix tailTrace_1402098
  have hstable : (prefixWord ++ tailWord_1402098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402098).length < 2 ^ (prefixWord ++ tailWord_1402098).sum := by decide
  have hdescent : baseEnd_1402098 < baseStart_1402098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402174 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1402174 : Nat := 118140960795 + 1402174 * 2 ^ 59
def prefixEnd_1402174 : Nat := 4983230072969 + 3 ^ 40 * 1402174 * 2
def baseEnd_1402174 : Nat := 719989223237502221476525

theorem tailTrace_1402174 : CollatzResearch.WordTrace tailWord_1402174 prefixEnd_1402174 719989223237502221476525 := by
  unfold tailWord_1402174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6392685902771318137368697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 34094324814780363399299717 6392685902771318137368697)
  ·
    refine ⟨4794514427078488603026523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6392685902771318137368697 4794514427078488603026523)
    ·
      refine ⟨7191771640617732904539785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4794514427078488603026523 7191771640617732904539785)
      ·
        refine ⟨5393828730463299678404839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7191771640617732904539785 5393828730463299678404839)
        ·
          refine ⟨8090743095694949517607259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5393828730463299678404839 8090743095694949517607259)
          ·
            refine ⟨12136114643542424276410889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8090743095694949517607259 12136114643542424276410889)
            ·
              refine ⟨9102085982656818207308167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12136114643542424276410889 9102085982656818207308167)
              ·
                refine ⟨13653128973985227310962251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9102085982656818207308167 13653128973985227310962251)
                ·
                  refine ⟨20479693460977840966443377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13653128973985227310962251 20479693460977840966443377)
                  ·
                    refine ⟨15359770095733380724832533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20479693460977840966443377 15359770095733380724832533)
                    ·
                      refine ⟨719989223237502221476525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15359770095733380724832533 719989223237502221476525)
                      ·
                        rfl

theorem cell23_1402174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1402174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402174 prefixEnd_1402174 := by exact prefixLift 1402174
  have htrace : WordTrace (prefixWord ++ tailWord_1402174) baseStart_1402174 baseEnd_1402174 := by
    simpa [prefixWord, tailWord_1402174, baseEnd_1402174] using wordTrace_append hprefix tailTrace_1402174
  have hstable : (prefixWord ++ tailWord_1402174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402174).length < 2 ^ (prefixWord ++ tailWord_1402174).sum := by decide
  have hdescent : baseEnd_1402174 < baseStart_1402174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402175 : List Nat := [1, 1, 2, 2, 4, 4, 2, 2, 1, 4]
def baseStart_1402175 : Nat := 118140960795 + 1402175 * 2 ^ 59
def prefixEnd_1402175 : Nat := 4983230072969 + 3 ^ 40 * 1402175 * 2
def baseEnd_1402175 : Nat := 239996578906052239188007

theorem tailTrace_1402175 : CollatzResearch.WordTrace tailWord_1402175 prefixEnd_1402175 239996578906052239188007 := by
  unfold tailWord_1402175
  simp only [CollatzResearch.WordTrace]
  refine ⟨51141523695166922269735979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34094349130111281513157319 51141523695166922269735979)
  ·
    refine ⟨76712285542750383404603969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51141523695166922269735979 76712285542750383404603969)
    ·
      refine ⟨57534214157062787553452977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76712285542750383404603969 57534214157062787553452977)
      ·
        refine ⟨43150660617797090665089733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57534214157062787553452977 43150660617797090665089733)
        ·
          refine ⟨8090748865836954499704325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43150660617797090665089733 8090748865836954499704325)
          ·
            refine ⟨1517015412344428968694561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8090748865836954499704325 1517015412344428968694561)
            ·
              refine ⟨1137761559258321726520921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517015412344428968694561 1137761559258321726520921)
              ·
                refine ⟨853321169443741294890691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1137761559258321726520921 853321169443741294890691)
                ·
                  refine ⟨1279981754165611942336037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853321169443741294890691 1279981754165611942336037)
                  ·
                    refine ⟨239996578906052239188007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1279981754165611942336037 239996578906052239188007)
                    ·
                      rfl

theorem cell23_1402175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 2, 2, 1, 4].length) (baseStart_1402175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402175 prefixEnd_1402175 := by exact prefixLift 1402175
  have htrace : WordTrace (prefixWord ++ tailWord_1402175) baseStart_1402175 baseEnd_1402175 := by
    simpa [prefixWord, tailWord_1402175, baseEnd_1402175] using wordTrace_append hprefix tailTrace_1402175
  have hstable : (prefixWord ++ tailWord_1402175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402175).length < 2 ^ (prefixWord ++ tailWord_1402175).sum := by decide
  have hdescent : baseEnd_1402175 < baseStart_1402175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402182 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1402182 : Nat := 118140960795 + 1402182 * 2 ^ 59
def prefixEnd_1402182 : Nat := 4983230072969 + 3 ^ 40 * 1402182 * 2
def baseEnd_1402182 : Nat := 719993331082738190176489

theorem tailTrace_1402182 : CollatzResearch.WordTrace tailWord_1402182 prefixEnd_1402182 719993331082738190176489 := by
  unfold tailWord_1402182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598180593941923827038775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 34094519337427708310160533 1598180593941923827038775)
  ·
    refine ⟨2397270890912885740558163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598180593941923827038775 2397270890912885740558163)
    ·
      refine ⟨3595906336369328610837245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397270890912885740558163 3595906336369328610837245)
      ·
        refine ⟨1348464876138498229063967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3595906336369328610837245 1348464876138498229063967)
        ·
          refine ⟨2022697314207747343595951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348464876138498229063967 2022697314207747343595951)
          ·
            refine ⟨3034045971311621015393927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022697314207747343595951 3034045971311621015393927)
            ·
              refine ⟨4551068956967431523090891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034045971311621015393927 4551068956967431523090891)
              ·
                refine ⟨6826603435451147284636337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551068956967431523090891 6826603435451147284636337)
                ·
                  refine ⟨5119952576588360463477253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6826603435451147284636337 5119952576588360463477253)
                  ·
                    refine ⟨959991108110317586901985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5119952576588360463477253 959991108110317586901985)
                    ·
                      refine ⟨719993331082738190176489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 959991108110317586901985 719993331082738190176489)
                      ·
                        rfl

theorem cell23_1402182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1402182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402182 prefixEnd_1402182 := by exact prefixLift 1402182
  have htrace : WordTrace (prefixWord ++ tailWord_1402182) baseStart_1402182 baseEnd_1402182 := by
    simpa [prefixWord, tailWord_1402182, baseEnd_1402182] using wordTrace_append hprefix tailTrace_1402182
  have hstable : (prefixWord ++ tailWord_1402182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402182).length < 2 ^ (prefixWord ++ tailWord_1402182).sum := by decide
  have hdescent : baseEnd_1402182 < baseStart_1402182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402208 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 2, 3, 2]
def baseStart_1402208 : Nat := 118140960795 + 1402208 * 2 ^ 59
def prefixEnd_1402208 : Nat := 4983230072969 + 3 ^ 40 * 1402208 * 2
def baseEnd_1402208 : Nat := 720006681579755088451369

theorem tailTrace_1402208 : CollatzResearch.WordTrace tailWord_1402208 prefixEnd_1402208 720006681579755088451369 := by
  unfold tailWord_1402208
  simp only [CollatzResearch.WordTrace]
  refine ⟨25571363652023684452843639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34095151536031579270458185 25571363652023684452843639)
  ·
    refine ⟨38357045478035526679265459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25571363652023684452843639 38357045478035526679265459)
    ·
      refine ⟨57535568217053290018898189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38357045478035526679265459 57535568217053290018898189)
      ·
        refine ⟨21575838081394983757086821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57535568217053290018898189 21575838081394983757086821)
        ·
          refine ⟨4045469640261559454453779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21575838081394983757086821 4045469640261559454453779)
          ·
            refine ⟨6068204460392339181680669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4045469640261559454453779 6068204460392339181680669)
            ·
              refine ⟨2275576672647127193130251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6068204460392339181680669 2275576672647127193130251)
              ·
                refine ⟨3413365008970690789695377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2275576672647127193130251 3413365008970690789695377)
                ·
                  refine ⟨2560023756728018092271533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3413365008970690789695377 2560023756728018092271533)
                  ·
                    refine ⟨960008908773006784601825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560023756728018092271533 960008908773006784601825)
                    ·
                      refine ⟨720006681579755088451369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960008908773006784601825 720006681579755088451369)
                      ·
                        rfl

theorem cell23_1402208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_1402208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402208 prefixEnd_1402208 := by exact prefixLift 1402208
  have htrace : WordTrace (prefixWord ++ tailWord_1402208) baseStart_1402208 baseEnd_1402208 := by
    simpa [prefixWord, tailWord_1402208, baseEnd_1402208] using wordTrace_append hprefix tailTrace_1402208
  have hstable : (prefixWord ++ tailWord_1402208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402208).length < 2 ^ (prefixWord ++ tailWord_1402208).sum := by decide
  have hdescent : baseEnd_1402208 < baseStart_1402208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402218 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1402218 : Nat := 118140960795 + 1402218 * 2 ^ 59
def prefixEnd_1402218 : Nat := 4983230072969 + 3 ^ 40 * 1402218 * 2
def baseEnd_1402218 : Nat := 240003938795433349775441

theorem tailTrace_1402218 : CollatzResearch.WordTrace tailWord_1402218 prefixEnd_1402218 240003938795433349775441 := by
  unfold tailWord_1402218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12785773008502785153387827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34095394689340760409034205 12785773008502785153387827)
  ·
    refine ⟨19178659512754177730081741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12785773008502785153387827 19178659512754177730081741)
    ·
      refine ⟨7191997317282816648780653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19178659512754177730081741 7191997317282816648780653)
      ·
        refine ⟨2696998993981056243292745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7191997317282816648780653 2696998993981056243292745)
        ·
          refine ⟨2022749245485792182469559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2696998993981056243292745 2022749245485792182469559)
          ·
            refine ⟨3034123868228688273704339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2022749245485792182469559 3034123868228688273704339)
            ·
              refine ⟨4551185802343032410556509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034123868228688273704339 4551185802343032410556509)
              ·
                refine ⟨1706694675878637153958691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4551185802343032410556509 1706694675878637153958691)
                ·
                  refine ⟨2560042013817955730938037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706694675878637153958691 2560042013817955730938037)
                  ·
                    refine ⟨240003938795433349775441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2560042013817955730938037 240003938795433349775441)
                    ·
                      rfl

theorem cell23_1402218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1402218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402218 prefixEnd_1402218 := by exact prefixLift 1402218
  have htrace : WordTrace (prefixWord ++ tailWord_1402218) baseStart_1402218 baseEnd_1402218 := by
    simpa [prefixWord, tailWord_1402218, baseEnd_1402218] using wordTrace_append hprefix tailTrace_1402218
  have hstable : (prefixWord ++ tailWord_1402218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402218).length < 2 ^ (prefixWord ++ tailWord_1402218).sum := by decide
  have hdescent : baseEnd_1402218 < baseStart_1402218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402224 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_1402224 : Nat := 118140960795 + 1402224 * 2 ^ 59
def prefixEnd_1402224 : Nat := 4983230072969 + 3 ^ 40 * 1402224 * 2
def baseEnd_1402224 : Nat := 720014897270227025851295

theorem tailTrace_1402224 : CollatzResearch.WordTrace tailWord_1402224 prefixEnd_1402224 720014897270227025851295 := by
  unfold tailWord_1402224
  simp only [CollatzResearch.WordTrace]
  refine ⟨25571655435994701819134863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34095540581326269092179817 25571655435994701819134863)
  ·
    refine ⟨38357483153992052728702295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25571655435994701819134863 38357483153992052728702295)
    ·
      refine ⟨57536224730988079093053443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38357483153992052728702295 57536224730988079093053443)
      ·
        refine ⟨86304337096482118639580165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57536224730988079093053443 86304337096482118639580165)
        ·
          refine ⟨16182063205590397244921281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86304337096482118639580165 16182063205590397244921281)
          ·
            refine ⟨12136547404192797933690961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16182063205590397244921281 12136547404192797933690961)
            ·
              refine ⟨9102410553144598450268221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12136547404192797933690961 9102410553144598450268221)
              ·
                refine ⟨3413403957429224418850583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9102410553144598450268221 3413403957429224418850583)
                ·
                  refine ⟨5120105936143836628275875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3413403957429224418850583 5120105936143836628275875)
                  ·
                    refine ⟨7680158904215754942413813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120105936143836628275875 7680158904215754942413813)
                    ·
                      refine ⟨720014897270227025851295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7680158904215754942413813 720014897270227025851295)
                      ·
                        rfl

theorem cell23_1402224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_1402224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402224 prefixEnd_1402224 := by exact prefixLift 1402224
  have htrace : WordTrace (prefixWord ++ tailWord_1402224) baseStart_1402224 baseEnd_1402224 := by
    simpa [prefixWord, tailWord_1402224, baseEnd_1402224] using wordTrace_append hprefix tailTrace_1402224
  have hstable : (prefixWord ++ tailWord_1402224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402224).length < 2 ^ (prefixWord ++ tailWord_1402224).sum := by decide
  have hdescent : baseEnd_1402224 < baseStart_1402224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402281 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 7, 3, 2]
def baseStart_1402281 : Nat := 118140960795 + 1402281 * 2 ^ 59
def prefixEnd_1402281 : Nat := 4983230072969 + 3 ^ 40 * 1402281 * 2
def baseEnd_1402281 : Nat := 720044165667533302838533

theorem tailTrace_1402281 : CollatzResearch.WordTrace tailWord_1402281 prefixEnd_1402281 720044165667533302838533 := by
  unfold tailWord_1402281
  simp only [CollatzResearch.WordTrace]
  refine ⟨51145389832782902373094697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34096926555188601582063131 51145389832782902373094697)
  ·
    refine ⟨38359042374587176779821023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51145389832782902373094697 38359042374587176779821023)
    ·
      refine ⟨57538563561880765169731535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38359042374587176779821023 57538563561880765169731535)
      ·
        refine ⟨86307845342821147754597303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57538563561880765169731535 86307845342821147754597303)
        ·
          refine ⟨129461768014231721631895955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86307845342821147754597303 129461768014231721631895955)
          ·
            refine ⟨194192652021347582447843933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129461768014231721631895955 194192652021347582447843933)
            ·
              refine ⟨72822244508005343417941475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194192652021347582447843933 72822244508005343417941475)
              ·
                refine ⟨109233366762008015126912213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72822244508005343417941475 109233366762008015126912213)
                ·
                  refine ⟨2560157033484562854537005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 109233366762008015126912213 2560157033484562854537005)
                  ·
                    refine ⟨960058887556711070451377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2560157033484562854537005 960058887556711070451377)
                    ·
                      refine ⟨720044165667533302838533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960058887556711070451377 720044165667533302838533)
                      ·
                        rfl

theorem cell23_1402281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 3, 2].length) (baseStart_1402281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402281 prefixEnd_1402281 := by exact prefixLift 1402281
  have htrace : WordTrace (prefixWord ++ tailWord_1402281) baseStart_1402281 baseEnd_1402281 := by
    simpa [prefixWord, tailWord_1402281, baseEnd_1402281] using wordTrace_append hprefix tailTrace_1402281
  have hstable : (prefixWord ++ tailWord_1402281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402281).length < 2 ^ (prefixWord ++ tailWord_1402281).sum := by decide
  have hdescent : baseEnd_1402281 < baseStart_1402281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402304 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 2, 6]
def baseStart_1402304 : Nat := 118140960795 + 1402304 * 2 ^ 59
def prefixEnd_1402304 : Nat := 4983230072969 + 3 ^ 40 * 1402304 * 2
def baseEnd_1402304 : Nat := 240018658574195570950309

theorem tailTrace_1402304 : CollatzResearch.WordTrace tailWord_1402304 prefixEnd_1402304 240018658574195570950309 := by
  unfold tailWord_1402304
  simp only [CollatzResearch.WordTrace]
  refine ⟨25573114355849788650590983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34097485807799718200787977 25573114355849788650590983)
  ·
    refine ⟨38359671533774682975886475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25573114355849788650590983 38359671533774682975886475)
    ·
      refine ⟨57539507300662024463829713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38359671533774682975886475 57539507300662024463829713)
      ·
        refine ⟨43154630475496518347872285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57539507300662024463829713 43154630475496518347872285)
        ·
          refine ⟨16182986428311194380452107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43154630475496518347872285 16182986428311194380452107)
          ·
            refine ⟨24274479642466791570678161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16182986428311194380452107 24274479642466791570678161)
            ·
              refine ⟨18205859731850093678008621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24274479642466791570678161 18205859731850093678008621)
              ·
                refine ⟨6827197399443785129253233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18205859731850093678008621 6827197399443785129253233)
                ·
                  refine ⟨5120398049582838846939925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6827197399443785129253233 5120398049582838846939925)
                  ·
                    refine ⟨240018658574195570950309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5120398049582838846939925 240018658574195570950309)
                    ·
                      rfl

theorem cell23_1402304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_1402304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402304 prefixEnd_1402304 := by exact prefixLift 1402304
  have htrace : WordTrace (prefixWord ++ tailWord_1402304) baseStart_1402304 baseEnd_1402304 := by
    simpa [prefixWord, tailWord_1402304, baseEnd_1402304] using wordTrace_append hprefix tailTrace_1402304
  have hstable : (prefixWord ++ tailWord_1402304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402304).length < 2 ^ (prefixWord ++ tailWord_1402304).sum := by decide
  have hdescent : baseEnd_1402304 < baseStart_1402304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402306 : List Nat := [3, 5, 2, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_1402306 : Nat := 118140960795 + 1402306 * 2 ^ 59
def prefixEnd_1402306 : Nat := 4983230072969 + 3 ^ 40 * 1402306 * 2
def baseEnd_1402306 : Nat := 720057002683895705025919

theorem tailTrace_1402306 : CollatzResearch.WordTrace tailWord_1402306 prefixEnd_1402306 720057002683895705025919 := by
  unfold tailWord_1402306
  simp only [CollatzResearch.WordTrace]
  refine ⟨12786575414423082910688693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 34097534438461554428503181 12786575414423082910688693)
  ·
    refine ⟨1198741445102164022877065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12786575414423082910688693 1198741445102164022877065)
    ·
      refine ⟨899056083826623017157799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1198741445102164022877065 899056083826623017157799)
      ·
        refine ⟨1348584125739934525736699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899056083826623017157799 1348584125739934525736699)
        ·
          refine ⟨2022876188609901788605049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348584125739934525736699 2022876188609901788605049)
          ·
            refine ⟨1517157141457426341453787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022876188609901788605049 1517157141457426341453787)
            ·
              refine ⟨2275735712186139512180681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517157141457426341453787 2275735712186139512180681)
              ·
                refine ⟨1706801784139604634135511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275735712186139512180681 1706801784139604634135511)
                ·
                  refine ⟨2560202676209406951203267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1706801784139604634135511 2560202676209406951203267)
                  ·
                    refine ⟨3840304014314110426804901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2560202676209406951203267 3840304014314110426804901)
                    ·
                      refine ⟨720057002683895705025919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3840304014314110426804901 720057002683895705025919)
                      ·
                        rfl

theorem cell23_1402306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_1402306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402306 prefixEnd_1402306 := by exact prefixLift 1402306
  have htrace : WordTrace (prefixWord ++ tailWord_1402306) baseStart_1402306 baseEnd_1402306 := by
    simpa [prefixWord, tailWord_1402306, baseEnd_1402306] using wordTrace_append hprefix tailTrace_1402306
  have hstable : (prefixWord ++ tailWord_1402306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402306).length < 2 ^ (prefixWord ++ tailWord_1402306).sum := by decide
  have hdescent : baseEnd_1402306 < baseStart_1402306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402328 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 6, 2, 2]
def baseStart_1402328 : Nat := 118140960795 + 1402328 * 2 ^ 59
def prefixEnd_1402328 : Nat := 4983230072969 + 3 ^ 40 * 1402328 * 2
def baseEnd_1402328 : Nat := 720068299258294618950817

theorem tailTrace_1402328 : CollatzResearch.WordTrace tailWord_1402328 prefixEnd_1402328 720068299258294618950817 := by
  unfold tailWord_1402328
  simp only [CollatzResearch.WordTrace]
  refine ⟨25573552031806314700027819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34098069375741752933370425 25573552031806314700027819)
  ·
    refine ⟨38360328047709472050041729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25573552031806314700027819 38360328047709472050041729)
    ·
      refine ⟨28770246035782104037531297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38360328047709472050041729 28770246035782104037531297)
      ·
        refine ⟨21577684526836578028148473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28770246035782104037531297 21577684526836578028148473)
        ·
          refine ⟨16183263395127433521111355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21577684526836578028148473 16183263395127433521111355)
          ·
            refine ⟨24274895092691150281667033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16183263395127433521111355 24274895092691150281667033)
            ·
              refine ⟨18206171319518362711250275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24274895092691150281667033 18206171319518362711250275)
              ·
                refine ⟨27309256979277544066875413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18206171319518362711250275 27309256979277544066875413)
                ·
                  refine ⟨1280121420903634878134785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27309256979277544066875413 1280121420903634878134785)
                  ·
                    refine ⟨960091065677726158601089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280121420903634878134785 960091065677726158601089)
                    ·
                      refine ⟨720068299258294618950817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960091065677726158601089 720068299258294618950817)
                      ·
                        rfl

theorem cell23_1402328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_1402328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402328 prefixEnd_1402328 := by exact prefixLift 1402328
  have htrace : WordTrace (prefixWord ++ tailWord_1402328) baseStart_1402328 baseEnd_1402328 := by
    simpa [prefixWord, tailWord_1402328, baseEnd_1402328] using wordTrace_append hprefix tailTrace_1402328
  have hstable : (prefixWord ++ tailWord_1402328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402328).length < 2 ^ (prefixWord ++ tailWord_1402328).sum := by decide
  have hdescent : baseEnd_1402328 < baseStart_1402328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402358 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1402358 : Nat := 118140960795 + 1402358 * 2 ^ 59
def prefixEnd_1402358 : Nat := 4983230072969 + 3 ^ 40 * 1402358 * 2
def baseEnd_1402358 : Nat := 720083703677929501575679

theorem tailTrace_1402358 : CollatzResearch.WordTrace tailWord_1402358 prefixEnd_1402358 720083703677929501575679 := by
  unfold tailWord_1402358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196762390843996532727983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 34098798835669296349098485 3196762390843996532727983)
  ·
    refine ⟨4795143586265994799091975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3196762390843996532727983 4795143586265994799091975)
    ·
      refine ⟨7192715379398992198637963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4795143586265994799091975 7192715379398992198637963)
      ·
        refine ⟨10789073069098488297956945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7192715379398992198637963 10789073069098488297956945)
        ·
          refine ⟨8091804801823866223467709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10789073069098488297956945 8091804801823866223467709)
          ·
            refine ⟨3034426800683949833800391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8091804801823866223467709 3034426800683949833800391)
            ·
              refine ⟨4551640201025924750700587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034426800683949833800391 4551640201025924750700587)
              ·
                refine ⟨6827460301538887126050881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551640201025924750700587 6827460301538887126050881)
                ·
                  refine ⟨5120595226154165344538161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6827460301538887126050881 5120595226154165344538161)
                  ·
                    refine ⟨3840446419615624008403621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5120595226154165344538161 3840446419615624008403621)
                    ·
                      refine ⟨720083703677929501575679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3840446419615624008403621 720083703677929501575679)
                      ·
                        rfl

theorem cell23_1402358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1402358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402358 prefixEnd_1402358 := by exact prefixLift 1402358
  have htrace : WordTrace (prefixWord ++ tailWord_1402358) baseStart_1402358 baseEnd_1402358 := by
    simpa [prefixWord, tailWord_1402358, baseEnd_1402358] using wordTrace_append hprefix tailTrace_1402358
  have hstable : (prefixWord ++ tailWord_1402358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402358).length < 2 ^ (prefixWord ++ tailWord_1402358).sum := by decide
  have hdescent : baseEnd_1402358 < baseStart_1402358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402519 : List Nat := [1, 1, 3, 3, 2, 2, 4, 2, 1, 1, 3]
def baseStart_1402519 : Nat := 118140960795 + 1402519 * 2 ^ 59
def prefixEnd_1402519 : Nat := 4983230072969 + 3 ^ 40 * 1402519 * 2
def baseEnd_1402519 : Nat := 720166374063303371662439

theorem tailTrace_1402519 : CollatzResearch.WordTrace tailWord_1402519 prefixEnd_1402519 720166374063303371662439 := by
  unfold tailWord_1402519
  simp only [CollatzResearch.WordTrace]
  refine ⟨51154070405920669020258611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34102713603947112680172407 51154070405920669020258611)
  ·
    refine ⟨76731105608881003530387917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51154070405920669020258611 76731105608881003530387917)
    ·
      refine ⟨28774164603330376323895469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76731105608881003530387917 28774164603330376323895469)
      ·
        refine ⟨10790311726248891121460801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28774164603330376323895469 10790311726248891121460801)
        ·
          refine ⟨8092733794686668341095601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10790311726248891121460801 8092733794686668341095601)
          ·
            refine ⟨6069550346015001255821701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8092733794686668341095601 6069550346015001255821701)
            ·
              refine ⟨1138040689877812735466569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6069550346015001255821701 1138040689877812735466569)
              ·
                refine ⟨853530517408359551599927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138040689877812735466569 853530517408359551599927)
                ·
                  refine ⟨1280295776112539327399891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853530517408359551599927 1280295776112539327399891)
                  ·
                    refine ⟨1920443664168808991099837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1280295776112539327399891 1920443664168808991099837)
                    ·
                      refine ⟨720166374063303371662439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1920443664168808991099837 720166374063303371662439)
                      ·
                        rfl

theorem cell23_1402519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_1402519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402519 prefixEnd_1402519 := by exact prefixLift 1402519
  have htrace : WordTrace (prefixWord ++ tailWord_1402519) baseStart_1402519 baseEnd_1402519 := by
    simpa [prefixWord, tailWord_1402519, baseEnd_1402519] using wordTrace_append hprefix tailTrace_1402519
  have hstable : (prefixWord ++ tailWord_1402519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402519).length < 2 ^ (prefixWord ++ tailWord_1402519).sum := by decide
  have hdescent : baseEnd_1402519 < baseStart_1402519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402521 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_1402521 : Nat := 118140960795 + 1402521 * 2 ^ 59
def prefixEnd_1402521 : Nat := 4983230072969 + 3 ^ 40 * 1402521 * 2
def baseEnd_1402521 : Nat := 720167401024612363837429

theorem tailTrace_1402521 : CollatzResearch.WordTrace tailWord_1402521 prefixEnd_1402521 720167401024612363837429 := by
  unfold tailWord_1402521
  simp only [CollatzResearch.WordTrace]
  refine ⟨51154143351913423361831417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34102762234608948907887611 51154143351913423361831417)
  ·
    refine ⟨38365607513935067521373563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51154143351913423361831417 38365607513935067521373563)
    ·
      refine ⟨57548411270902601282060345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38365607513935067521373563 57548411270902601282060345)
      ·
        refine ⟨43161308453176950961545259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57548411270902601282060345 43161308453176950961545259)
        ·
          refine ⟨64741962679765426442317889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43161308453176950961545259 64741962679765426442317889)
          ·
            refine ⟨48556472009824069831738417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64741962679765426442317889 48556472009824069831738417)
            ·
              refine ⟨36417354007368052373803813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48556472009824069831738417 36417354007368052373803813)
              ·
                refine ⟨6828253876381509820088215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36417354007368052373803813 6828253876381509820088215)
                ·
                  refine ⟨10242380814572264730132323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6828253876381509820088215 10242380814572264730132323)
                  ·
                    refine ⟨15363571221858397095198485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10242380814572264730132323 15363571221858397095198485)
                    ·
                      refine ⟨720167401024612363837429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15363571221858397095198485 720167401024612363837429)
                      ·
                        rfl

theorem cell23_1402521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_1402521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402521 prefixEnd_1402521 := by exact prefixLift 1402521
  have htrace : WordTrace (prefixWord ++ tailWord_1402521) baseStart_1402521 baseEnd_1402521 := by
    simpa [prefixWord, tailWord_1402521, baseEnd_1402521] using wordTrace_append hprefix tailTrace_1402521
  have hstable : (prefixWord ++ tailWord_1402521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402521).length < 2 ^ (prefixWord ++ tailWord_1402521).sum := by decide
  have hdescent : baseEnd_1402521 < baseStart_1402521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402536 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_1402536 : Nat := 118140960795 + 1402536 * 2 ^ 59
def prefixEnd_1402536 : Nat := 4983230072969 + 3 ^ 40 * 1402536 * 2
def baseEnd_1402536 : Nat := 720175103234429805149861

theorem tailTrace_1402536 : CollatzResearch.WordTrace tailWord_1402536 prefixEnd_1402536 720175103234429805149861 := by
  unfold tailWord_1402536
  simp only [CollatzResearch.WordTrace]
  refine ⟨25577345223429540461813731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 34103126964572720615751641 25577345223429540461813731)
  ·
    refine ⟨38366017835144310692720597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25577345223429540461813731 38366017835144310692720597)
    ·
      refine ⟨899203543011194781860639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 38366017835144310692720597 899203543011194781860639)
      ·
        refine ⟨1348805314516792172790959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899203543011194781860639 1348805314516792172790959)
        ·
          refine ⟨2023207971775188259186439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348805314516792172790959 2023207971775188259186439)
          ·
            refine ⟨3034811957662782388779659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023207971775188259186439 3034811957662782388779659)
            ·
              refine ⟨4552217936494173583169489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034811957662782388779659 4552217936494173583169489)
              ·
                refine ⟨3414163452370630187377117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4552217936494173583169489 3414163452370630187377117)
                ·
                  refine ⟨1280311294638986320266419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3414163452370630187377117 1280311294638986320266419)
                  ·
                    refine ⟨1920466941958479480399629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1280311294638986320266419 1920466941958479480399629)
                    ·
                      refine ⟨720175103234429805149861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1920466941958479480399629 720175103234429805149861)
                      ·
                        rfl

theorem cell23_1402536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_1402536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402536 prefixEnd_1402536 := by exact prefixLift 1402536
  have htrace : WordTrace (prefixWord ++ tailWord_1402536) baseStart_1402536 baseEnd_1402536 := by
    simpa [prefixWord, tailWord_1402536, baseEnd_1402536] using wordTrace_append hprefix tailTrace_1402536
  have hstable : (prefixWord ++ tailWord_1402536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402536).length < 2 ^ (prefixWord ++ tailWord_1402536).sum := by decide
  have hdescent : baseEnd_1402536 < baseStart_1402536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1402559 : List Nat := [1, 1, 2, 2, 2, 3, 4, 3, 1, 2, 2]
def baseStart_1402559 : Nat := 118140960795 + 1402559 * 2 ^ 59
def prefixEnd_1402559 : Nat := 4983230072969 + 3 ^ 40 * 1402559 * 2
def baseEnd_1402559 : Nat := 720186913289483215162255

theorem tailTrace_1402559 : CollatzResearch.WordTrace tailWord_1402559 prefixEnd_1402559 720186913289483215162255 := by
  unfold tailWord_1402559
  simp only [CollatzResearch.WordTrace]
  refine ⟨51155529325775755851714731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 34103686217183837234476487 51155529325775755851714731)
  ·
    refine ⟨76733293988663633777572097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51155529325775755851714731 76733293988663633777572097)
    ·
      refine ⟨57549970491497725333179073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76733293988663633777572097 57549970491497725333179073)
      ·
        refine ⟨43162477868623293999884305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57549970491497725333179073 43162477868623293999884305)
        ·
          refine ⟨32371858401467470499913229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43162477868623293999884305 32371858401467470499913229)
          ·
            refine ⟨12139446900550301437467461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32371858401467470499913229 12139446900550301437467461)
            ·
              refine ⟨2276146293853181519525149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12139446900550301437467461 2276146293853181519525149)
              ·
                refine ⟨853554860194943069821931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2276146293853181519525149 853554860194943069821931)
                ·
                  refine ⟨1280332290292414604732897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853554860194943069821931 1280332290292414604732897)
                  ·
                    refine ⟨960249217719310953549673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1280332290292414604732897 960249217719310953549673)
                    ·
                      refine ⟨720186913289483215162255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 960249217719310953549673 720186913289483215162255)
                      ·
                        rfl

theorem cell23_1402559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_1402559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1402559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1402559 prefixEnd_1402559 := by exact prefixLift 1402559
  have htrace : WordTrace (prefixWord ++ tailWord_1402559) baseStart_1402559 baseEnd_1402559 := by
    simpa [prefixWord, tailWord_1402559, baseEnd_1402559] using wordTrace_append hprefix tailTrace_1402559
  have hstable : (prefixWord ++ tailWord_1402559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1402559).length < 2 ^ (prefixWord ++ tailWord_1402559).sum := by decide
  have hdescent : baseEnd_1402559 < baseStart_1402559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1402559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
