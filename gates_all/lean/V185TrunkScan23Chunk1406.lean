import V185TrunkScan23Chunk1405

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8328424 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_8328424 : Nat := 118140960795 + 8328424 * 2 ^ 59
def prefixEnd_8328424 : Nat := 4983230072969 + 3 ^ 40 * 8328424 * 2
def baseEnd_8328424 : Nat := 4276484606441028236498281

theorem tailTrace_8328424 : CollatzResearch.WordTrace tailWord_8328424 prefixEnd_8328424 4276484606441028236498281 := by
  unfold tailWord_8328424
  simp only [CollatzResearch.WordTrace]
  refine ⟨151881289189774852211364163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202508385586366469615152217 151881289189774852211364163)
  ·
    refine ⟨227821933784662278317046245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151881289189774852211364163 227821933784662278317046245)
    ·
      refine ⟨42716612584624177184446171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227821933784662278317046245 42716612584624177184446171)
      ·
        refine ⟨64074918876936265776669257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42716612584624177184446171 64074918876936265776669257)
        ·
          refine ⟨48056189157702199332501943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64074918876936265776669257 48056189157702199332501943)
          ·
            refine ⟨72084283736553298998752915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48056189157702199332501943 72084283736553298998752915)
            ·
              refine ⟨108126425604829948498129373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72084283736553298998752915 108126425604829948498129373)
              ·
                refine ⟨40547409601811230686798515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108126425604829948498129373 40547409601811230686798515)
                ·
                  refine ⟨60821114402716846030197773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40547409601811230686798515 60821114402716846030197773)
                  ·
                    refine ⟨22807917901018817261324165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60821114402716846030197773 22807917901018817261324165)
                    ·
                      refine ⟨4276484606441028236498281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22807917901018817261324165 4276484606441028236498281)
                      ·
                        rfl

theorem cell23_8328424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_8328424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328424 prefixEnd_8328424 := by exact prefixLift 8328424
  have htrace : WordTrace (prefixWord ++ tailWord_8328424) baseStart_8328424 baseEnd_8328424 := by
    simpa [prefixWord, tailWord_8328424, baseEnd_8328424] using wordTrace_append hprefix tailTrace_8328424
  have hstable : (prefixWord ++ tailWord_8328424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328424).length < 2 ^ (prefixWord ++ tailWord_8328424).sum := by decide
  have hdescent : baseEnd_8328424 < baseStart_8328424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328451 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 3, 4]
def baseStart_8328451 : Nat := 118140960795 + 8328451 * 2 ^ 59
def prefixEnd_8328451 : Nat := 4983230072969 + 3 ^ 40 * 8328451 * 2
def baseEnd_8328451 : Nat := 1425499490139566543620219

theorem tailTrace_8328451 : CollatzResearch.WordTrace tailWord_8328451 prefixEnd_8328451 1425499490139566543620219 := by
  unfold tailWord_8328451
  simp only [CollatzResearch.WordTrace]
  refine ⟨303763563150451888033961207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202509042100301258689307471 303763563150451888033961207)
  ·
    refine ⟨455645344725677832050941811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303763563150451888033961207 455645344725677832050941811)
    ·
      refine ⟨683468017088516748076412717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455645344725677832050941811 683468017088516748076412717)
      ·
        refine ⟨256300506408193780528654769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 683468017088516748076412717 256300506408193780528654769)
        ·
          refine ⟨192225379806145335396491077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256300506408193780528654769 192225379806145335396491077)
          ·
            refine ⟨36042258713652250386842077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192225379806145335396491077 36042258713652250386842077)
            ·
              refine ⟨13515847017619593895065779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36042258713652250386842077 13515847017619593895065779)
              ·
                refine ⟨20273770526429390842598669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13515847017619593895065779 20273770526429390842598669)
                ·
                  refine ⟨7602663947411021565974501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20273770526429390842598669 7602663947411021565974501)
                  ·
                    refine ⟨1425499490139566543620219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7602663947411021565974501 1425499490139566543620219)
                    ·
                      rfl

theorem cell23_8328451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 4].length) (baseStart_8328451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328451 prefixEnd_8328451 := by exact prefixLift 8328451
  have htrace : WordTrace (prefixWord ++ tailWord_8328451) baseStart_8328451 baseEnd_8328451 := by
    simpa [prefixWord, tailWord_8328451, baseEnd_8328451] using wordTrace_append hprefix tailTrace_8328451
  have hstable : (prefixWord ++ tailWord_8328451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328451).length < 2 ^ (prefixWord ++ tailWord_8328451).sum := by decide
  have hdescent : baseEnd_8328451 < baseStart_8328451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328531 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 4]
def baseStart_8328531 : Nat := 118140960795 + 8328531 * 2 ^ 59
def prefixEnd_8328531 : Nat := 4983230072969 + 3 ^ 40 * 8328531 * 2
def baseEnd_8328531 : Nat := 4276539548871059317860289

theorem tailTrace_8328531 : CollatzResearch.WordTrace tailWord_8328531 prefixEnd_8328531 4276539548871059317860289 := by
  unfold tailWord_8328531
  simp only [CollatzResearch.WordTrace]
  refine ⟨303766480990162061696873447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202510987326774707797915631 303766480990162061696873447)
  ·
    refine ⟨455649721485243092545310171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303766480990162061696873447 455649721485243092545310171)
    ·
      refine ⟨683474582227864638817965257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455649721485243092545310171 683474582227864638817965257)
      ·
        refine ⟨512605936670898479113473943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683474582227864638817965257 512605936670898479113473943)
        ·
          refine ⟨768908905006347718670210915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512605936670898479113473943 768908905006347718670210915)
          ·
            refine ⟨1153363357509521578005316373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768908905006347718670210915 1153363357509521578005316373)
            ·
              refine ⟨54063907383258823968999205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1153363357509521578005316373 54063907383258823968999205)
              ·
                refine ⟨10136982634361029494187351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54063907383258823968999205 10136982634361029494187351)
                ·
                  refine ⟨15205473951541544241281027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10136982634361029494187351 15205473951541544241281027)
                  ·
                    refine ⟨22808210927312316361921541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15205473951541544241281027 22808210927312316361921541)
                    ·
                      refine ⟨4276539548871059317860289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22808210927312316361921541 4276539548871059317860289)
                      ·
                        rfl

theorem cell23_8328531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 1, 4].length) (baseStart_8328531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328531 prefixEnd_8328531 := by exact prefixLift 8328531
  have htrace : WordTrace (prefixWord ++ tailWord_8328531) baseStart_8328531 baseEnd_8328531 := by
    simpa [prefixWord, tailWord_8328531, baseEnd_8328531] using wordTrace_append hprefix tailTrace_8328531
  have hstable : (prefixWord ++ tailWord_8328531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328531).length < 2 ^ (prefixWord ++ tailWord_8328531).sum := by decide
  have hdescent : baseEnd_8328531 < baseStart_8328531 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328535 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 2, 3, 2]
def baseStart_8328535 : Nat := 118140960795 + 8328535 * 2 ^ 59
def prefixEnd_8328535 : Nat := 4983230072969 + 3 ^ 40 * 8328535 * 2
def baseEnd_8328535 : Nat := 4276541602793677302210271

theorem tailTrace_8328535 : CollatzResearch.WordTrace tailWord_8328535 prefixEnd_8328535 4276541602793677302210271 := by
  unfold tailWord_8328535
  simp only [CollatzResearch.WordTrace]
  refine ⟨303766626882147570380019059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202511084588098380253346039 303766626882147570380019059)
  ·
    refine ⟨455649940323221355570028589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303766626882147570380019059 455649940323221355570028589)
    ·
      refine ⟨170868727621208008338760721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455649940323221355570028589 170868727621208008338760721)
      ·
        refine ⟨128151545715906006254070541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170868727621208008338760721 128151545715906006254070541)
        ·
          refine ⟨48056829643464752345276453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128151545715906006254070541 48056829643464752345276453)
          ·
            refine ⟨9010655558149641064739335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48056829643464752345276453 9010655558149641064739335)
            ·
              refine ⟨13515983337224461597109003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9010655558149641064739335 13515983337224461597109003)
              ·
                refine ⟨20273975005836692395663505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13515983337224461597109003 20273975005836692395663505)
                ·
                  refine ⟨15205481254377519296747629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20273975005836692395663505 15205481254377519296747629)
                  ·
                    refine ⟨5702055470391569736280361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15205481254377519296747629 5702055470391569736280361)
                    ·
                      refine ⟨4276541602793677302210271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702055470391569736280361 4276541602793677302210271)
                      ·
                        rfl

theorem cell23_8328535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_8328535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328535 prefixEnd_8328535 := by exact prefixLift 8328535
  have htrace : WordTrace (prefixWord ++ tailWord_8328535) baseStart_8328535 baseEnd_8328535 := by
    simpa [prefixWord, tailWord_8328535, baseEnd_8328535] using wordTrace_append hprefix tailTrace_8328535
  have hstable : (prefixWord ++ tailWord_8328535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328535).length < 2 ^ (prefixWord ++ tailWord_8328535).sum := by decide
  have hdescent : baseEnd_8328535 < baseStart_8328535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328548 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_8328548 : Nat := 118140960795 + 8328548 * 2 ^ 59
def prefixEnd_8328548 : Nat := 4983230072969 + 3 ^ 40 * 8328548 * 2
def baseEnd_8328548 : Nat := 4276548278042185751347711

theorem tailTrace_8328548 : CollatzResearch.WordTrace tailWord_8328548 prefixEnd_8328548 4276548278042185751347711 := by
  unfold tailWord_8328548
  simp only [CollatzResearch.WordTrace]
  refine ⟨151883550515550236800121149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202511400687400315733494865 151883550515550236800121149)
  ·
    refine ⟨56956331443331338800045431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151883550515550236800121149 56956331443331338800045431)
    ·
      refine ⟨85434497164997008200068147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56956331443331338800045431 85434497164997008200068147)
      ·
        refine ⟨128151745747495512300102221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85434497164997008200068147 128151745747495512300102221)
        ·
          refine ⟨48056904655310817112538333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128151745747495512300102221 48056904655310817112538333)
          ·
            refine ⟨18021339245741556417201875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48056904655310817112538333 18021339245741556417201875)
            ·
              refine ⟨27032008868612334625802813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18021339245741556417201875 27032008868612334625802813)
              ·
                refine ⟨10137003325729625484676055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27032008868612334625802813 10137003325729625484676055)
                ·
                  refine ⟨15205504988594438227014083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137003325729625484676055 15205504988594438227014083)
                  ·
                    refine ⟨22808257482891657340521125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15205504988594438227014083 22808257482891657340521125)
                    ·
                      refine ⟨4276548278042185751347711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22808257482891657340521125 4276548278042185751347711)
                      ·
                        rfl

theorem cell23_8328548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_8328548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328548 prefixEnd_8328548 := by exact prefixLift 8328548
  have htrace : WordTrace (prefixWord ++ tailWord_8328548) baseStart_8328548 baseEnd_8328548 := by
    simpa [prefixWord, tailWord_8328548, baseEnd_8328548] using wordTrace_append hprefix tailTrace_8328548
  have hstable : (prefixWord ++ tailWord_8328548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328548).length < 2 ^ (prefixWord ++ tailWord_8328548).sum := by decide
  have hdescent : baseEnd_8328548 < baseStart_8328548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328585 : List Nat := [1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 3]
def baseStart_8328585 : Nat := 118140960795 + 8328585 * 2 ^ 59
def prefixEnd_8328585 : Nat := 4983230072969 + 3 ^ 40 * 8328585 * 2
def baseEnd_8328585 : Nat := 4276567276826402106585041

theorem tailTrace_8328585 : CollatzResearch.WordTrace tailWord_8328585 prefixEnd_8328585 4276567276826402106585041 := by
  unfold tailWord_8328585
  simp only [CollatzResearch.WordTrace]
  refine ⟨303768450531966428919339209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202512300354644285946226139 303768450531966428919339209)
  ·
    refine ⟨227826337898974821689504407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303768450531966428919339209 227826337898974821689504407)
    ·
      refine ⟨341739506848462232534256611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227826337898974821689504407 341739506848462232534256611)
      ·
        refine ⟨512609260272693348801384917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341739506848462232534256611 512609260272693348801384917)
        ·
          refine ⟨12014279537641250362532459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 512609260272693348801384917 12014279537641250362532459)
          ·
            refine ⟨18021419306461875543798689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12014279537641250362532459 18021419306461875543798689)
            ·
              refine ⟨13516064479846406657849017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18021419306461875543798689 13516064479846406657849017)
              ·
                refine ⟨10137048359884804993386763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13516064479846406657849017 10137048359884804993386763)
                ·
                  refine ⟨15205572539827207490080145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137048359884804993386763 15205572539827207490080145)
                  ·
                    refine ⟨11404179404870405617560109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15205572539827207490080145 11404179404870405617560109)
                    ·
                      refine ⟨4276567276826402106585041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404179404870405617560109 4276567276826402106585041)
                      ·
                        rfl

theorem cell23_8328585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 2, 3].length) (baseStart_8328585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328585 prefixEnd_8328585 := by exact prefixLift 8328585
  have htrace : WordTrace (prefixWord ++ tailWord_8328585) baseStart_8328585 baseEnd_8328585 := by
    simpa [prefixWord, tailWord_8328585, baseEnd_8328585] using wordTrace_append hprefix tailTrace_8328585
  have hstable : (prefixWord ++ tailWord_8328585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328585).length < 2 ^ (prefixWord ++ tailWord_8328585).sum := by decide
  have hdescent : baseEnd_8328585 < baseStart_8328585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328615 : List Nat := [1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_8328615 : Nat := 118140960795 + 8328615 * 2 ^ 59
def prefixEnd_8328615 : Nat := 4983230072969 + 3 ^ 40 * 8328615 * 2
def baseEnd_8328615 : Nat := 4276582681246036989209903

theorem tailTrace_8328615 : CollatzResearch.WordTrace tailWord_8328615 prefixEnd_8328615 4276582681246036989209903 := by
  unfold tailWord_8328615
  simp only [CollatzResearch.WordTrace]
  refine ⟨303769544721857744042931299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202513029814571829361954199 303769544721857744042931299)
  ·
    refine ⟨455654317082786616064396949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303769544721857744042931299 455654317082786616064396949)
    ·
      refine ⟨21358796113255622628018607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 455654317082786616064396949 21358796113255622628018607)
      ·
        refine ⟨32038194169883433942027911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21358796113255622628018607 32038194169883433942027911)
        ·
          refine ⟨48057291254825150913041867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32038194169883433942027911 48057291254825150913041867)
          ·
            refine ⟨72085936882237726369562801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48057291254825150913041867 72085936882237726369562801)
            ·
              refine ⟨54064452661678294777172101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72085936882237726369562801 54064452661678294777172101)
              ·
                refine ⟨10137084874064680270719769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54064452661678294777172101 10137084874064680270719769)
                ·
                  refine ⟨7602813655548510203039827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137084874064680270719769 7602813655548510203039827)
                  ·
                    refine ⟨11404220483322765304559741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7602813655548510203039827 11404220483322765304559741)
                    ·
                      refine ⟨4276582681246036989209903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404220483322765304559741 4276582681246036989209903)
                      ·
                        rfl

theorem cell23_8328615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_8328615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328615 prefixEnd_8328615 := by exact prefixLift 8328615
  have htrace : WordTrace (prefixWord ++ tailWord_8328615) baseStart_8328615 baseEnd_8328615 := by
    simpa [prefixWord, tailWord_8328615, baseEnd_8328615] using wordTrace_append hprefix tailTrace_8328615
  have hstable : (prefixWord ++ tailWord_8328615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328615).length < 2 ^ (prefixWord ++ tailWord_8328615).sum := by decide
  have hdescent : baseEnd_8328615 < baseStart_8328615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328616 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 3, 2, 2]
def baseStart_8328616 : Nat := 118140960795 + 8328616 * 2 ^ 59
def prefixEnd_8328616 : Nat := 4983230072969 + 3 ^ 40 * 8328616 * 2
def baseEnd_8328616 : Nat := 4276583194726691485297399

theorem tailTrace_8328616 : CollatzResearch.WordTrace tailWord_8328616 prefixEnd_8328616 4276583194726691485297399 := by
  unfold tailWord_8328616
  simp only [CollatzResearch.WordTrace]
  refine ⟨151884790597427060606858851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202513054129902747475811801 151884790597427060606858851)
  ·
    refine ⟨227827185896140590910288277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151884790597427060606858851 227827185896140590910288277)
    ·
      refine ⟨10679399338881590198919763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227827185896140590910288277 10679399338881590198919763)
      ·
        refine ⟨16019099008322385298379645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679399338881590198919763 16019099008322385298379645)
        ·
          refine ⟨6007162128120894486892367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16019099008322385298379645 6007162128120894486892367)
          ·
            refine ⟨9010743192181341730338551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007162128120894486892367 9010743192181341730338551)
            ·
              refine ⟨13516114788272012595507827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9010743192181341730338551 13516114788272012595507827)
              ·
                refine ⟨20274172182408018893261741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13516114788272012595507827 20274172182408018893261741)
                ·
                  refine ⟨7602814568403007084973153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20274172182408018893261741 7602814568403007084973153)
                  ·
                    refine ⟨5702110926302255313729865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7602814568403007084973153 5702110926302255313729865)
                    ·
                      refine ⟨4276583194726691485297399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702110926302255313729865 4276583194726691485297399)
                      ·
                        rfl

theorem cell23_8328616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_8328616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328616 prefixEnd_8328616 := by exact prefixLift 8328616
  have htrace : WordTrace (prefixWord ++ tailWord_8328616) baseStart_8328616 baseEnd_8328616 := by
    simpa [prefixWord, tailWord_8328616, baseEnd_8328616] using wordTrace_append hprefix tailTrace_8328616
  have hstable : (prefixWord ++ tailWord_8328616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328616).length < 2 ^ (prefixWord ++ tailWord_8328616).sum := by decide
  have hdescent : baseEnd_8328616 < baseStart_8328616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328685 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_8328685 : Nat := 118140960795 + 8328685 * 2 ^ 59
def prefixEnd_8328685 : Nat := 4983230072969 + 3 ^ 40 * 8328685 * 2
def baseEnd_8328685 : Nat := 4276618624891851715334581

theorem tailTrace_8328685 : CollatzResearch.WordTrace tailWord_8328685 prefixEnd_8328685 4276618624891851715334581 := by
  unfold tailWord_8328685
  simp only [CollatzResearch.WordTrace]
  refine ⟨303772097831604145997979509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202514731887736097331986339 303772097831604145997979509)
  ·
    refine ⟨28478634171712888687310579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303772097831604145997979509 28478634171712888687310579)
    ·
      refine ⟨42717951257569333030965869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28478634171712888687310579 42717951257569333030965869)
      ·
        refine ⟨16019231721588499886612201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42717951257569333030965869 16019231721588499886612201)
        ·
          refine ⟨12014423791191374914959151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16019231721588499886612201 12014423791191374914959151)
          ·
            refine ⟨18021635686787062372438727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12014423791191374914959151 18021635686787062372438727)
            ·
              refine ⟨27032453530180593558658091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18021635686787062372438727 27032453530180593558658091)
              ·
                refine ⟨40548680295270890337987137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27032453530180593558658091 40548680295270890337987137)
                ·
                  refine ⟨30411510221453167753490353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40548680295270890337987137 30411510221453167753490353)
                  ·
                    refine ⟨22808632666089875815117765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30411510221453167753490353 22808632666089875815117765)
                    ·
                      refine ⟨4276618624891851715334581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22808632666089875815117765 4276618624891851715334581)
                      ·
                        rfl

theorem cell23_8328685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_8328685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328685 prefixEnd_8328685 := by exact prefixLift 8328685
  have htrace : WordTrace (prefixWord ++ tailWord_8328685) baseStart_8328685 baseEnd_8328685 := by
    simpa [prefixWord, tailWord_8328685, baseEnd_8328685] using wordTrace_append hprefix tailTrace_8328685
  have hstable : (prefixWord ++ tailWord_8328685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328685).length < 2 ^ (prefixWord ++ tailWord_8328685).sum := by decide
  have hdescent : baseEnd_8328685 < baseStart_8328685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328688 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3]
def baseStart_8328688 : Nat := 118140960795 + 8328688 * 2 ^ 59
def prefixEnd_8328688 : Nat := 4983230072969 + 3 ^ 40 * 8328688 * 2
def baseEnd_8328688 : Nat := 4276620165333815203597067

theorem tailTrace_8328688 : CollatzResearch.WordTrace tailWord_8328688 prefixEnd_8328688 4276620165333815203597067 := by
  unfold tailWord_8328688
  simp only [CollatzResearch.WordTrace]
  refine ⟨151886103625296638755169359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202514804833728851673559145 151886103625296638755169359)
  ·
    refine ⟨227829155437944958132754039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151886103625296638755169359 227829155437944958132754039)
    ·
      refine ⟨341743733156917437199131059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227829155437944958132754039 341743733156917437199131059)
      ·
        refine ⟨512615599735376155798696589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341743733156917437199131059 512615599735376155798696589)
        ·
          refine ⟨192230849900766058424511221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512615599735376155798696589 192230849900766058424511221)
          ·
            refine ⟨18021642178196817977297927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192230849900766058424511221 18021642178196817977297927)
            ·
              refine ⟨27032463267295226965946891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18021642178196817977297927 27032463267295226965946891)
              ·
                refine ⟨40548694900942840448920337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27032463267295226965946891 40548694900942840448920337)
                ·
                  refine ⟨30411521175707130336690253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40548694900942840448920337 30411521175707130336690253)
                  ·
                    refine ⟨11404320440890173876258845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30411521175707130336690253 11404320440890173876258845)
                    ·
                      refine ⟨4276620165333815203597067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404320440890173876258845 4276620165333815203597067)
                      ·
                        rfl

theorem cell23_8328688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_8328688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328688 prefixEnd_8328688 := by exact prefixLift 8328688
  have htrace : WordTrace (prefixWord ++ tailWord_8328688) baseStart_8328688 baseEnd_8328688 := by
    simpa [prefixWord, tailWord_8328688, baseEnd_8328688] using wordTrace_append hprefix tailTrace_8328688
  have hstable : (prefixWord ++ tailWord_8328688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328688).length < 2 ^ (prefixWord ++ tailWord_8328688).sum := by decide
  have hdescent : baseEnd_8328688 < baseStart_8328688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328698 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2]
def baseStart_8328698 : Nat := 118140960795 + 8328698 * 2 ^ 59
def prefixEnd_8328698 : Nat := 4983230072969 + 3 ^ 40 * 8328698 * 2
def baseEnd_8328698 : Nat := 4276625300140360164472021

theorem tailTrace_8328698 : CollatzResearch.WordTrace tailWord_8328698 prefixEnd_8328698 4276625300140360164472021 := by
  unfold tailWord_8328698
  simp only [CollatzResearch.WordTrace]
  refine ⟨75943142995139262304550687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202515047987038032812135165 75943142995139262304550687)
  ·
    refine ⟨113914714492708893456826031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75943142995139262304550687 113914714492708893456826031)
    ·
      refine ⟨170872071739063340185239047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113914714492708893456826031 170872071739063340185239047)
      ·
        refine ⟨256308107608595010277858571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170872071739063340185239047 256308107608595010277858571)
        ·
          refine ⟨384462161412892515416787857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256308107608595010277858571 384462161412892515416787857)
          ·
            refine ⟨288346621059669386562590893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384462161412892515416787857 288346621059669386562590893)
            ·
              refine ⟨108129982897376019960971585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288346621059669386562590893 108129982897376019960971585)
              ·
                refine ⟨81097487173032014970728689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108129982897376019960971585 81097487173032014970728689)
                ·
                  refine ⟨60823115379774011228046517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81097487173032014970728689 60823115379774011228046517)
                  ·
                    refine ⟨5702167066853813552629361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60823115379774011228046517 5702167066853813552629361)
                    ·
                      refine ⟨4276625300140360164472021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702167066853813552629361 4276625300140360164472021)
                      ·
                        rfl

theorem cell23_8328698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2].length) (baseStart_8328698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328698 prefixEnd_8328698 := by exact prefixLift 8328698
  have htrace : WordTrace (prefixWord ++ tailWord_8328698) baseStart_8328698 baseEnd_8328698 := by
    simpa [prefixWord, tailWord_8328698, baseEnd_8328698] using wordTrace_append hprefix tailTrace_8328698
  have hstable : (prefixWord ++ tailWord_8328698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328698).length < 2 ^ (prefixWord ++ tailWord_8328698).sum := by decide
  have hdescent : baseEnd_8328698 < baseStart_8328698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328710 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_8328710 : Nat := 118140960795 + 8328710 * 2 ^ 59
def prefixEnd_8328710 : Nat := 4983230072969 + 3 ^ 40 * 8328710 * 2
def baseEnd_8328710 : Nat := 4276631461908214117521967

theorem tailTrace_8328710 : CollatzResearch.WordTrace tailWord_8328710 prefixEnd_8328710 4276631461908214117521967 := by
  unfold tailWord_8328710
  simp only [CollatzResearch.WordTrace]
  refine ⟨9492906551766049227113737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 202515339771009050178426389 9492906551766049227113737)
  ·
    refine ⟨7119679913824536920335303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9492906551766049227113737 7119679913824536920335303)
    ·
      refine ⟨10679519870736805380502955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7119679913824536920335303 10679519870736805380502955)
      ·
        refine ⟨16019279806105208070754433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679519870736805380502955 16019279806105208070754433)
        ·
          refine ⟨12014459854578906053065825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16019279806105208070754433 12014459854578906053065825)
          ·
            refine ⟨9010844890934179539799369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12014459854578906053065825 9010844890934179539799369)
            ·
              refine ⟨6758133668200634654849527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9010844890934179539799369 6758133668200634654849527)
              ·
                refine ⟨10137200502300951982274291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758133668200634654849527 10137200502300951982274291)
                ·
                  refine ⟨15205800753451427973411437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137200502300951982274291 15205800753451427973411437)
                  ·
                    refine ⟨5702175282544285490029289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15205800753451427973411437 5702175282544285490029289)
                    ·
                      refine ⟨4276631461908214117521967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702175282544285490029289 4276631461908214117521967)
                      ·
                        rfl

theorem cell23_8328710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_8328710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328710 prefixEnd_8328710 := by exact prefixLift 8328710
  have htrace : WordTrace (prefixWord ++ tailWord_8328710) baseStart_8328710 baseEnd_8328710 := by
    simpa [prefixWord, tailWord_8328710, baseEnd_8328710] using wordTrace_append hprefix tailTrace_8328710
  have hstable : (prefixWord ++ tailWord_8328710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328710).length < 2 ^ (prefixWord ++ tailWord_8328710).sum := by decide
  have hdescent : baseEnd_8328710 < baseStart_8328710 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328741 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 6]
def baseStart_8328741 : Nat := 118140960795 + 8328741 * 2 ^ 59
def prefixEnd_8328741 : Nat := 4983230072969 + 3 ^ 40 * 8328741 * 2
def baseEnd_8328741 : Nat := 4276647379808503496234323

theorem tailTrace_8328741 : CollatzResearch.WordTrace tailWord_8328741 prefixEnd_8328741 4276647379808503496234323 := by
  unfold tailWord_8328741
  simp only [CollatzResearch.WordTrace]
  refine ⟨303774140319401267562018077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202516093546267511708012051 303774140319401267562018077)
  ·
    refine ⟨113915302619775475335756779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303774140319401267562018077 113915302619775475335756779)
    ·
      refine ⟨170872953929663213003635169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113915302619775475335756779 170872953929663213003635169)
      ·
        refine ⟨128154715447247409752726377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170872953929663213003635169 128154715447247409752726377)
        ·
          refine ⟨96116036585435557314544783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128154715447247409752726377 96116036585435557314544783)
          ·
            refine ⟨144174054878153335971817175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96116036585435557314544783 144174054878153335971817175)
            ·
              refine ⟨216261082317230003957725763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144174054878153335971817175 216261082317230003957725763)
              ·
                refine ⟨324391623475845005936588645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216261082317230003957725763 324391623475845005936588645)
                ·
                  refine ⟨60823429401720938613110371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324391623475845005936588645 60823429401720938613110371)
                  ·
                    refine ⟨91235144102581407919665557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60823429401720938613110371 91235144102581407919665557)
                    ·
                      refine ⟨4276647379808503496234323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91235144102581407919665557 4276647379808503496234323)
                      ·
                        rfl

theorem cell23_8328741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_8328741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328741 prefixEnd_8328741 := by exact prefixLift 8328741
  have htrace : WordTrace (prefixWord ++ tailWord_8328741) baseStart_8328741 baseEnd_8328741 := by
    simpa [prefixWord, tailWord_8328741, baseEnd_8328741] using wordTrace_append hprefix tailTrace_8328741
  have hstable : (prefixWord ++ tailWord_8328741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328741).length < 2 ^ (prefixWord ++ tailWord_8328741).sum := by decide
  have hdescent : baseEnd_8328741 < baseStart_8328741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328846 : List Nat := [4, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_8328846 : Nat := 118140960795 + 8328846 * 2 ^ 59
def prefixEnd_8328846 : Nat := 4983230072969 + 3 ^ 40 * 8328846 * 2
def baseEnd_8328846 : Nat := 4276701295277225585421341

theorem tailTrace_8328846 : CollatzResearch.WordTrace tailWord_8328846 prefixEnd_8328846 4276701295277225585421341 := by
  unfold tailWord_8328846
  simp only [CollatzResearch.WordTrace]
  refine ⟨37972246248002608811823799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202518646656013913663060261 37972246248002608811823799)
  ·
    refine ⟨56958369372003913217735699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37972246248002608811823799 56958369372003913217735699)
    ·
      refine ⟨85437554058005869826603549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56958369372003913217735699 85437554058005869826603549)
      ·
        refine ⟨32039082771752201184976331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85437554058005869826603549 32039082771752201184976331)
        ·
          refine ⟨48058624157628301777464497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32039082771752201184976331 48058624157628301777464497)
          ·
            refine ⟨36043968118221226333098373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48058624157628301777464497 36043968118221226333098373)
            ·
              refine ⟨6758244022166479937455945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36043968118221226333098373 6758244022166479937455945)
              ·
                refine ⟨5068683016624859953091959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6758244022166479937455945 5068683016624859953091959)
                ·
                  refine ⟨7603024524937289929637939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5068683016624859953091959 7603024524937289929637939)
                  ·
                    refine ⟨11404536787405934894456909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7603024524937289929637939 11404536787405934894456909)
                    ·
                      refine ⟨4276701295277225585421341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404536787405934894456909 4276701295277225585421341)
                      ·
                        rfl

theorem cell23_8328846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_8328846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328846 prefixEnd_8328846 := by exact prefixLift 8328846
  have htrace : WordTrace (prefixWord ++ tailWord_8328846) baseStart_8328846 baseEnd_8328846 := by
    simpa [prefixWord, tailWord_8328846, baseEnd_8328846] using wordTrace_append hprefix tailTrace_8328846
  have hstable : (prefixWord ++ tailWord_8328846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328846).length < 2 ^ (prefixWord ++ tailWord_8328846).sum := by decide
  have hdescent : baseEnd_8328846 < baseStart_8328846 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328855 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_8328855 : Nat := 118140960795 + 8328855 * 2 ^ 59
def prefixEnd_8328855 : Nat := 4983230072969 + 3 ^ 40 * 8328855 * 2
def baseEnd_8328855 : Nat := 4276705916603116050208799

theorem tailTrace_8328855 : CollatzResearch.WordTrace tailWord_8328855 prefixEnd_8328855 4276705916603116050208799 := by
  unfold tailWord_8328855
  simp only [CollatzResearch.WordTrace]
  refine ⟨303778298240988265031668019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202518865493992176687778679 303778298240988265031668019)
  ·
    refine ⟨455667447361482397547502029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303778298240988265031668019 455667447361482397547502029)
    ·
      refine ⟨170875292760555899080313261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455667447361482397547502029 170875292760555899080313261)
      ·
        refine ⟨64078234785208462155117473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170875292760555899080313261 64078234785208462155117473)
        ·
          refine ⟨48058676088906346616338105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64078234785208462155117473 48058676088906346616338105)
          ·
            refine ⟨36044007066679759962253579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48058676088906346616338105 36044007066679759962253579)
            ·
              refine ⟨54066010600019639943380369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36044007066679759962253579 54066010600019639943380369)
              ·
                refine ⟨40549507950014729957535277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54066010600019639943380369 40549507950014729957535277)
                ·
                  refine ⟨15206065481255523734075729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40549507950014729957535277 15206065481255523734075729)
                  ·
                    refine ⟨11404549110941642800556797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15206065481255523734075729 11404549110941642800556797)
                    ·
                      refine ⟨4276705916603116050208799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404549110941642800556797 4276705916603116050208799)
                      ·
                        rfl

theorem cell23_8328855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_8328855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328855 prefixEnd_8328855 := by exact prefixLift 8328855
  have htrace : WordTrace (prefixWord ++ tailWord_8328855) baseStart_8328855 baseEnd_8328855 := by
    simpa [prefixWord, tailWord_8328855, baseEnd_8328855] using wordTrace_append hprefix tailTrace_8328855
  have hstable : (prefixWord ++ tailWord_8328855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328855).length < 2 ^ (prefixWord ++ tailWord_8328855).sum := by decide
  have hdescent : baseEnd_8328855 < baseStart_8328855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328862 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_8328862 : Nat := 118140960795 + 8328862 * 2 ^ 59
def prefixEnd_8328862 : Nat := 4983230072969 + 3 ^ 40 * 8328862 * 2
def baseEnd_8328862 : Nat := 1425569836989232507607089

theorem tailTrace_8328862 : CollatzResearch.WordTrace tailWord_8328862 prefixEnd_8328862 1425569836989232507607089 := by
  unfold tailWord_8328862
  simp only [CollatzResearch.WordTrace]
  refine ⟨37972319193995363153396605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202519035701308603484781893 37972319193995363153396605)
  ·
    refine ⟨14239619697748261182523727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37972319193995363153396605 14239619697748261182523727)
    ·
      refine ⟨21359429546622391773785591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14239619697748261182523727 21359429546622391773785591)
      ·
        refine ⟨32039144319933587660678387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21359429546622391773785591 32039144319933587660678387)
        ·
          refine ⟨48058716479900381491017581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32039144319933587660678387 48058716479900381491017581)
          ·
            refine ⟨18022018679962643059131593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48058716479900381491017581 18022018679962643059131593)
            ·
              refine ⟨13516514009971982294348695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18022018679962643059131593 13516514009971982294348695)
              ·
                refine ⟨20274771014957973441523043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13516514009971982294348695 20274771014957973441523043)
                ·
                  refine ⟨30412156522436960162284565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20274771014957973441523043 30412156522436960162284565)
                  ·
                    refine ⟨1425569836989232507607089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30412156522436960162284565 1425569836989232507607089)
                    ·
                      rfl

theorem cell23_8328862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_8328862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328862 prefixEnd_8328862 := by exact prefixLift 8328862
  have htrace : WordTrace (prefixWord ++ tailWord_8328862) baseStart_8328862 baseEnd_8328862 := by
    simpa [prefixWord, tailWord_8328862, baseEnd_8328862] using wordTrace_append hprefix tailTrace_8328862
  have hstable : (prefixWord ++ tailWord_8328862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328862).length < 2 ^ (prefixWord ++ tailWord_8328862).sum := by decide
  have hdescent : baseEnd_8328862 < baseStart_8328862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328865 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_8328865 : Nat := 118140960795 + 8328865 * 2 ^ 59
def prefixEnd_8328865 : Nat := 4983230072969 + 3 ^ 40 * 8328865 * 2
def baseEnd_8328865 : Nat := 4276711051409661011083753

theorem tailTrace_8328865 : CollatzResearch.WordTrace tailWord_8328865 prefixEnd_8328865 4276711051409661011083753 := by
  unfold tailWord_8328865
  simp only [CollatzResearch.WordTrace]
  refine ⟨303778662970952036739532049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202519108647301357826354699 303778662970952036739532049)
  ·
    refine ⟨227833997228214027554649037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303778662970952036739532049 227833997228214027554649037)
    ·
      refine ⟨85437748960580260332993389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227833997228214027554649037 85437748960580260332993389)
      ·
        refine ⟨32039155860217597624872521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85437748960580260332993389 32039155860217597624872521)
        ·
          refine ⟨24029366895163198218654391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32039155860217597624872521 24029366895163198218654391)
          ·
            refine ⟨36044050342744797327981587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24029366895163198218654391 36044050342744797327981587)
            ·
              refine ⟨54066075514117195991972381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36044050342744797327981587 54066075514117195991972381)
              ·
                refine ⟨20274778317793948496989643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54066075514117195991972381 20274778317793948496989643)
                ·
                  refine ⟨30412167476690922745484465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20274778317793948496989643 30412167476690922745484465)
                  ·
                    refine ⟨22809125607518192059113349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30412167476690922745484465 22809125607518192059113349)
                    ·
                      refine ⟨4276711051409661011083753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22809125607518192059113349 4276711051409661011083753)
                      ·
                        rfl

theorem cell23_8328865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_8328865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328865 prefixEnd_8328865 := by exact prefixLift 8328865
  have htrace : WordTrace (prefixWord ++ tailWord_8328865) baseStart_8328865 baseEnd_8328865 := by
    simpa [prefixWord, tailWord_8328865, baseEnd_8328865] using wordTrace_append hprefix tailTrace_8328865
  have hstable : (prefixWord ++ tailWord_8328865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328865).length < 2 ^ (prefixWord ++ tailWord_8328865).sum := by decide
  have hdescent : baseEnd_8328865 < baseStart_8328865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328886 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4]
def baseStart_8328886 : Nat := 118140960795 + 8328886 * 2 ^ 59
def prefixEnd_8328886 : Nat := 4983230072969 + 3 ^ 40 * 8328886 * 2
def baseEnd_8328886 : Nat := 4276721834503405428921157

theorem tailTrace_8328886 : CollatzResearch.WordTrace tailWord_8328886 prefixEnd_8328886 4276721834503405428921157 := by
  unfold tailWord_8328886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18986214306492247332877907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202519619269250638217364341 18986214306492247332877907)
  ·
    refine ⟨28479321459738370999316861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18986214306492247332877907 28479321459738370999316861)
    ·
      refine ⟨10679745547401889124743823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28479321459738370999316861 10679745547401889124743823)
      ·
        refine ⟨16019618321102833687115735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10679745547401889124743823 16019618321102833687115735)
        ·
          refine ⟨24029427481654250530673603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16019618321102833687115735 24029427481654250530673603)
          ·
            refine ⟨36044141222481375796010405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24029427481654250530673603 36044141222481375796010405)
            ·
              refine ⟨6758276479215257961751951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36044141222481375796010405 6758276479215257961751951)
              ·
                refine ⟨10137414718822886942627927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758276479215257961751951 10137414718822886942627927)
                ·
                  refine ⟨15206122078234330413941891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137414718822886942627927 15206122078234330413941891)
                  ·
                    refine ⟨22809183117351495620912837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15206122078234330413941891 22809183117351495620912837)
                    ·
                      refine ⟨4276721834503405428921157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22809183117351495620912837 4276721834503405428921157)
                      ·
                        rfl

theorem cell23_8328886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_8328886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328886 prefixEnd_8328886 := by exact prefixLift 8328886
  have htrace : WordTrace (prefixWord ++ tailWord_8328886) baseStart_8328886 baseEnd_8328886 := by
    simpa [prefixWord, tailWord_8328886, baseEnd_8328886] using wordTrace_append hprefix tailTrace_8328886
  have hstable : (prefixWord ++ tailWord_8328886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328886).length < 2 ^ (prefixWord ++ tailWord_8328886).sum := by decide
  have hdescent : baseEnd_8328886 < baseStart_8328886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328919 : List Nat := [1, 1, 3, 2, 1, 3, 5, 1, 2, 1, 3]
def baseStart_8328919 : Nat := 118140960795 + 8328919 * 2 ^ 59
def prefixEnd_8328919 : Nat := 4983230072969 + 3 ^ 40 * 8328919 * 2
def baseEnd_8328919 : Nat := 4276738779365003799808505

theorem tailTrace_8328919 : CollatzResearch.WordTrace tailWord_8328919 prefixEnd_8328919 4276738779365003799808505 := by
  unfold tailWord_8328919
  simp only [CollatzResearch.WordTrace]
  refine ⟨303780632512756403961997811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202520421675170935974665207 303780632512756403961997811)
  ·
    refine ⟨455670948769134605942996717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303780632512756403961997811 455670948769134605942996717)
    ·
      refine ⟨170876605788425477228623769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455670948769134605942996717 170876605788425477228623769)
      ·
        refine ⟨128157454341319107921467827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170876605788425477228623769 128157454341319107921467827)
        ·
          refine ⟨192236181511978661882201741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128157454341319107921467827 192236181511978661882201741)
          ·
            refine ⟨72088568066991998205825653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192236181511978661882201741 72088568066991998205825653)
            ·
              refine ⟨6758303256280499831796155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72088568066991998205825653 6758303256280499831796155)
              ·
                refine ⟨10137454884420749747694233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758303256280499831796155 10137454884420749747694233)
                ·
                  refine ⟨7603091163315562310770675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137454884420749747694233 7603091163315562310770675)
                  ·
                    refine ⟨11404636744973343466156013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7603091163315562310770675 11404636744973343466156013)
                    ·
                      refine ⟨4276738779365003799808505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404636744973343466156013 4276738779365003799808505)
                      ·
                        rfl

theorem cell23_8328919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_8328919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328919 prefixEnd_8328919 := by exact prefixLift 8328919
  have htrace : WordTrace (prefixWord ++ tailWord_8328919) baseStart_8328919 baseEnd_8328919 := by
    simpa [prefixWord, tailWord_8328919, baseEnd_8328919] using wordTrace_append hprefix tailTrace_8328919
  have hstable : (prefixWord ++ tailWord_8328919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328919).length < 2 ^ (prefixWord ++ tailWord_8328919).sum := by decide
  have hdescent : baseEnd_8328919 < baseStart_8328919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328942 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_8328942 : Nat := 118140960795 + 8328942 * 2 ^ 59
def prefixEnd_8328942 : Nat := 4983230072969 + 3 ^ 40 * 8328942 * 2
def baseEnd_8328942 : Nat := 4276750589420057209820899

theorem tailTrace_8328942 : CollatzResearch.WordTrace tailWord_8328942 prefixEnd_8328942 4276750589420057209820899 := by
  unfold tailWord_8328942
  simp only [CollatzResearch.WordTrace]
  refine ⟨37972683923959134861260635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202520980927782052593390053 37972683923959134861260635)
  ·
    refine ⟨56959025885938702291890953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37972683923959134861260635 56959025885938702291890953)
    ·
      refine ⟨42719269414454026718918215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56959025885938702291890953 42719269414454026718918215)
      ·
        refine ⟨64078904121681040078377323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42719269414454026718918215 64078904121681040078377323)
        ·
          refine ⟨96118356182521560117565985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64078904121681040078377323 96118356182521560117565985)
          ·
            refine ⟨72088767136891170088174489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96118356182521560117565985 72088767136891170088174489)
            ·
              refine ⟨54066575352668377566130867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72088767136891170088174489 54066575352668377566130867)
              ·
                refine ⟨81099863029002566349196301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54066575352668377566130867 81099863029002566349196301)
                ·
                  refine ⟨30412448635875962380948613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81099863029002566349196301 30412448635875962380948613)
                  ·
                    refine ⟨5702334119226742946427865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30412448635875962380948613 5702334119226742946427865)
                    ·
                      refine ⟨4276750589420057209820899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702334119226742946427865 4276750589420057209820899)
                      ·
                        rfl

theorem cell23_8328942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_8328942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328942 prefixEnd_8328942 := by exact prefixLift 8328942
  have htrace : WordTrace (prefixWord ++ tailWord_8328942) baseStart_8328942 baseEnd_8328942 := by
    simpa [prefixWord, tailWord_8328942, baseEnd_8328942] using wordTrace_append hprefix tailTrace_8328942
  have hstable : (prefixWord ++ tailWord_8328942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328942).length < 2 ^ (prefixWord ++ tailWord_8328942).sum := by decide
  have hdescent : baseEnd_8328942 < baseStart_8328942 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328945 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_8328945 : Nat := 118140960795 + 8328945 * 2 ^ 59
def prefixEnd_8328945 : Nat := 4983230072969 + 3 ^ 40 * 8328945 * 2
def baseEnd_8328945 : Nat := 4276752129862020698083385

theorem tailTrace_8328945 : CollatzResearch.WordTrace tailWord_8328945 prefixEnd_8328945 4276752129862020698083385 := by
  unfold tailWord_8328945
  simp only [CollatzResearch.WordTrace]
  refine ⟨303781580810662210402444289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202521053873774806934962859 303781580810662210402444289)
  ·
    refine ⟨227836185607996657801833217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303781580810662210402444289 227836185607996657801833217)
    ·
      refine ⟨170877139205997493351374913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227836185607996657801833217 170877139205997493351374913)
      ·
        refine ⟨128157854404498120013531185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170877139205997493351374913 128157854404498120013531185)
        ·
          refine ⟨96118390803373590010148389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128157854404498120013531185 96118390803373590010148389)
          ·
            refine ⟨18022198275632548126902823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96118390803373590010148389 18022198275632548126902823)
            ·
              refine ⟨27033297413448822190354235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18022198275632548126902823 27033297413448822190354235)
              ·
                refine ⟨40549946120173233285531353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27033297413448822190354235 40549946120173233285531353)
                ·
                  refine ⟨30412459590129924964148515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40549946120173233285531353 30412459590129924964148515)
                  ·
                    refine ⟨45618689385194887446222773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30412459590129924964148515 45618689385194887446222773)
                    ·
                      refine ⟨4276752129862020698083385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45618689385194887446222773 4276752129862020698083385)
                      ·
                        rfl

theorem cell23_8328945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_8328945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328945 prefixEnd_8328945 := by exact prefixLift 8328945
  have htrace : WordTrace (prefixWord ++ tailWord_8328945) baseStart_8328945 baseEnd_8328945 := by
    simpa [prefixWord, tailWord_8328945, baseEnd_8328945] using wordTrace_append hprefix tailTrace_8328945
  have hstable : (prefixWord ++ tailWord_8328945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328945).length < 2 ^ (prefixWord ++ tailWord_8328945).sum := by decide
  have hdescent : baseEnd_8328945 < baseStart_8328945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328962 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_8328962 : Nat := 118140960795 + 8328962 * 2 ^ 59
def prefixEnd_8328962 : Nat := 4983230072969 + 3 ^ 40 * 8328962 * 2
def baseEnd_8328962 : Nat := 4276760859033147131570807

theorem tailTrace_8328962 : CollatzResearch.WordTrace tailWord_8328962 prefixEnd_8328962 4276760859033147131570807 := by
  unfold tailWord_8328962
  simp only [CollatzResearch.WordTrace]
  refine ⟨75945550212900155576453285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202521467234400414870542093 75945550212900155576453285)
  ·
    refine ⟨14239790664918779170584991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75945550212900155576453285 14239790664918779170584991)
    ·
      refine ⟨21359685997378168755877487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14239790664918779170584991 21359685997378168755877487)
      ·
        refine ⟨32039528996067253133816231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21359685997378168755877487 32039528996067253133816231)
        ·
          refine ⟨48059293494100879700724347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32039528996067253133816231 48059293494100879700724347)
          ·
            refine ⟨72088940241151319551086521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48059293494100879700724347 72088940241151319551086521)
            ·
              refine ⟨54066705180863489663314891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72088940241151319551086521 54066705180863489663314891)
              ·
                refine ⟨81100057771295234494972337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54066705180863489663314891 81100057771295234494972337)
                ·
                  refine ⟨60825043328471425871229253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81100057771295234494972337 60825043328471425871229253)
                  ·
                    refine ⟨11404695624088392350855485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60825043328471425871229253 11404695624088392350855485)
                    ·
                      refine ⟨4276760859033147131570807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404695624088392350855485 4276760859033147131570807)
                      ·
                        rfl

theorem cell23_8328962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_8328962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328962 prefixEnd_8328962 := by exact prefixLift 8328962
  have htrace : WordTrace (prefixWord ++ tailWord_8328962) baseStart_8328962 baseEnd_8328962 := by
    simpa [prefixWord, tailWord_8328962, baseEnd_8328962] using wordTrace_append hprefix tailTrace_8328962
  have hstable : (prefixWord ++ tailWord_8328962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328962).length < 2 ^ (prefixWord ++ tailWord_8328962).sum := by decide
  have hdescent : baseEnd_8328962 < baseStart_8328962 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8328995 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 2, 5]
def baseStart_8328995 : Nat := 118140960795 + 8328995 * 2 ^ 59
def prefixEnd_8328995 : Nat := 4983230072969 + 3 ^ 40 * 8328995 * 2
def baseEnd_8328995 : Nat := 1425592601298248500819385

theorem tailTrace_8328995 : CollatzResearch.WordTrace tailWord_8328995 prefixEnd_8328995 1425592601298248500819385 := by
  unfold tailWord_8328995
  simp only [CollatzResearch.WordTrace]
  refine ⟨303783404460481068941764439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202522269640320712627842959 303783404460481068941764439)
  ·
    refine ⟨455675106690721603412646659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303783404460481068941764439 455675106690721603412646659)
    ·
      refine ⟨683512660036082405118969989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455675106690721603412646659 683512660036082405118969989)
      ·
        refine ⟨128158623756765450959806873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 683512660036082405118969989 128158623756765450959806873)
        ·
          refine ⟨96118967817574088219855155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128158623756765450959806873 96118967817574088219855155)
          ·
            refine ⟨144178451726361132329782733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96118967817574088219855155 144178451726361132329782733)
            ·
              refine ⟨54066919397385424623668525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144178451726361132329782733 54066919397385424623668525)
              ·
                refine ⟨20275094774019534233875697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54066919397385424623668525 20275094774019534233875697)
                ·
                  refine ⟨15206321080514650675406773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20275094774019534233875697 15206321080514650675406773)
                  ·
                    refine ⟨1425592601298248500819385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15206321080514650675406773 1425592601298248500819385)
                    ·
                      rfl

theorem cell23_8328995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 5].length) (baseStart_8328995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8328995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8328995 prefixEnd_8328995 := by exact prefixLift 8328995
  have htrace : WordTrace (prefixWord ++ tailWord_8328995) baseStart_8328995 baseEnd_8328995 := by
    simpa [prefixWord, tailWord_8328995, baseEnd_8328995] using wordTrace_append hprefix tailTrace_8328995
  have hstable : (prefixWord ++ tailWord_8328995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8328995).length < 2 ^ (prefixWord ++ tailWord_8328995).sum := by decide
  have hdescent : baseEnd_8328995 < baseStart_8328995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8328995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329015 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_8329015 : Nat := 118140960795 + 8329015 * 2 ^ 59
def prefixEnd_8329015 : Nat := 4983230072969 + 3 ^ 40 * 8329015 * 2
def baseEnd_8329015 : Nat := 4276788073507835424208063

theorem tailTrace_8329015 : CollatzResearch.WordTrace tailWord_8329015 prefixEnd_8329015 4276788073507835424208063 := by
  unfold tailWord_8329015
  simp only [CollatzResearch.WordTrace]
  refine ⟨303784133920408612357492499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202522755946939074904994999 303784133920408612357492499)
  ·
    refine ⟨455676200880612918536238749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303784133920408612357492499 455676200880612918536238749)
    ·
      refine ⟨170878575330229844451089531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455676200880612918536238749 170878575330229844451089531)
      ·
        refine ⟨256317862995344766676634297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170878575330229844451089531 256317862995344766676634297)
        ·
          refine ⟨192238397246508575007475723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256317862995344766676634297 192238397246508575007475723)
          ·
            refine ⟨288357595869762862511213585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192238397246508575007475723 288357595869762862511213585)
            ·
              refine ⟨216268196902322146883410189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288357595869762862511213585 216268196902322146883410189)
              ·
                refine ⟨81100573838370805081278821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216268196902322146883410189 81100573838370805081278821)
                ·
                  refine ⟨15206357594694525952739779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81100573838370805081278821 15206357594694525952739779)
                  ·
                    refine ⟨22809536392041788929109669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15206357594694525952739779 22809536392041788929109669)
                    ·
                      refine ⟨4276788073507835424208063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22809536392041788929109669 4276788073507835424208063)
                      ·
                        rfl

theorem cell23_8329015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_8329015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329015 prefixEnd_8329015 := by exact prefixLift 8329015
  have htrace : WordTrace (prefixWord ++ tailWord_8329015) baseStart_8329015 baseEnd_8329015 := by
    simpa [prefixWord, tailWord_8329015, baseEnd_8329015] using wordTrace_append hprefix tailTrace_8329015
  have hstable : (prefixWord ++ tailWord_8329015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329015).length < 2 ^ (prefixWord ++ tailWord_8329015).sum := by decide
  have hdescent : baseEnd_8329015 < baseStart_8329015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329022 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_8329022 : Nat := 118140960795 + 8329022 * 2 ^ 59
def prefixEnd_8329022 : Nat := 4983230072969 + 3 ^ 40 * 8329022 * 2
def baseEnd_8329022 : Nat := 4276791667872416896820531

theorem tailTrace_8329022 : CollatzResearch.WordTrace tailWord_8329022 prefixEnd_8329022 4276791667872416896820531 := by
  unfold tailWord_8329022
  simp only [CollatzResearch.WordTrace]
  refine ⟨37973048653922906569124665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202522926154255501701998213 37973048653922906569124665)
  ·
    refine ⟨28479786490442179926843499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37973048653922906569124665 28479786490442179926843499)
    ·
      refine ⟨42719679735663269890265249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28479786490442179926843499 42719679735663269890265249)
      ·
        refine ⟨32039759801747452417698937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42719679735663269890265249 32039759801747452417698937)
        ·
          refine ⟨24029819851310589313274203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32039759801747452417698937 24029819851310589313274203)
          ·
            refine ⟨36044729776965883969911305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24029819851310589313274203 36044729776965883969911305)
            ·
              refine ⟨27033547332724412977433479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36044729776965883969911305 27033547332724412977433479)
              ·
                refine ⟨40550320999086619466150219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27033547332724412977433479 40550320999086619466150219)
                ·
                  refine ⟨60825481498629929199225329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40550320999086619466150219 60825481498629929199225329)
                  ·
                    refine ⟨45619111123972446899418997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60825481498629929199225329 45619111123972446899418997)
                    ·
                      refine ⟨4276791667872416896820531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45619111123972446899418997 4276791667872416896820531)
                      ·
                        rfl

theorem cell23_8329022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_8329022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329022 prefixEnd_8329022 := by exact prefixLift 8329022
  have htrace : WordTrace (prefixWord ++ tailWord_8329022) baseStart_8329022 baseEnd_8329022 := by
    simpa [prefixWord, tailWord_8329022, baseEnd_8329022] using wordTrace_append hprefix tailTrace_8329022
  have hstable : (prefixWord ++ tailWord_8329022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329022).length < 2 ^ (prefixWord ++ tailWord_8329022).sum := by decide
  have hdescent : baseEnd_8329022 < baseStart_8329022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329032 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 1, 6, 2]
def baseStart_8329032 : Nat := 118140960795 + 8329032 * 2 ^ 59
def prefixEnd_8329032 : Nat := 4983230072969 + 3 ^ 40 * 8329032 * 2
def baseEnd_8329032 : Nat := 4276796802678961857695485

theorem tailTrace_8329032 : CollatzResearch.WordTrace tailWord_8329032 prefixEnd_8329032 4276796802678961857695485 := by
  unfold tailWord_8329032
  simp only [CollatzResearch.WordTrace]
  refine ⟨151892376980673512130430675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202523169307564682840574233 151892376980673512130430675)
  ·
    refine ⟨227838565471010268195646013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151892376980673512130430675 227838565471010268195646013)
    ·
      refine ⟨85439462051628850573367255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227838565471010268195646013 85439462051628850573367255)
      ·
        refine ⟨128159193077443275860050883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85439462051628850573367255 128159193077443275860050883)
        ·
          refine ⟨192238789616164913790076325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128159193077443275860050883 192238789616164913790076325)
          ·
            refine ⟨36044773053030921335639311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192238789616164913790076325 36044773053030921335639311)
            ·
              refine ⟨54067159579546382003458967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36044773053030921335639311 54067159579546382003458967)
              ·
                refine ⟨81100739369319573005188451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54067159579546382003458967 81100739369319573005188451)
                ·
                  refine ⟨121651109053979359507782677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81100739369319573005188451 121651109053979359507782677)
                  ·
                    refine ⟨5702395736905282476927313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121651109053979359507782677 5702395736905282476927313)
                    ·
                      refine ⟨4276796802678961857695485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702395736905282476927313 4276796802678961857695485)
                      ·
                        rfl

theorem cell23_8329032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_8329032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329032 prefixEnd_8329032 := by exact prefixLift 8329032
  have htrace : WordTrace (prefixWord ++ tailWord_8329032) baseStart_8329032 baseEnd_8329032 := by
    simpa [prefixWord, tailWord_8329032, baseEnd_8329032] using wordTrace_append hprefix tailTrace_8329032
  have hstable : (prefixWord ++ tailWord_8329032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329032).length < 2 ^ (prefixWord ++ tailWord_8329032).sum := by decide
  have hdescent : baseEnd_8329032 < baseStart_8329032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329042 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_8329042 : Nat := 118140960795 + 8329042 * 2 ^ 59
def prefixEnd_8329042 : Nat := 4983230072969 + 3 ^ 40 * 8329042 * 2
def baseEnd_8329042 : Nat := 1425600645828502272856813

theorem tailTrace_8329042 : CollatzResearch.WordTrace tailWord_8329042 prefixEnd_8329042 1425600645828502272856813 := by
  unfold tailWord_8329042
  simp only [CollatzResearch.WordTrace]
  refine ⟨75946279672827698992181345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202523412460873863979150253 75946279672827698992181345)
  ·
    refine ⟨56959709754620774244136009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75946279672827698992181345 56959709754620774244136009)
    ·
      refine ⟨42719782315965580683102007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56959709754620774244136009 42719782315965580683102007)
      ·
        refine ⟨64079673473948371024653011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42719782315965580683102007 64079673473948371024653011)
        ·
          refine ⟨96119510210922556536979517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64079673473948371024653011 96119510210922556536979517)
          ·
            refine ⟨36044816329095958701367319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96119510210922556536979517 36044816329095958701367319)
            ·
              refine ⟨54067224493643938052050979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36044816329095958701367319 54067224493643938052050979)
              ·
                refine ⟨81100836740465907078076469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54067224493643938052050979 81100836740465907078076469)
                ·
                  refine ⟨7603203444418678788569669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81100836740465907078076469 7603203444418678788569669)
                  ·
                    refine ⟨1425600645828502272856813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7603203444418678788569669 1425600645828502272856813)
                    ·
                      rfl

theorem cell23_8329042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_8329042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329042 prefixEnd_8329042 := by exact prefixLift 8329042
  have htrace : WordTrace (prefixWord ++ tailWord_8329042) baseStart_8329042 baseEnd_8329042 := by
    simpa [prefixWord, tailWord_8329042, baseEnd_8329042] using wordTrace_append hprefix tailTrace_8329042
  have hstable : (prefixWord ++ tailWord_8329042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329042).length < 2 ^ (prefixWord ++ tailWord_8329042).sum := by decide
  have hdescent : baseEnd_8329042 < baseStart_8329042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329065 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 3]
def baseStart_8329065 : Nat := 118140960795 + 8329065 * 2 ^ 59
def prefixEnd_8329065 : Nat := 4983230072969 + 3 ^ 40 * 8329065 * 2
def baseEnd_8329065 : Nat := 4276813747540560228582833

theorem tailTrace_8329065 : CollatzResearch.WordTrace tailWord_8329065 prefixEnd_8329065 4276813747540560228582833 := by
  unfold tailWord_8329065
  simp only [CollatzResearch.WordTrace]
  refine ⟨303785957570227470896812649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202523971713484980597875099 303785957570227470896812649)
  ·
    refine ⟨227839468177670603172609487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303785957570227470896812649 227839468177670603172609487)
    ·
      refine ⟨341759202266505904758914231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227839468177670603172609487 341759202266505904758914231)
      ·
        refine ⟨512638803399758857138371347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341759202266505904758914231 512638803399758857138371347)
        ·
          refine ⟨768958205099638285707557021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512638803399758857138371347 768958205099638285707557021)
          ·
            refine ⟨288359326912364357140333883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 768958205099638285707557021 288359326912364357140333883)
            ·
              refine ⟨432538990368546535710500825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288359326912364357140333883 432538990368546535710500825)
              ·
                refine ⟨324404242776409901782875619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432538990368546535710500825 324404242776409901782875619)
                ·
                  refine ⟨486606364164614852674313429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324404242776409901782875619 486606364164614852674313429)
                  ·
                    refine ⟨11404836660108160609554221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 486606364164614852674313429 11404836660108160609554221)
                    ·
                      refine ⟨4276813747540560228582833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404836660108160609554221 4276813747540560228582833)
                      ·
                        rfl

theorem cell23_8329065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_8329065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329065 prefixEnd_8329065 := by exact prefixLift 8329065
  have htrace : WordTrace (prefixWord ++ tailWord_8329065) baseStart_8329065 baseEnd_8329065 := by
    simpa [prefixWord, tailWord_8329065, baseEnd_8329065] using wordTrace_append hprefix tailTrace_8329065
  have hstable : (prefixWord ++ tailWord_8329065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329065).length < 2 ^ (prefixWord ++ tailWord_8329065).sum := by decide
  have hdescent : baseEnd_8329065 < baseStart_8329065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329109 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 2, 3, 2]
def baseStart_8329109 : Nat := 118140960795 + 8329109 * 2 ^ 59
def prefixEnd_8329109 : Nat := 4983230072969 + 3 ^ 40 * 8329109 * 2
def baseEnd_8329109 : Nat := 4276836340689358056432631

theorem tailTrace_8329109 : CollatzResearch.WordTrace tailWord_8329109 prefixEnd_8329109 4276836340689358056432631 := by
  unfold tailWord_8329109
  simp only [CollatzResearch.WordTrace]
  refine ⟨303787562382068066411414381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202525041588045377607609587 303787562382068066411414381)
  ·
    refine ⟨113920335893275524904280393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303787562382068066411414381 113920335893275524904280393)
    ·
      refine ⟨85440251919956643678210295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113920335893275524904280393 85440251919956643678210295)
      ·
        refine ⟨128160377879934965517315443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85440251919956643678210295 128160377879934965517315443)
        ·
          refine ⟨192240566819902448275973165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128160377879934965517315443 192240566819902448275973165)
          ·
            refine ⟨72090212557463418103489937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192240566819902448275973165 72090212557463418103489937)
            ·
              refine ⟨54067659418097563577617453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72090212557463418103489937 54067659418097563577617453)
              ·
                refine ⟨20275372281786586341606545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54067659418097563577617453 20275372281786586341606545)
                ·
                  refine ⟨15206529211339939756204909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20275372281786586341606545 15206529211339939756204909)
                  ·
                    refine ⟨5702448454252477408576841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15206529211339939756204909 5702448454252477408576841)
                    ·
                      refine ⟨4276836340689358056432631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702448454252477408576841 4276836340689358056432631)
                      ·
                        rfl

theorem cell23_8329109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_8329109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329109 prefixEnd_8329109 := by exact prefixLift 8329109
  have htrace : WordTrace (prefixWord ++ tailWord_8329109) baseStart_8329109 baseEnd_8329109 := by
    simpa [prefixWord, tailWord_8329109, baseEnd_8329109] using wordTrace_append hprefix tailTrace_8329109
  have hstable : (prefixWord ++ tailWord_8329109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329109).length < 2 ^ (prefixWord ++ tailWord_8329109).sum := by decide
  have hdescent : baseEnd_8329109 < baseStart_8329109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329135 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 6]
def baseStart_8329135 : Nat := 118140960795 + 8329135 * 2 ^ 59
def prefixEnd_8329135 : Nat := 4983230072969 + 3 ^ 40 * 8329135 * 2
def baseEnd_8329135 : Nat := 4276849691186374954707511

theorem tailTrace_8329135 : CollatzResearch.WordTrace tailWord_8329135 prefixEnd_8329135 4276849691186374954707511 := by
  unfold tailWord_8329135
  simp only [CollatzResearch.WordTrace]
  refine ⟨303788510679973872851860859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202525673786649248567907239 303788510679973872851860859)
  ·
    refine ⟨455682766019960809277791289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303788510679973872851860859 455682766019960809277791289)
    ·
      refine ⟨341762074514970606958343467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455682766019960809277791289 341762074514970606958343467)
      ·
        refine ⟨512643111772455910437515201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341762074514970606958343467 512643111772455910437515201)
        ·
          refine ⟨384482333829341932828136401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512643111772455910437515201 384482333829341932828136401)
          ·
            refine ⟨288361750372006449621102301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384482333829341932828136401 288361750372006449621102301)
            ·
              refine ⟨108135656389502418607913363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288361750372006449621102301 108135656389502418607913363)
              ·
                refine ⟨162203484584253627911870045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108135656389502418607913363 162203484584253627911870045)
                ·
                  refine ⟨60826306719095110466951267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162203484584253627911870045 60826306719095110466951267)
                  ·
                    refine ⟨91239460078642665700426901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60826306719095110466951267 91239460078642665700426901)
                    ·
                      refine ⟨4276849691186374954707511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91239460078642665700426901 4276849691186374954707511)
                      ·
                        rfl

theorem cell23_8329135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_8329135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329135 prefixEnd_8329135 := by exact prefixLift 8329135
  have htrace : WordTrace (prefixWord ++ tailWord_8329135) baseStart_8329135 baseEnd_8329135 := by
    simpa [prefixWord, tailWord_8329135, baseEnd_8329135] using wordTrace_append hprefix tailTrace_8329135
  have hstable : (prefixWord ++ tailWord_8329135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329135).length < 2 ^ (prefixWord ++ tailWord_8329135).sum := by decide
  have hdescent : baseEnd_8329135 < baseStart_8329135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329140 : List Nat := [2, 5, 2, 1, 3, 1, 2, 1, 6]
def baseStart_8329140 : Nat := 118140960795 + 8329140 * 2 ^ 59
def prefixEnd_8329140 : Nat := 4983230072969 + 3 ^ 40 * 8329140 * 2
def baseEnd_8329140 : Nat := 475205806509960826127221

theorem tailTrace_8329140 : CollatzResearch.WordTrace tailWord_8329140 prefixEnd_8329140 475205806509960826127221 := by
  unfold tailWord_8329140
  simp only [CollatzResearch.WordTrace]
  refine ⟨151894346522477879352896437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202525795363303839137195249 151894346522477879352896437)
  ·
    refine ⟨14240094986482301189334041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151894346522477879352896437 14240094986482301189334041)
    ·
      refine ⟨10680071239861725892000531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14240094986482301189334041 10680071239861725892000531)
      ·
        refine ⟨16020106859792588838000797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680071239861725892000531 16020106859792588838000797)
        ·
          refine ⟨6007540072422220814250299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16020106859792588838000797 6007540072422220814250299)
          ·
            refine ⟨9011310108633331221375449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007540072422220814250299 9011310108633331221375449)
            ·
              refine ⟨6758482581474998416031587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011310108633331221375449 6758482581474998416031587)
              ·
                refine ⟨10137723872212497624047381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758482581474998416031587 10137723872212497624047381)
                ·
                  refine ⟨475205806509960826127221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10137723872212497624047381 475205806509960826127221)
                  ·
                    rfl

theorem cell23_8329140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_8329140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329140 prefixEnd_8329140 := by exact prefixLift 8329140
  have htrace : WordTrace (prefixWord ++ tailWord_8329140) baseStart_8329140 baseEnd_8329140 := by
    simpa [prefixWord, tailWord_8329140, baseEnd_8329140] using wordTrace_append hprefix tailTrace_8329140
  have hstable : (prefixWord ++ tailWord_8329140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329140).length < 2 ^ (prefixWord ++ tailWord_8329140).sum := by decide
  have hdescent : baseEnd_8329140 < baseStart_8329140 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329152 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_8329152 : Nat := 118140960795 + 8329152 * 2 ^ 59
def prefixEnd_8329152 : Nat := 4983230072969 + 3 ^ 40 * 8329152 * 2
def baseEnd_8329152 : Nat := 4276858420357501388194933

theorem tailTrace_8329152 : CollatzResearch.WordTrace tailWord_8329152 prefixEnd_8329152 4276858420357501388194933 := by
  unfold tailWord_8329152
  simp only [CollatzResearch.WordTrace]
  refine ⟨151894565360456142377614855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202526087147274856503486473 151894565360456142377614855)
  ·
    refine ⟨227841848040684213566422283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151894565360456142377614855 227841848040684213566422283)
    ·
      refine ⟨341762772061026320349633425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227841848040684213566422283 341762772061026320349633425)
      ·
        refine ⟨256322079045769740262225069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341762772061026320349633425 256322079045769740262225069)
        ·
          refine ⟨96120779642163652598334401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256322079045769740262225069 96120779642163652598334401)
          ·
            refine ⟨72090584731622739448750801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96120779642163652598334401 72090584731622739448750801)
            ·
              refine ⟨54067938548717054586563101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72090584731622739448750801 54067938548717054586563101)
              ·
                refine ⟨20275476955768895469961163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54067938548717054586563101 20275476955768895469961163)
                ·
                  refine ⟨30413215433653343204941745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20275476955768895469961163 30413215433653343204941745)
                  ·
                    refine ⟨22809911575240007403706309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30413215433653343204941745 22809911575240007403706309)
                    ·
                      refine ⟨4276858420357501388194933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22809911575240007403706309 4276858420357501388194933)
                      ·
                        rfl

theorem cell23_8329152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_8329152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329152 prefixEnd_8329152 := by exact prefixLift 8329152
  have htrace : WordTrace (prefixWord ++ tailWord_8329152) baseStart_8329152 baseEnd_8329152 := by
    simpa [prefixWord, tailWord_8329152, baseEnd_8329152] using wordTrace_append hprefix tailTrace_8329152
  have hstable : (prefixWord ++ tailWord_8329152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329152).length < 2 ^ (prefixWord ++ tailWord_8329152).sum := by decide
  have hdescent : baseEnd_8329152 < baseStart_8329152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329176 : List Nat := [2, 1, 2, 2, 2, 2, 5, 1, 1, 2, 3]
def baseStart_8329176 : Nat := 118140960795 + 8329176 * 2 ^ 59
def prefixEnd_8329176 : Nat := 4983230072969 + 3 ^ 40 * 8329176 * 2
def baseEnd_8329176 : Nat := 4276870743893209294294823

theorem tailTrace_8329176 : CollatzResearch.WordTrace tailWord_8329176 prefixEnd_8329176 4276870743893209294294823 := by
  unfold tailWord_8329176
  simp only [CollatzResearch.WordTrace]
  refine ⟨151895003036412668427051691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202526670715216891236068921 151895003036412668427051691)
  ·
    refine ⟨227842504554619002640577537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151895003036412668427051691 227842504554619002640577537)
    ·
      refine ⟨170881878415964251980433153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227842504554619002640577537 170881878415964251980433153)
      ·
        refine ⟨128161408811973188985324865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170881878415964251980433153 128161408811973188985324865)
        ·
          refine ⟨96121056608979891738993649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128161408811973188985324865 96121056608979891738993649)
          ·
            refine ⟨72090792456734918804245237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96121056608979891738993649 72090792456734918804245237)
            ·
              refine ⟨6758511792818898637897991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72090792456734918804245237 6758511792818898637897991)
              ·
                refine ⟨10137767689228347956846987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758511792818898637897991 10137767689228347956846987)
                ·
                  refine ⟨15206651533842521935270481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10137767689228347956846987 15206651533842521935270481)
                  ·
                    refine ⟨11404988650381891451452861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15206651533842521935270481 11404988650381891451452861)
                    ·
                      refine ⟨4276870743893209294294823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11404988650381891451452861 4276870743893209294294823)
                      ·
                        rfl

theorem cell23_8329176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_8329176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329176 prefixEnd_8329176 := by exact prefixLift 8329176
  have htrace : WordTrace (prefixWord ++ tailWord_8329176) baseStart_8329176 baseEnd_8329176 := by
    simpa [prefixWord, tailWord_8329176, baseEnd_8329176] using wordTrace_append hprefix tailTrace_8329176
  have hstable : (prefixWord ++ tailWord_8329176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329176).length < 2 ^ (prefixWord ++ tailWord_8329176).sum := by decide
  have hdescent : baseEnd_8329176 < baseStart_8329176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329199 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 5, 3, 2]
def baseStart_8329199 : Nat := 118140960795 + 8329199 * 2 ^ 59
def prefixEnd_8329199 : Nat := 4983230072969 + 3 ^ 40 * 8329199 * 2
def baseEnd_8329199 : Nat := 4276882553948262704307217

theorem tailTrace_8329199 : CollatzResearch.WordTrace tailWord_8329199 prefixEnd_8329199 4276882553948262704307217 := by
  unfold tailWord_8329199
  simp only [CollatzResearch.WordTrace]
  refine ⟨303790844951742011782190651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202527229967828007854793767 303790844951742011782190651)
  ·
    refine ⟨455686267427613017673285977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303790844951742011782190651 455686267427613017673285977)
    ·
      refine ⟨341764700570709763254964483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455686267427613017673285977 341764700570709763254964483)
      ·
        refine ⟨512647050856064644882446725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341764700570709763254964483 512647050856064644882446725)
        ·
          refine ⟨96121322035512120915458761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512647050856064644882446725 96121322035512120915458761)
          ·
            refine ⟨72090991526634090686594071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96121322035512120915458761 72090991526634090686594071)
            ·
              refine ⟨108136487289951136029891107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72090991526634090686594071 108136487289951136029891107)
              ·
                refine ⟨162204730934926704044836661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108136487289951136029891107 162204730934926704044836661)
                ·
                  refine ⟨15206693525149378504203437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162204730934926704044836661 15206693525149378504203437)
                  ·
                    refine ⟨5702510071931016939076289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15206693525149378504203437 5702510071931016939076289)
                    ·
                      refine ⟨4276882553948262704307217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702510071931016939076289 4276882553948262704307217)
                      ·
                        rfl

theorem cell23_8329199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 3, 2].length) (baseStart_8329199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329199 prefixEnd_8329199 := by exact prefixLift 8329199
  have htrace : WordTrace (prefixWord ++ tailWord_8329199) baseStart_8329199 baseEnd_8329199 := by
    simpa [prefixWord, tailWord_8329199, baseEnd_8329199] using wordTrace_append hprefix tailTrace_8329199
  have hstable : (prefixWord ++ tailWord_8329199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329199).length < 2 ^ (prefixWord ++ tailWord_8329199).sum := by decide
  have hdescent : baseEnd_8329199 < baseStart_8329199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329212 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_8329212 : Nat := 118140960795 + 8329212 * 2 ^ 59
def prefixEnd_8329212 : Nat := 4983230072969 + 3 ^ 40 * 8329212 * 2
def baseEnd_8329212 : Nat := 4276889229196771153444657

theorem tailTrace_8329212 : CollatzResearch.WordTrace tailWord_8329212 prefixEnd_8329212 4276889229196771153444657 := by
  unfold tailWord_8329212
  simp only [CollatzResearch.WordTrace]
  refine ⟨151895659550347457501206945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202527546067129943334942593 151895659550347457501206945)
  ·
    refine ⟨113921744662760593125905209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151895659550347457501206945 113921744662760593125905209)
    ·
      refine ⟨85441308497070444844428907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113921744662760593125905209 85441308497070444844428907)
      ·
        refine ⟨128161962745605667266643361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85441308497070444844428907 128161962745605667266643361)
        ·
          refine ⟨96121472059204250449982521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128161962745605667266643361 96121472059204250449982521)
          ·
            refine ⟨72091104044403187837486891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96121472059204250449982521 72091104044403187837486891)
            ·
              refine ⟨108136656066604781756230337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72091104044403187837486891 108136656066604781756230337)
              ·
                refine ⟨81102492049953586317172753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108136656066604781756230337 81102492049953586317172753)
                ·
                  refine ⟨60826869037465189737879565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81102492049953586317172753 60826869037465189737879565)
                  ·
                    refine ⟨22810075889049446151704837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60826869037465189737879565 22810075889049446151704837)
                    ·
                      refine ⟨4276889229196771153444657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22810075889049446151704837 4276889229196771153444657)
                      ·
                        rfl

theorem cell23_8329212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_8329212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329212 prefixEnd_8329212 := by exact prefixLift 8329212
  have htrace : WordTrace (prefixWord ++ tailWord_8329212) baseStart_8329212 baseEnd_8329212 := by
    simpa [prefixWord, tailWord_8329212, baseEnd_8329212] using wordTrace_append hprefix tailTrace_8329212
  have hstable : (prefixWord ++ tailWord_8329212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329212).length < 2 ^ (prefixWord ++ tailWord_8329212).sum := by decide
  have hdescent : baseEnd_8329212 < baseStart_8329212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329232 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3]
def baseStart_8329232 : Nat := 118140960795 + 8329232 * 2 ^ 59
def prefixEnd_8329232 : Nat := 4983230072969 + 3 ^ 40 * 8329232 * 2
def baseEnd_8329232 : Nat := 4276899498809861075194565

theorem tailTrace_8329232 : CollatzResearch.WordTrace tailWord_8329232 prefixEnd_8329232 4276899498809861075194565 := by
  unfold tailWord_8329232
  simp only [CollatzResearch.WordTrace]
  refine ⟨151896024280311229209070975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202528032373748305612094633 151896024280311229209070975)
  ·
    refine ⟨227844036420466843813606463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151896024280311229209070975 227844036420466843813606463)
    ·
      refine ⟨341766054630700265720409695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227844036420466843813606463 341766054630700265720409695)
      ·
        refine ⟨512649081946050398580614543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341766054630700265720409695 512649081946050398580614543)
        ·
          refine ⟨768973622919075597870921815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512649081946050398580614543 768973622919075597870921815)
          ·
            refine ⟨1153460434378613396806382723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768973622919075597870921815 1153460434378613396806382723)
            ·
              refine ⟨1730190651567920095209574085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153460434378613396806382723 1730190651567920095209574085)
              ·
                refine ⟨324410747168985017851795141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1730190651567920095209574085 324410747168985017851795141)
                ·
                  refine ⟨60827015094184690847211589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324410747168985017851795141 60827015094184690847211589)
                  ·
                    refine ⟨11405065330159629533852173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60827015094184690847211589 11405065330159629533852173)
                    ·
                      refine ⟨4276899498809861075194565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11405065330159629533852173 4276899498809861075194565)
                      ·
                        rfl

theorem cell23_8329232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_8329232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329232 prefixEnd_8329232 := by exact prefixLift 8329232
  have htrace : WordTrace (prefixWord ++ tailWord_8329232) baseStart_8329232 baseEnd_8329232 := by
    simpa [prefixWord, tailWord_8329232, baseEnd_8329232] using wordTrace_append hprefix tailTrace_8329232
  have hstable : (prefixWord ++ tailWord_8329232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329232).length < 2 ^ (prefixWord ++ tailWord_8329232).sum := by decide
  have hdescent : baseEnd_8329232 < baseStart_8329232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329314 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_8329314 : Nat := 118140960795 + 8329314 * 2 ^ 59
def prefixEnd_8329314 : Nat := 4983230072969 + 3 ^ 40 * 8329314 * 2
def baseEnd_8329314 : Nat := 4276941604223529754369189

theorem tailTrace_8329314 : CollatzResearch.WordTrace tailWord_8329314 prefixEnd_8329314 4276941604223529754369189 := by
  unfold tailWord_8329314
  simp only [CollatzResearch.WordTrace]
  refine ⟨75948759836581346605656749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202530026230883590948417997 75948759836581346605656749)
  ·
    refine ⟨28480784938718004977121281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75948759836581346605656749 28480784938718004977121281)
    ·
      refine ⟨21360588704038503732840961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28480784938718004977121281 21360588704038503732840961)
      ·
        refine ⟨16020441528028877799630721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21360588704038503732840961 16020441528028877799630721)
        ·
          refine ⟨12015331146021658349723041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16020441528028877799630721 12015331146021658349723041)
          ·
            refine ⟨9011498359516243762292281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12015331146021658349723041 9011498359516243762292281)
            ·
              refine ⟨6758623769637182821719211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011498359516243762292281 6758623769637182821719211)
              ·
                refine ⟨10137935654455774232578817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6758623769637182821719211 10137935654455774232578817)
                ·
                  refine ⟨7603451740841830674434113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10137935654455774232578817 7603451740841830674434113)
                  ·
                    refine ⟨5702588805631373005825585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7603451740841830674434113 5702588805631373005825585)
                    ·
                      refine ⟨4276941604223529754369189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702588805631373005825585 4276941604223529754369189)
                      ·
                        rfl

theorem cell23_8329314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_8329314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329314 prefixEnd_8329314 := by exact prefixLift 8329314
  have htrace : WordTrace (prefixWord ++ tailWord_8329314) baseStart_8329314 baseEnd_8329314 := by
    simpa [prefixWord, tailWord_8329314, baseEnd_8329314] using wordTrace_append hprefix tailTrace_8329314
  have hstable : (prefixWord ++ tailWord_8329314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329314).length < 2 ^ (prefixWord ++ tailWord_8329314).sum := by decide
  have hdescent : baseEnd_8329314 < baseStart_8329314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329319 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_8329319 : Nat := 118140960795 + 8329319 * 2 ^ 59
def prefixEnd_8329319 : Nat := 4983230072969 + 3 ^ 40 * 8329319 * 2
def baseEnd_8329319 : Nat := 4276944171626802234806665

theorem tailTrace_8329319 : CollatzResearch.WordTrace tailWord_8329319 prefixEnd_8329319 4276944171626802234806665 := by
  unfold tailWord_8329319
  simp only [CollatzResearch.WordTrace]
  refine ⟨303795221711307272276559011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202530147807538181517706007 303795221711307272276559011)
  ·
    refine ⟨455692832566960908414838517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303795221711307272276559011 455692832566960908414838517)
    ·
      refine ⟨42721203053152585163891111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 455692832566960908414838517 42721203053152585163891111)
      ·
        refine ⟨64081804579728877745836667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42721203053152585163891111 64081804579728877745836667)
        ·
          refine ⟨96122706869593316618755001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64081804579728877745836667 96122706869593316618755001)
          ·
            refine ⟨72092030152194987464066251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96122706869593316618755001 72092030152194987464066251)
            ·
              refine ⟨108138045228292481196099377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72092030152194987464066251 108138045228292481196099377)
              ·
                refine ⟨81103533921219360897074533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108138045228292481196099377 81103533921219360897074533)
                ·
                  refine ⟨15206912610228630168201475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81103533921219360897074533 15206912610228630168201475)
                  ·
                    refine ⟨22810368915342945252302213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15206912610228630168201475 22810368915342945252302213)
                    ·
                      refine ⟨4276944171626802234806665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22810368915342945252302213 4276944171626802234806665)
                      ·
                        rfl

theorem cell23_8329319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_8329319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329319 prefixEnd_8329319 := by exact prefixLift 8329319
  have htrace : WordTrace (prefixWord ++ tailWord_8329319) baseStart_8329319 baseEnd_8329319 := by
    simpa [prefixWord, tailWord_8329319, baseEnd_8329319] using wordTrace_append hprefix tailTrace_8329319
  have hstable : (prefixWord ++ tailWord_8329319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329319).length < 2 ^ (prefixWord ++ tailWord_8329319).sum := by decide
  have hdescent : baseEnd_8329319 < baseStart_8329319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329329 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 5, 4]
def baseStart_8329329 : Nat := 118140960795 + 8329329 * 2 ^ 59
def prefixEnd_8329329 : Nat := 4983230072969 + 3 ^ 40 * 8329329 * 2
def baseEnd_8329329 : Nat := 1425649768811115731893873

theorem tailTrace_8329329 : CollatzResearch.WordTrace tailWord_8329329 prefixEnd_8329329 1425649768811115731893873 := by
  unfold tailWord_8329329
  simp only [CollatzResearch.WordTrace]
  refine ⟨303795586441271043984423041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202530390960847362656282027 303795586441271043984423041)
  ·
    refine ⟨227846689830953282988317281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303795586441271043984423041 227846689830953282988317281)
    ·
      refine ⟨170885017373214962241237961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227846689830953282988317281 170885017373214962241237961)
      ·
        refine ⟨128163763029911221680928471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170885017373214962241237961 128163763029911221680928471)
        ·
          refine ⟨192245644544866832521392707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128163763029911221680928471 192245644544866832521392707)
          ·
            refine ⟨288368466817300248782089061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192245644544866832521392707 288368466817300248782089061)
            ·
              refine ⟨54069087528243796646641699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288368466817300248782089061 54069087528243796646641699)
              ·
                refine ⟨81103631292365694969962549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54069087528243796646641699 81103631292365694969962549)
                ·
                  refine ⟨7603465433659283903433989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81103631292365694969962549 7603465433659283903433989)
                  ·
                    refine ⟨1425649768811115731893873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7603465433659283903433989 1425649768811115731893873)
                    ·
                      rfl

theorem cell23_8329329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_8329329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329329 prefixEnd_8329329 := by exact prefixLift 8329329
  have htrace : WordTrace (prefixWord ++ tailWord_8329329) baseStart_8329329 baseEnd_8329329 := by
    simpa [prefixWord, tailWord_8329329, baseEnd_8329329] using wordTrace_append hprefix tailTrace_8329329
  have hstable : (prefixWord ++ tailWord_8329329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329329).length < 2 ^ (prefixWord ++ tailWord_8329329).sum := by decide
  have hdescent : baseEnd_8329329 < baseStart_8329329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329390 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8329390 : Nat := 118140960795 + 8329390 * 2 ^ 59
def prefixEnd_8329390 : Nat := 4983230072969 + 3 ^ 40 * 8329390 * 2
def baseEnd_8329390 : Nat := 4276980628753271457018839

theorem tailTrace_8329390 : CollatzResearch.WordTrace tailWord_8329390 prefixEnd_8329390 4276980628753271457018839 := by
  unfold tailWord_8329390
  simp only [CollatzResearch.WordTrace]
  refine ⟨37974726411756256425299203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202531874196033367601595749 37974726411756256425299203)
  ·
    refine ⟨56962089617634384637948805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37974726411756256425299203 56962089617634384637948805)
    ·
      refine ⟨10680391803306447119615401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56962089617634384637948805 10680391803306447119615401)
      ·
        refine ⟨8010293852479835339711551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10680391803306447119615401 8010293852479835339711551)
        ·
          refine ⟨12015440778719753009567327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010293852479835339711551 12015440778719753009567327)
          ·
            refine ⟨18023161168079629514350991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12015440778719753009567327 18023161168079629514350991)
            ·
              refine ⟨27034741752119444271526487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18023161168079629514350991 27034741752119444271526487)
              ·
                refine ⟨40552112628179166407289731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27034741752119444271526487 40552112628179166407289731)
                ·
                  refine ⟨60828168942268749610934597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40552112628179166407289731 60828168942268749610934597)
                  ·
                    refine ⟨11405281676675390552050237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60828168942268749610934597 11405281676675390552050237)
                    ·
                      refine ⟨4276980628753271457018839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11405281676675390552050237 4276980628753271457018839)
                      ·
                        rfl

theorem cell23_8329390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8329390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329390 prefixEnd_8329390 := by exact prefixLift 8329390
  have htrace : WordTrace (prefixWord ++ tailWord_8329390) baseStart_8329390 baseEnd_8329390 := by
    simpa [prefixWord, tailWord_8329390, baseEnd_8329390] using wordTrace_append hprefix tailTrace_8329390
  have hstable : (prefixWord ++ tailWord_8329390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329390).length < 2 ^ (prefixWord ++ tailWord_8329390).sum := by decide
  have hdescent : baseEnd_8329390 < baseStart_8329390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329397 : List Nat := [1, 3, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_8329397 : Nat := 118140960795 + 8329397 * 2 ^ 59
def prefixEnd_8329397 : Nat := 4983230072969 + 3 ^ 40 * 8329397 * 2
def baseEnd_8329397 : Nat := 1425661407705950976543769

theorem tailTrace_8329397 : CollatzResearch.WordTrace tailWord_8329397 prefixEnd_8329397 1425661407705950976543769 := by
  unfold tailWord_8329397
  simp only [CollatzResearch.WordTrace]
  refine ⟨303798066605024691597898445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202532044403349794398598963 303798066605024691597898445)
  ·
    refine ⟨113924274976884259349211917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303798066605024691597898445 113924274976884259349211917)
    ·
      refine ⟨42721603116331597255954469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113924274976884259349211917 42721603116331597255954469)
      ·
        refine ⟨8010300584312174485491463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42721603116331597255954469 8010300584312174485491463)
        ·
          refine ⟨12015450876468261728237195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8010300584312174485491463 12015450876468261728237195)
          ·
            refine ⟨18023176314702392592355793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12015450876468261728237195 18023176314702392592355793)
            ·
              refine ⟨13517382236026794444266845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18023176314702392592355793 13517382236026794444266845)
              ·
                refine ⟨5069018338510047916600067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13517382236026794444266845 5069018338510047916600067)
                ·
                  refine ⟨7603527507765071874900101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069018338510047916600067 7603527507765071874900101)
                  ·
                    refine ⟨1425661407705950976543769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7603527507765071874900101 1425661407705950976543769)
                    ·
                      rfl

theorem cell23_8329397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_8329397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329397 prefixEnd_8329397 := by exact prefixLift 8329397
  have htrace : WordTrace (prefixWord ++ tailWord_8329397) baseStart_8329397 baseEnd_8329397 := by
    simpa [prefixWord, tailWord_8329397, baseEnd_8329397] using wordTrace_append hprefix tailTrace_8329397
  have hstable : (prefixWord ++ tailWord_8329397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329397).length < 2 ^ (prefixWord ++ tailWord_8329397).sum := by decide
  have hdescent : baseEnd_8329397 < baseStart_8329397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329410 : List Nat := [3, 5, 1, 1, 1, 1, 3, 2, 6]
def baseStart_8329410 : Nat := 118140960795 + 8329410 * 2 ^ 59
def prefixEnd_8329410 : Nat := 4983230072969 + 3 ^ 40 * 8329410 * 2
def baseEnd_8329410 : Nat := 475221210929595708752083

theorem tailTrace_8329410 : CollatzResearch.WordTrace tailWord_8329410 prefixEnd_8329410 475221210929595708752083 := by
  unfold tailWord_8329410
  simp only [CollatzResearch.WordTrace]
  refine ⟨75949635188494398704530421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202532360502651729878747789 75949635188494398704530421)
  ·
    refine ⟨7120278298921349878549727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75949635188494398704530421 7120278298921349878549727)
    ·
      refine ⟨10680417448382024817824591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7120278298921349878549727 10680417448382024817824591)
      ·
        refine ⟨16020626172573037226736887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680417448382024817824591 16020626172573037226736887)
        ·
          refine ⟨24030939258859555840105331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16020626172573037226736887 24030939258859555840105331)
          ·
            refine ⟨36046408888289333760157997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24030939258859555840105331 36046408888289333760157997)
            ·
              refine ⟨13517403333108500160059249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36046408888289333760157997 13517403333108500160059249)
              ·
                refine ⟨10138052499831375120044437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13517403333108500160059249 10138052499831375120044437)
                ·
                  refine ⟨475221210929595708752083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10138052499831375120044437 475221210929595708752083)
                  ·
                    rfl

theorem cell23_8329410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_8329410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329410 prefixEnd_8329410 := by exact prefixLift 8329410
  have htrace : WordTrace (prefixWord ++ tailWord_8329410) baseStart_8329410 baseEnd_8329410 := by
    simpa [prefixWord, tailWord_8329410, baseEnd_8329410] using wordTrace_append hprefix tailTrace_8329410
  have hstable : (prefixWord ++ tailWord_8329410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329410).length < 2 ^ (prefixWord ++ tailWord_8329410).sum := by decide
  have hdescent : baseEnd_8329410 < baseStart_8329410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329430 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_8329430 : Nat := 118140960795 + 8329430 * 2 ^ 59
def prefixEnd_8329430 : Nat := 4983230072969 + 3 ^ 40 * 8329430 * 2
def baseEnd_8329430 : Nat := 4277001167979451300518655

theorem tailTrace_8329430 : CollatzResearch.WordTrace tailWord_8329430 prefixEnd_8329430 4277001167979451300518655 := by
  unfold tailWord_8329430
  simp only [CollatzResearch.WordTrace]
  refine ⟨18987454388369071139615609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202532846809270092155899829 18987454388369071139615609)
  ·
    refine ⟨14240590791276803354711707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18987454388369071139615609 14240590791276803354711707)
    ·
      refine ⟨21360886186915205032067561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14240590791276803354711707 21360886186915205032067561)
      ·
        refine ⟨16020664640186403774050671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21360886186915205032067561 16020664640186403774050671)
        ·
          refine ⟨24030996960279605661076007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16020664640186403774050671 24030996960279605661076007)
          ·
            refine ⟨36046495440419408491614011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24030996960279605661076007 36046495440419408491614011)
            ·
              refine ⟨54069743160629112737421017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36046495440419408491614011 54069743160629112737421017)
              ·
                refine ⟨40552307370471834553065763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54069743160629112737421017 40552307370471834553065763)
                ·
                  refine ⟨60828461055707751829598645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40552307370471834553065763 60828461055707751829598645)
                  ·
                    refine ⟨5702668223972601734024873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60828461055707751829598645 5702668223972601734024873)
                    ·
                      refine ⟨4277001167979451300518655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702668223972601734024873 4277001167979451300518655)
                      ·
                        rfl

theorem cell23_8329430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_8329430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329430 prefixEnd_8329430 := by exact prefixLift 8329430
  have htrace : WordTrace (prefixWord ++ tailWord_8329430) baseStart_8329430 baseEnd_8329430 := by
    simpa [prefixWord, tailWord_8329430, baseEnd_8329430] using wordTrace_append hprefix tailTrace_8329430
  have hstable : (prefixWord ++ tailWord_8329430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329430).length < 2 ^ (prefixWord ++ tailWord_8329430).sum := by decide
  have hdescent : baseEnd_8329430 < baseStart_8329430 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329556 : List Nat := [2, 4, 1, 1, 2, 2, 1, 1, 9]
def baseStart_8329556 : Nat := 118140960795 + 8329556 * 2 ^ 59
def prefixEnd_8329556 : Nat := 4983230072969 + 3 ^ 40 * 8329556 * 2
def baseEnd_8329556 : Nat := 475229540726879756393675

theorem tailTrace_8329556 : CollatzResearch.WordTrace tailWord_8329556 prefixEnd_8329556 475229540726879756393675 := by
  unfold tailWord_8329556
  simp only [CollatzResearch.WordTrace]
  refine ⟨151901932905724330876468261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202535910540965774501957681 151901932905724330876468261)
  ·
    refine ⟨28481612419823312039337799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151901932905724330876468261 28481612419823312039337799)
    ·
      refine ⟨42722418629734968059006699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28481612419823312039337799 42722418629734968059006699)
      ·
        refine ⟨64083627944602452088510049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42722418629734968059006699 64083627944602452088510049)
        ·
          refine ⟨48062720958451839066382537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64083627944602452088510049 48062720958451839066382537)
          ·
            refine ⟨36047040718838879299786903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48062720958451839066382537 36047040718838879299786903)
            ·
              refine ⟨54070561078258318949680355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36047040718838879299786903 54070561078258318949680355)
              ·
                refine ⟨81105841617387478424520533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54070561078258318949680355 81105841617387478424520533)
                ·
                  refine ⟨475229540726879756393675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81105841617387478424520533 475229540726879756393675)
                  ·
                    rfl

theorem cell23_8329556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_8329556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329556 prefixEnd_8329556 := by exact prefixLift 8329556
  have htrace : WordTrace (prefixWord ++ tailWord_8329556) baseStart_8329556 baseEnd_8329556 := by
    simpa [prefixWord, tailWord_8329556, baseEnd_8329556] using wordTrace_append hprefix tailTrace_8329556
  have hstable : (prefixWord ++ tailWord_8329556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329556).length < 2 ^ (prefixWord ++ tailWord_8329556).sum := by decide
  have hdescent : baseEnd_8329556 < baseStart_8329556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329573 : List Nat := [1, 3, 1, 3, 1, 3, 1, 5, 5]
def baseStart_8329573 : Nat := 118140960795 + 8329573 * 2 ^ 59
def prefixEnd_8329573 : Nat := 4983230072969 + 3 ^ 40 * 8329573 * 2
def baseEnd_8329573 : Nat := 475230510634782693447833

theorem tailTrace_8329573 : CollatzResearch.WordTrace tailWord_8329573 prefixEnd_8329573 475230510634782693447833 := by
  unfold tailWord_8329573
  simp only [CollatzResearch.WordTrace]
  refine ⟨303804485852387073656305373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202536323901591382437536915 303804485852387073656305373)
  ·
    refine ⟨113926682194645152621114515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303804485852387073656305373 113926682194645152621114515)
    ·
      refine ⟨170890023291967728931671773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113926682194645152621114515 170890023291967728931671773)
      ·
        refine ⟨64083758734487898349376915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170890023291967728931671773 64083758734487898349376915)
        ·
          refine ⟨96125638101731847524065373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64083758734487898349376915 96125638101731847524065373)
          ·
            refine ⟨36047114288149442821524515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96125638101731847524065373 36047114288149442821524515)
            ·
              refine ⟨54070671432224164232286773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36047114288149442821524515 54070671432224164232286773)
              ·
                refine ⟨5069125446771015396776885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54070671432224164232286773 5069125446771015396776885)
                ·
                  refine ⟨475230510634782693447833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5069125446771015396776885 475230510634782693447833)
                  ·
                    rfl

theorem cell23_8329573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_8329573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329573 prefixEnd_8329573 := by exact prefixLift 8329573
  have htrace : WordTrace (prefixWord ++ tailWord_8329573) baseStart_8329573 baseEnd_8329573 := by
    simpa [prefixWord, tailWord_8329573, baseEnd_8329573] using wordTrace_append hprefix tailTrace_8329573
  have hstable : (prefixWord ++ tailWord_8329573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329573).length < 2 ^ (prefixWord ++ tailWord_8329573).sum := by decide
  have hdescent : baseEnd_8329573 < baseStart_8329573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329623 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 1, 6, 2]
def baseStart_8329623 : Nat := 118140960795 + 8329623 * 2 ^ 59
def prefixEnd_8329623 : Nat := 4983230072969 + 3 ^ 40 * 8329623 * 2
def baseEnd_8329623 : Nat := 4277100269745769045405267

theorem tailTrace_8329623 : CollatzResearch.WordTrace tailWord_8329623 prefixEnd_8329623 4277100269745769045405267 := by
  unfold tailWord_8329623
  simp only [CollatzResearch.WordTrace]
  refine ⟨303806309502205932195625523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202537539668137288130417015 303806309502205932195625523)
  ·
    refine ⟨455709464253308898293438285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303806309502205932195625523 455709464253308898293438285)
    ·
      refine ⟨170891049094990836860039357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455709464253308898293438285 170891049094990836860039357)
      ·
        refine ⟨64084143410621563822514759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170891049094990836860039357 64084143410621563822514759)
        ·
          refine ⟨96126215115932345733772139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64084143410621563822514759 96126215115932345733772139)
          ·
            refine ⟨144189322673898518600658209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96126215115932345733772139 144189322673898518600658209)
            ·
              refine ⟨108141992005423888950493657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144189322673898518600658209 108141992005423888950493657)
              ·
                refine ⟨81106494004067916712870243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108141992005423888950493657 81106494004067916712870243)
                ·
                  refine ⟨121659741006101875069305365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81106494004067916712870243 121659741006101875069305365)
                  ·
                    refine ⟨5702800359661025393873689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121659741006101875069305365 5702800359661025393873689)
                    ·
                      refine ⟨4277100269745769045405267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702800359661025393873689 4277100269745769045405267)
                      ·
                        rfl

theorem cell23_8329623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_8329623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329623 prefixEnd_8329623 := by exact prefixLift 8329623
  have htrace : WordTrace (prefixWord ++ tailWord_8329623) baseStart_8329623 baseEnd_8329623 := by
    simpa [prefixWord, tailWord_8329623, baseEnd_8329623] using wordTrace_append hprefix tailTrace_8329623
  have hstable : (prefixWord ++ tailWord_8329623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329623).length < 2 ^ (prefixWord ++ tailWord_8329623).sum := by decide
  have hdescent : baseEnd_8329623 < baseStart_8329623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329636 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_8329636 : Nat := 118140960795 + 8329636 * 2 ^ 59
def prefixEnd_8329636 : Nat := 4983230072969 + 3 ^ 40 * 8329636 * 2
def baseEnd_8329636 : Nat := 4277106944994277494542707

theorem tailTrace_8329636 : CollatzResearch.WordTrace tailWord_8329636 prefixEnd_8329636 4277106944994277494542707 := by
  unfold tailWord_8329636
  simp only [CollatzResearch.WordTrace]
  refine ⟨151903391825579417707924381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202537855767439223610565841 151903391825579417707924381)
  ·
    refine ⟨56963771934592281640471643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151903391825579417707924381 56963771934592281640471643)
    ·
      refine ⟨85445657901888422460707465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56963771934592281640471643 85445657901888422460707465)
      ·
        refine ⟨64084243426416316845530599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85445657901888422460707465 64084243426416316845530599)
        ·
          refine ⟨96126365139624475268295899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64084243426416316845530599 96126365139624475268295899)
          ·
            refine ⟨144189547709436712902443849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96126365139624475268295899 144189547709436712902443849)
            ·
              refine ⟨108142160782077534676832887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144189547709436712902443849 108142160782077534676832887)
              ·
                refine ⟨162213241173116302015249331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108142160782077534676832887 162213241173116302015249331)
                ·
                  refine ⟨243319861759674453022873997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162213241173116302015249331 243319861759674453022873997)
                  ·
                    refine ⟨91244948159877919883577749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243319861759674453022873997 91244948159877919883577749)
                    ·
                      refine ⟨4277106944994277494542707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91244948159877919883577749 4277106944994277494542707)
                      ·
                        rfl

theorem cell23_8329636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_8329636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329636 prefixEnd_8329636 := by exact prefixLift 8329636
  have htrace : WordTrace (prefixWord ++ tailWord_8329636) baseStart_8329636 baseEnd_8329636 := by
    simpa [prefixWord, tailWord_8329636, baseEnd_8329636] using wordTrace_append hprefix tailTrace_8329636
  have hstable : (prefixWord ++ tailWord_8329636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329636).length < 2 ^ (prefixWord ++ tailWord_8329636).sum := by decide
  have hdescent : baseEnd_8329636 < baseStart_8329636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329640 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_8329640 : Nat := 118140960795 + 8329640 * 2 ^ 59
def prefixEnd_8329640 : Nat := 4983230072969 + 3 ^ 40 * 8329640 * 2
def baseEnd_8329640 : Nat := 4277108998916895478892689

theorem tailTrace_8329640 : CollatzResearch.WordTrace tailWord_8329640 prefixEnd_8329640 4277108998916895478892689 := by
  unfold tailWord_8329640
  simp only [CollatzResearch.WordTrace]
  refine ⟨151903464771572172049497187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202537953028762896065996249 151903464771572172049497187)
  ·
    refine ⟨227855197157358258074245781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151903464771572172049497187 227855197157358258074245781)
    ·
      refine ⟨10680712366751168347230271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227855197157358258074245781 10680712366751168347230271)
      ·
        refine ⟨16021068550126752520845407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10680712366751168347230271 16021068550126752520845407)
        ·
          refine ⟨24031602825190128781268111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16021068550126752520845407 24031602825190128781268111)
          ·
            refine ⟨36047404237785193171902167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24031602825190128781268111 36047404237785193171902167)
            ·
              refine ⟨54071106356677789757853251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36047404237785193171902167 54071106356677789757853251)
              ·
                refine ⟨81106659535016684636779877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54071106356677789757853251 81106659535016684636779877)
                ·
                  refine ⟨15207498662815628369396227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81106659535016684636779877 15207498662815628369396227)
                  ·
                    refine ⟨22811247994223442554094341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15207498662815628369396227 22811247994223442554094341)
                    ·
                      refine ⟨4277108998916895478892689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22811247994223442554094341 4277108998916895478892689)
                      ·
                        rfl

theorem cell23_8329640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_8329640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329640 prefixEnd_8329640 := by exact prefixLift 8329640
  have htrace : WordTrace (prefixWord ++ tailWord_8329640) baseStart_8329640 baseEnd_8329640 := by
    simpa [prefixWord, tailWord_8329640, baseEnd_8329640] using wordTrace_append hprefix tailTrace_8329640
  have hstable : (prefixWord ++ tailWord_8329640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329640).length < 2 ^ (prefixWord ++ tailWord_8329640).sum := by decide
  have hdescent : baseEnd_8329640 < baseStart_8329640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329683 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 7, 5, 2]
def baseStart_8329683 : Nat := 118140960795 + 8329683 * 2 ^ 59
def prefixEnd_8329683 : Nat := 4983230072969 + 3 ^ 40 * 8329683 * 2
def baseEnd_8329683 : Nat := 4277131078585038810654991

theorem tailTrace_8329683 : CollatzResearch.WordTrace tailWord_8329683 prefixEnd_8329683 4277131078585038810654991 := by
  unfold tailWord_8329683
  simp only [CollatzResearch.WordTrace]
  refine ⟨303808497881988562442809703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202538998587992374961873135 303808497881988562442809703)
  ·
    refine ⟨455712746822982843664214555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303808497881988562442809703 455712746822982843664214555)
    ·
      refine ⟨683569120234474265496321833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455712746822982843664214555 683569120234474265496321833)
      ·
        refine ⟨512676840175855699122241375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683569120234474265496321833 512676840175855699122241375)
        ·
          refine ⟨769015260263783548683362063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512676840175855699122241375 769015260263783548683362063)
          ·
            refine ⟨1153522890395675323025043095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769015260263783548683362063 1153522890395675323025043095)
            ·
              refine ⟨1730284335593512984537564643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153522890395675323025043095 1730284335593512984537564643)
              ·
                refine ⟨2595426503390269476806346965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730284335593512984537564643 2595426503390269476806346965)
                ·
                  refine ⟨60830308673209440862648757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2595426503390269476806346965 60830308673209440862648757)
                  ·
                    refine ⟨5702841438113385080873321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60830308673209440862648757 5702841438113385080873321)
                    ·
                      refine ⟨4277131078585038810654991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702841438113385080873321 4277131078585038810654991)
                      ·
                        rfl

theorem cell23_8329683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5, 2].length) (baseStart_8329683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329683 prefixEnd_8329683 := by exact prefixLift 8329683
  have htrace : WordTrace (prefixWord ++ tailWord_8329683) baseStart_8329683 baseEnd_8329683 := by
    simpa [prefixWord, tailWord_8329683, baseEnd_8329683] using wordTrace_append hprefix tailTrace_8329683
  have hstable : (prefixWord ++ tailWord_8329683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329683).length < 2 ^ (prefixWord ++ tailWord_8329683).sum := by decide
  have hdescent : baseEnd_8329683 < baseStart_8329683 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329701 : List Nat := [1, 3, 1, 5, 2, 2, 2, 2, 1, 4]
def baseStart_8329701 : Nat := 118140960795 + 8329701 * 2 ^ 59
def prefixEnd_8329701 : Nat := 4983230072969 + 3 ^ 40 * 8329701 * 2
def baseEnd_8329701 : Nat := 1425713440412273246743303

theorem tailTrace_8329701 : CollatzResearch.WordTrace tailWord_8329701 prefixEnd_8329701 1425713440412273246743303 := by
  unfold tailWord_8329701
  simp only [CollatzResearch.WordTrace]
  refine ⟨303809154395923351516964957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202539436263948901011309971 303809154395923351516964957)
  ·
    refine ⟨113928432898471256818861859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303809154395923351516964957 113928432898471256818861859)
    ·
      refine ⟨170892649347706885228292789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113928432898471256818861859 170892649347706885228292789)
      ·
        refine ⟨16021185876347520490152449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170892649347706885228292789 16021185876347520490152449)
        ·
          refine ⟨12015889407260640367614337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16021185876347520490152449 12015889407260640367614337)
          ·
            refine ⟨9011917055445480275710753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12015889407260640367614337 9011917055445480275710753)
            ·
              refine ⟨6758937791584110206783065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9011917055445480275710753 6758937791584110206783065)
              ·
                refine ⟨5069203343688082655087299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6758937791584110206783065 5069203343688082655087299)
                ·
                  refine ⟨7603805015532123982630949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069203343688082655087299 7603805015532123982630949)
                  ·
                    refine ⟨1425713440412273246743303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7603805015532123982630949 1425713440412273246743303)
                    ·
                      rfl

theorem cell23_8329701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 1, 4].length) (baseStart_8329701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329701 prefixEnd_8329701 := by exact prefixLift 8329701
  have htrace : WordTrace (prefixWord ++ tailWord_8329701) baseStart_8329701 baseEnd_8329701 := by
    simpa [prefixWord, tailWord_8329701, baseEnd_8329701] using wordTrace_append hprefix tailTrace_8329701
  have hstable : (prefixWord ++ tailWord_8329701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329701).length < 2 ^ (prefixWord ++ tailWord_8329701).sum := by decide
  have hdescent : baseEnd_8329701 < baseStart_8329701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329707 : List Nat := [1, 1, 1, 1, 2, 3, 5, 4, 1, 1, 3]
def baseStart_8329707 : Nat := 118140960795 + 8329707 * 2 ^ 59
def prefixEnd_8329707 : Nat := 4983230072969 + 3 ^ 40 * 8329707 * 2
def baseEnd_8329707 : Nat := 4277143402120746716754881

theorem tailTrace_8329707 : CollatzResearch.WordTrace tailWord_8329707 prefixEnd_8329707 4277143402120746716754881 := by
  unfold tailWord_8329707
  simp only [CollatzResearch.WordTrace]
  refine ⟨303809373233901614541683375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202539582155934409694455583 303809373233901614541683375)
  ·
    refine ⟨455714059850852421812525063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303809373233901614541683375 455714059850852421812525063)
    ·
      refine ⟨683571089776278632718787595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455714059850852421812525063 683571089776278632718787595)
      ·
        refine ⟨1025356634664417949078181393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683571089776278632718787595 1025356634664417949078181393)
        ·
          refine ⟨769017475998313461808636045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1025356634664417949078181393 769017475998313461808636045)
          ·
            refine ⟨288381553499367548178238517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 769017475998313461808636045 288381553499367548178238517)
            ·
              refine ⟨27035770640565707641709861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288381553499367548178238517 27035770640565707641709861)
              ·
                refine ⟨5069206995106070182820599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27035770640565707641709861 5069206995106070182820599)
                ·
                  refine ⟨7603810492659105274230899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069206995106070182820599 7603810492659105274230899)
                  ·
                    refine ⟨11405715738988657911346349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7603810492659105274230899 11405715738988657911346349)
                    ·
                      refine ⟨4277143402120746716754881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11405715738988657911346349 4277143402120746716754881)
                      ·
                        rfl

theorem cell23_8329707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 4, 1, 1, 3].length) (baseStart_8329707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329707 prefixEnd_8329707 := by exact prefixLift 8329707
  have htrace : WordTrace (prefixWord ++ tailWord_8329707) baseStart_8329707 baseEnd_8329707 := by
    simpa [prefixWord, tailWord_8329707, baseEnd_8329707] using wordTrace_append hprefix tailTrace_8329707
  have hstable : (prefixWord ++ tailWord_8329707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329707).length < 2 ^ (prefixWord ++ tailWord_8329707).sum := by decide
  have hdescent : baseEnd_8329707 < baseStart_8329707 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329713 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_8329713 : Nat := 118140960795 + 8329713 * 2 ^ 59
def prefixEnd_8329713 : Nat := 4983230072969 + 3 ^ 40 * 8329713 * 2
def baseEnd_8329713 : Nat := 4277146483004673693279853

theorem tailTrace_8329713 : CollatzResearch.WordTrace tailWord_8329713 prefixEnd_8329713 4277146483004673693279853 := by
  unfold tailWord_8329713
  simp only [CollatzResearch.WordTrace]
  refine ⟨303809592071879877566401793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202539728047919918377601195 303809592071879877566401793)
  ·
    refine ⟨227857194053909908174801345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303809592071879877566401793 227857194053909908174801345)
    ·
      refine ⟨170892895540432431131101009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227857194053909908174801345 170892895540432431131101009)
      ·
        refine ⟨128169671655324323348325757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170892895540432431131101009 128169671655324323348325757)
        ·
          refine ⟨48063626870746621255622159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128169671655324323348325757 48063626870746621255622159)
          ·
            refine ⟨72095440306119931883433239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48063626870746621255622159 72095440306119931883433239)
            ·
              refine ⟨108143160459179897825149859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72095440306119931883433239 108143160459179897825149859)
              ·
                refine ⟨162214740688769846737724789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108143160459179897825149859 162214740688769846737724789)
                ·
                  refine ⟨15207631939572173131661699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162214740688769846737724789 15207631939572173131661699)
                  ·
                    refine ⟨22811447909358259697492549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15207631939572173131661699 22811447909358259697492549)
                    ·
                      refine ⟨4277146483004673693279853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22811447909358259697492549 4277146483004673693279853)
                      ·
                        rfl

theorem cell23_8329713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_8329713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329713 prefixEnd_8329713 := by exact prefixLift 8329713
  have htrace : WordTrace (prefixWord ++ tailWord_8329713) baseStart_8329713 baseEnd_8329713 := by
    simpa [prefixWord, tailWord_8329713, baseEnd_8329713] using wordTrace_append hprefix tailTrace_8329713
  have hstable : (prefixWord ++ tailWord_8329713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329713).length < 2 ^ (prefixWord ++ tailWord_8329713).sum := by decide
  have hdescent : baseEnd_8329713 < baseStart_8329713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329757 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_8329757 : Nat := 118140960795 + 8329757 * 2 ^ 59
def prefixEnd_8329757 : Nat := 4983230072969 + 3 ^ 40 * 8329757 * 2
def baseEnd_8329757 : Nat := 1425723025384490507043217

theorem tailTrace_8329757 : CollatzResearch.WordTrace tailWord_8329757 prefixEnd_8329757 1425723025384490507043217 := by
  unfold tailWord_8329757
  simp only [CollatzResearch.WordTrace]
  refine ⟨303811196883720473081003525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202540797922480315387335683 303811196883720473081003525)
  ·
    refine ⟨56964599415697588702688161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303811196883720473081003525 56964599415697588702688161)
    ·
      refine ⟨42723449561773191527016121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56964599415697588702688161 42723449561773191527016121)
      ·
        refine ⟨32042587171329893645262091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42723449561773191527016121 32042587171329893645262091)
        ·
          refine ⟨48063880756994840467893137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32042587171329893645262091 48063880756994840467893137)
          ·
            refine ⟨36047910567746130350919853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48063880756994840467893137 36047910567746130350919853)
            ·
              refine ⟨13517966462904798881594945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36047910567746130350919853 13517966462904798881594945)
              ·
                refine ⟨10138474847178599161196209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13517966462904798881594945 10138474847178599161196209)
                ·
                  refine ⟨7603856135383949370897157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10138474847178599161196209 7603856135383949370897157)
                  ·
                    refine ⟨1425723025384490507043217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7603856135383949370897157 1425723025384490507043217)
                    ·
                      rfl

theorem cell23_8329757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_8329757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329757 prefixEnd_8329757 := by exact prefixLift 8329757
  have htrace : WordTrace (prefixWord ++ tailWord_8329757) baseStart_8329757 baseEnd_8329757 := by
    simpa [prefixWord, tailWord_8329757, baseEnd_8329757] using wordTrace_append hprefix tailTrace_8329757
  have hstable : (prefixWord ++ tailWord_8329757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329757).length < 2 ^ (prefixWord ++ tailWord_8329757).sum := by decide
  have hdescent : baseEnd_8329757 < baseStart_8329757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329774 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_8329774 : Nat := 118140960795 + 8329774 * 2 ^ 59
def prefixEnd_8329774 : Nat := 4983230072969 + 3 ^ 40 * 8329774 * 2
def baseEnd_8329774 : Nat := 1425725935108199318205691

theorem tailTrace_8329774 : CollatzResearch.WordTrace tailWord_8329774 prefixEnd_8329774 1425725935108199318205691 := by
  unfold tailWord_8329774
  simp only [CollatzResearch.WordTrace]
  refine ⟨37976477115582360623046547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202541211283105923322914917 37976477115582360623046547)
  ·
    refine ⟨56964715673373540934569821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37976477115582360623046547 56964715673373540934569821)
    ·
      refine ⟨21361768377515077850463683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56964715673373540934569821 21361768377515077850463683)
      ·
        refine ⟨32042652566272616775695525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21361768377515077850463683 32042652566272616775695525)
        ·
          refine ⟨6007997356176115645442911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32042652566272616775695525 6007997356176115645442911)
          ·
            refine ⟨9011996034264173468164367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6007997356176115645442911 9011996034264173468164367)
            ·
              refine ⟨13517994051396260202246551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9011996034264173468164367 13517994051396260202246551)
              ·
                refine ⟨20276991077094390303369827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13517994051396260202246551 20276991077094390303369827)
                ·
                  refine ⟨30415486615641585455054741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20276991077094390303369827 30415486615641585455054741)
                  ·
                    refine ⟨1425725935108199318205691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30415486615641585455054741 1425725935108199318205691)
                    ·
                      rfl

theorem cell23_8329774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_8329774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329774 prefixEnd_8329774 := by exact prefixLift 8329774
  have htrace : WordTrace (prefixWord ++ tailWord_8329774) baseStart_8329774 baseEnd_8329774 := by
    simpa [prefixWord, tailWord_8329774, baseEnd_8329774] using wordTrace_append hprefix tailTrace_8329774
  have hstable : (prefixWord ++ tailWord_8329774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329774).length < 2 ^ (prefixWord ++ tailWord_8329774).sum := by decide
  have hdescent : baseEnd_8329774 < baseStart_8329774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329807 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 1, 3, 2]
def baseStart_8329807 : Nat := 118140960795 + 8329807 * 2 ^ 59
def prefixEnd_8329807 : Nat := 4983230072969 + 3 ^ 40 * 8329807 * 2
def baseEnd_8329807 : Nat := 4277194750186196325504421

theorem tailTrace_8329807 : CollatzResearch.WordTrace tailWord_8329807 prefixEnd_8329807 4277194750186196325504421 := by
  unfold tailWord_8329807
  simp only [CollatzResearch.WordTrace]
  refine ⟨303813020533539331620323675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202542013689026221080215783 303813020533539331620323675)
  ·
    refine ⟨455719530800308997430485513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303813020533539331620323675 455719530800308997430485513)
    ·
      refine ⟨341789648100231748072864135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455719530800308997430485513 341789648100231748072864135)
      ·
        refine ⟨512684472150347622109296203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341789648100231748072864135 512684472150347622109296203)
        ·
          refine ⟨769026708225521433163944305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512684472150347622109296203 769026708225521433163944305)
          ·
            refine ⟨576770031169141074872958229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769026708225521433163944305 576770031169141074872958229)
            ·
              refine ⟨27036095211053487884669917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 576770031169141074872958229 27036095211053487884669917)
              ·
                refine ⟨10138535704145057956751219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27036095211053487884669917 10138535704145057956751219)
                ·
                  refine ⟨15207803556217586935126829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10138535704145057956751219 15207803556217586935126829)
                  ·
                    refine ⟨5702926333581595100672561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15207803556217586935126829 5702926333581595100672561)
                    ·
                      refine ⟨4277194750186196325504421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5702926333581595100672561 4277194750186196325504421)
                      ·
                        rfl

theorem cell23_8329807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 3, 2].length) (baseStart_8329807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329807 prefixEnd_8329807 := by exact prefixLift 8329807
  have htrace : WordTrace (prefixWord ++ tailWord_8329807) baseStart_8329807 baseEnd_8329807 := by
    simpa [prefixWord, tailWord_8329807, baseEnd_8329807] using wordTrace_append hprefix tailTrace_8329807
  have hstable : (prefixWord ++ tailWord_8329807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329807).length < 2 ^ (prefixWord ++ tailWord_8329807).sum := by decide
  have hdescent : baseEnd_8329807 < baseStart_8329807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329813 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_8329813 : Nat := 118140960795 + 8329813 * 2 ^ 59
def prefixEnd_8329813 : Nat := 4983230072969 + 3 ^ 40 * 8329813 * 2
def baseEnd_8329813 : Nat := 1425732610356707767343131

theorem tailTrace_8329813 : CollatzResearch.WordTrace tailWord_8329813 prefixEnd_8329813 1425732610356707767343131 := by
  unfold tailWord_8329813
  simp only [CollatzResearch.WordTrace]
  refine ⟨303813239371517594645042093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202542159581011729763361395 303813239371517594645042093)
  ·
    refine ⟨113929964764319097991890785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303813239371517594645042093 113929964764319097991890785)
    ·
      refine ⟨85447473573239323493918089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113929964764319097991890785 85447473573239323493918089)
      ·
        refine ⟨64085605179929492620438567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85447473573239323493918089 64085605179929492620438567)
        ·
          refine ⟨96128407769894238930657851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64085605179929492620438567 96128407769894238930657851)
          ·
            refine ⟨144192611654841358395986777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96128407769894238930657851 144192611654841358395986777)
            ·
              refine ⟨108144458741131018796990083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144192611654841358395986777 108144458741131018796990083)
              ·
                refine ⟨162216688111696528195485125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108144458741131018796990083 162216688111696528195485125)
                ·
                  refine ⟨30415629020943099036653461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162216688111696528195485125 30415629020943099036653461)
                  ·
                    refine ⟨1425732610356707767343131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30415629020943099036653461 1425732610356707767343131)
                    ·
                      rfl

theorem cell23_8329813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_8329813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329813 prefixEnd_8329813 := by exact prefixLift 8329813
  have htrace : WordTrace (prefixWord ++ tailWord_8329813) baseStart_8329813 baseEnd_8329813 := by
    simpa [prefixWord, tailWord_8329813, baseEnd_8329813] using wordTrace_append hprefix tailTrace_8329813
  have hstable : (prefixWord ++ tailWord_8329813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329813).length < 2 ^ (prefixWord ++ tailWord_8329813).sum := by decide
  have hdescent : baseEnd_8329813 < baseStart_8329813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329833 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_8329833 : Nat := 118140960795 + 8329833 * 2 ^ 59
def prefixEnd_8329833 : Nat := 4983230072969 + 3 ^ 40 * 8329833 * 2
def baseEnd_8329833 : Nat := 4277208100683213223779301

theorem tailTrace_8329833 : CollatzResearch.WordTrace tailWord_8329833 prefixEnd_8329833 4277208100683213223779301 := by
  unfold tailWord_8329833
  simp only [CollatzResearch.WordTrace]
  refine ⟨303813968831445138060770153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202542645887630092040513435 303813968831445138060770153)
  ·
    refine ⟨227860476623583853545577615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303813968831445138060770153 227860476623583853545577615)
    ·
      refine ⟨341790714935375780318366423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227860476623583853545577615 341790714935375780318366423)
      ·
        refine ⟨512686072403063670477549635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341790714935375780318366423 512686072403063670477549635)
        ·
          refine ⟨769029108604595505716324453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512686072403063670477549635 769029108604595505716324453)
          ·
            refine ⟨144192957863361657321810835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 769029108604595505716324453 144192957863361657321810835)
            ·
              refine ⟨216289436795042485982716253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144192957863361657321810835 216289436795042485982716253)
              ·
                refine ⟨81108538798140932243518595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216289436795042485982716253 81108538798140932243518595)
                ·
                  refine ⟨121662808197211398365277893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81108538798140932243518595 121662808197211398365277893)
                  ·
                    refine ⟨22811776536977137193489605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121662808197211398365277893 22811776536977137193489605)
                    ·
                      refine ⟨4277208100683213223779301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22811776536977137193489605 4277208100683213223779301)
                      ·
                        rfl

theorem cell23_8329833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_8329833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329833 prefixEnd_8329833 := by exact prefixLift 8329833
  have htrace : WordTrace (prefixWord ++ tailWord_8329833) baseStart_8329833 baseEnd_8329833 := by
    simpa [prefixWord, tailWord_8329833, baseEnd_8329833] using wordTrace_append hprefix tailTrace_8329833
  have hstable : (prefixWord ++ tailWord_8329833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329833).length < 2 ^ (prefixWord ++ tailWord_8329833).sum := by decide
  have hdescent : baseEnd_8329833 < baseStart_8329833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329907 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 2, 5]
def baseStart_8329907 : Nat := 118140960795 + 8329907 * 2 ^ 59
def prefixEnd_8329907 : Nat := 4983230072969 + 3 ^ 40 * 8329907 * 2
def baseEnd_8329907 : Nat := 1425748699417215311417987

theorem tailTrace_8329907 : CollatzResearch.WordTrace tailWord_8329907 prefixEnd_8329907 1425748699417215311417987 := by
  unfold tailWord_8329907
  simp only [CollatzResearch.WordTrace]
  refine ⟨303816667833177048698963975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202544445222118032465975983 303816667833177048698963975)
  ·
    refine ⟨455725001749765573048445963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303816667833177048698963975 455725001749765573048445963)
    ·
      refine ⟨683587502624648359572668945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455725001749765573048445963 683587502624648359572668945)
      ·
        refine ⟨512690626968486269679501709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683587502624648359572668945 512690626968486269679501709)
        ·
          refine ⟨192258985113182351129813141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512690626968486269679501709 192258985113182351129813141)
          ·
            refine ⟨9012139927180422709209991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 192258985113182351129813141 9012139927180422709209991)
            ·
              refine ⟨13518209890770634063814987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012139927180422709209991 13518209890770634063814987)
              ·
                refine ⟨20277314836155951095722481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13518209890770634063814987 20277314836155951095722481)
                ·
                  refine ⟨15207986127116963321791861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20277314836155951095722481 15207986127116963321791861)
                  ·
                    refine ⟨1425748699417215311417987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15207986127116963321791861 1425748699417215311417987)
                    ·
                      rfl

theorem cell23_8329907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 5].length) (baseStart_8329907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329907 prefixEnd_8329907 := by exact prefixLift 8329907
  have htrace : WordTrace (prefixWord ++ tailWord_8329907) baseStart_8329907 baseEnd_8329907 := by
    simpa [prefixWord, tailWord_8329907, baseEnd_8329907] using wordTrace_append hprefix tailTrace_8329907
  have hstable : (prefixWord ++ tailWord_8329907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329907).length < 2 ^ (prefixWord ++ tailWord_8329907).sum := by decide
  have hdescent : baseEnd_8329907 < baseStart_8329907 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329937 : List Nat := [1, 2, 2, 1, 2, 3, 4, 1, 3, 4]
def baseStart_8329937 : Nat := 118140960795 + 8329937 * 2 ^ 59
def prefixEnd_8329937 : Nat := 4983230072969 + 3 ^ 40 * 8329937 * 2
def baseEnd_8329937 : Nat := 1425753834223760272292941

theorem tailTrace_8329937 : CollatzResearch.WordTrace tailWord_8329937 prefixEnd_8329937 1425753834223760272292941 := by
  unfold tailWord_8329937
  simp only [CollatzResearch.WordTrace]
  refine ⟨303817762023068363822556065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202545174682045575881704043 303817762023068363822556065)
  ·
    refine ⟨227863321517301272866917049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303817762023068363822556065 227863321517301272866917049)
    ·
      refine ⟨170897491137975954650187787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227863321517301272866917049 170897491137975954650187787)
      ·
        refine ⟨256346236706963931975281681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170897491137975954650187787 256346236706963931975281681)
        ·
          refine ⟨192259677530222948981461261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256346236706963931975281681 192259677530222948981461261)
          ·
            refine ⟨72097379073833605868047973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192259677530222948981461261 72097379073833605868047973)
            ·
              refine ⟨13518258576343801100258995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72097379073833605868047973 13518258576343801100258995)
              ·
                refine ⟨20277387864515701650388493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13518258576343801100258995 20277387864515701650388493)
                ·
                  refine ⟨7604020449193388118895685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20277387864515701650388493 7604020449193388118895685)
                  ·
                    refine ⟨1425753834223760272292941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7604020449193388118895685 1425753834223760272292941)
                    ·
                      rfl

theorem cell23_8329937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_8329937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329937 prefixEnd_8329937 := by exact prefixLift 8329937
  have htrace : WordTrace (prefixWord ++ tailWord_8329937) baseStart_8329937 baseEnd_8329937 := by
    simpa [prefixWord, tailWord_8329937, baseEnd_8329937] using wordTrace_append hprefix tailTrace_8329937
  have hstable : (prefixWord ++ tailWord_8329937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329937).length < 2 ^ (prefixWord ++ tailWord_8329937).sum := by decide
  have hdescent : baseEnd_8329937 < baseStart_8329937 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8329977 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 3]
def baseStart_8329977 : Nat := 118140960795 + 8329977 * 2 ^ 59
def prefixEnd_8329977 : Nat := 4983230072969 + 3 ^ 40 * 8329977 * 2
def baseEnd_8329977 : Nat := 4277282041897460660378639

theorem tailTrace_8329977 : CollatzResearch.WordTrace tailWord_8329977 prefixEnd_8329977 4277282041897460660378639 := by
  unfold tailWord_8329977
  simp only [CollatzResearch.WordTrace]
  refine ⟨303819220942923450654012185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202546147295282300436008123 303819220942923450654012185)
  ·
    refine ⟨227864415707192587990509139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303819220942923450654012185 227864415707192587990509139)
    ·
      refine ⟨341796623560788881985763709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227864415707192587990509139 341796623560788881985763709)
      ·
        refine ⟨128173733835295830744661391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341796623560788881985763709 128173733835295830744661391)
        ·
          refine ⟨192260600752943746116992087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128173733835295830744661391 192260600752943746116992087)
          ·
            refine ⟨288390901129415619175488131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192260600752943746116992087 288390901129415619175488131)
            ·
              refine ⟨432586351694123428763232197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288390901129415619175488131 432586351694123428763232197)
              ·
                refine ⟨81109940942648142893106037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432586351694123428763232197 81109940942648142893106037)
                ·
                  refine ⟨7604056963373263396228691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81109940942648142893106037 7604056963373263396228691)
                  ·
                    refine ⟨11406085445059895094343037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7604056963373263396228691 11406085445059895094343037)
                    ·
                      refine ⟨4277282041897460660378639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406085445059895094343037 4277282041897460660378639)
                      ·
                        rfl

theorem cell23_8329977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_8329977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8329977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8329977 prefixEnd_8329977 := by exact prefixLift 8329977
  have htrace : WordTrace (prefixWord ++ tailWord_8329977) baseStart_8329977 baseEnd_8329977 := by
    simpa [prefixWord, tailWord_8329977, baseEnd_8329977] using wordTrace_append hprefix tailTrace_8329977
  have hstable : (prefixWord ++ tailWord_8329977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8329977).length < 2 ^ (prefixWord ++ tailWord_8329977).sum := by decide
  have hdescent : baseEnd_8329977 < baseStart_8329977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8329977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330017 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_8330017 : Nat := 118140960795 + 8330017 * 2 ^ 59
def prefixEnd_8330017 : Nat := 4983230072969 + 3 ^ 40 * 8330017 * 2
def baseEnd_8330017 : Nat := 4277302581123640503878455

theorem tailTrace_8330017 : CollatzResearch.WordTrace tailWord_8330017 prefixEnd_8330017 4277302581123640503878455 := by
  unfold tailWord_8330017
  simp only [CollatzResearch.WordTrace]
  refine ⟨303820679862778537485468305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202547119908519024990312203 303820679862778537485468305)
  ·
    refine ⟨227865509897083903114101229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303820679862778537485468305 227865509897083903114101229)
    ·
      refine ⟨85449566211406463667787961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227865509897083903114101229 85449566211406463667787961)
      ·
        refine ⟨64087174658554847750840971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85449566211406463667787961 64087174658554847750840971)
        ·
          refine ⟨96130761987832271626261457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64087174658554847750840971 96130761987832271626261457)
          ·
            refine ⟨72098071490874203719696093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96130761987832271626261457 72098071490874203719696093)
            ·
              refine ⟨27036776809077826394886035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72098071490874203719696093 27036776809077826394886035)
              ·
                refine ⟨40555165213616739592329053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27036776809077826394886035 40555165213616739592329053)
                ·
                  refine ⟨15208186955106277347123395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40555165213616739592329053 15208186955106277347123395)
                  ·
                    refine ⟨22812280432659416020685093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15208186955106277347123395 22812280432659416020685093)
                    ·
                      refine ⟨4277302581123640503878455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22812280432659416020685093 4277302581123640503878455)
                      ·
                        rfl

theorem cell23_8330017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_8330017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330017 prefixEnd_8330017 := by exact prefixLift 8330017
  have htrace : WordTrace (prefixWord ++ tailWord_8330017) baseStart_8330017 baseEnd_8330017 := by
    simpa [prefixWord, tailWord_8330017, baseEnd_8330017] using wordTrace_append hprefix tailTrace_8330017
  have hstable : (prefixWord ++ tailWord_8330017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330017).length < 2 ^ (prefixWord ++ tailWord_8330017).sum := by decide
  have hdescent : baseEnd_8330017 < baseStart_8330017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330057 : List Nat := [1, 2, 1, 1, 2, 7, 1, 8]
def baseStart_8330057 : Nat := 118140960795 + 8330057 * 2 ^ 59
def prefixEnd_8330057 : Nat := 4983230072969 + 3 ^ 40 * 8330057 * 2
def baseEnd_8330057 : Nat := 158419374827771123976973

theorem tailTrace_8330057 : CollatzResearch.WordTrace tailWord_8330057 prefixEnd_8330057 158419374827771123976973 := by
  unfold tailWord_8330057
  simp only [CollatzResearch.WordTrace]
  refine ⟨303822138782633624316924425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202548092521755749544616283 303822138782633624316924425)
  ·
    refine ⟨227866604086975218237693319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303822138782633624316924425 227866604086975218237693319)
    ·
      refine ⟨341799906130462827356539979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227866604086975218237693319 341799906130462827356539979)
      ·
        refine ⟨512699859195694241034809969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341799906130462827356539979 512699859195694241034809969)
        ·
          refine ⟨384524894396770680776107477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512699859195694241034809969 384524894396770680776107477)
          ·
            refine ⟨9012302212424312830690019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 384524894396770680776107477 9012302212424312830690019)
            ·
              refine ⟨13518453318636469246035029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012302212424312830690019 13518453318636469246035029)
              ·
                refine ⟨158419374827771123976973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13518453318636469246035029 158419374827771123976973)
                ·
                  rfl

theorem cell23_8330057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 8].length) (baseStart_8330057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330057 prefixEnd_8330057 := by exact prefixLift 8330057
  have htrace : WordTrace (prefixWord ++ tailWord_8330057) baseStart_8330057 baseEnd_8330057 := by
    simpa [prefixWord, tailWord_8330057, baseEnd_8330057] using wordTrace_append hprefix tailTrace_8330057
  have hstable : (prefixWord ++ tailWord_8330057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330057).length < 2 ^ (prefixWord ++ tailWord_8330057).sum := by decide
  have hdescent : baseEnd_8330057 < baseStart_8330057 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330061 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_8330061 : Nat := 118140960795 + 8330061 * 2 ^ 59
def prefixEnd_8330061 : Nat := 4983230072969 + 3 ^ 40 * 8330061 * 2
def baseEnd_8330061 : Nat := 1425775058090812777242751

theorem tailTrace_8330061 : CollatzResearch.WordTrace tailWord_8330061 prefixEnd_8330061 1425775058090812777242751 := by
  unfold tailWord_8330061
  simp only [CollatzResearch.WordTrace]
  refine ⟨303822284674619133000070037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202548189783079422000046691 303822284674619133000070037)
  ·
    refine ⟨14241669594122771859378283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 303822284674619133000070037 14241669594122771859378283)
    ·
      refine ⟨21362504391184157789067425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14241669594122771859378283 21362504391184157789067425)
      ·
        refine ⟨16021878293388118341800569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21362504391184157789067425 16021878293388118341800569)
        ·
          refine ⟨12016408720041088756350427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16021878293388118341800569 12016408720041088756350427)
          ·
            refine ⟨18024613080061633134525641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12016408720041088756350427 18024613080061633134525641)
            ·
              refine ⟨13518459810046224850894231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18024613080061633134525641 13518459810046224850894231)
              ·
                refine ⟨20277689715069337276341347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13518459810046224850894231 20277689715069337276341347)
                ·
                  refine ⟨30416534572604005914512021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20277689715069337276341347 30416534572604005914512021)
                  ·
                    refine ⟨1425775058090812777242751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30416534572604005914512021 1425775058090812777242751)
                    ·
                      rfl

theorem cell23_8330061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_8330061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330061 prefixEnd_8330061 := by exact prefixLift 8330061
  have htrace : WordTrace (prefixWord ++ tailWord_8330061) baseStart_8330061 baseEnd_8330061 := by
    simpa [prefixWord, tailWord_8330061, baseEnd_8330061] using wordTrace_append hprefix tailTrace_8330061
  have hstable : (prefixWord ++ tailWord_8330061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330061).length < 2 ^ (prefixWord ++ tailWord_8330061).sum := by decide
  have hdescent : baseEnd_8330061 < baseStart_8330061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330068 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_8330068 : Nat := 118140960795 + 8330068 * 2 ^ 59
def prefixEnd_8330068 : Nat := 4983230072969 + 3 ^ 40 * 8330068 * 2
def baseEnd_8330068 : Nat := 4277328768637019804340721

theorem tailTrace_8330068 : CollatzResearch.WordTrace tailWord_8330068 prefixEnd_8330068 4277328768637019804340721 := by
  unfold tailWord_8330068
  simp only [CollatzResearch.WordTrace]
  refine ⟨151911269992796886597787429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202548359990395848797049905 151911269992796886597787429)
  ·
    refine ⟨28483363123649416237085143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151911269992796886597787429 28483363123649416237085143)
    ·
      refine ⟨42725044685474124355627715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28483363123649416237085143 42725044685474124355627715)
      ·
        refine ⟨64087567028211186533441573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42725044685474124355627715 64087567028211186533441573)
        ·
          refine ⟨12016418817789597475020295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64087567028211186533441573 12016418817789597475020295)
          ·
            refine ⟨18024628226684396212530443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12016418817789597475020295 18024628226684396212530443)
            ·
              refine ⟨27036942340026594318795665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18024628226684396212530443 27036942340026594318795665)
              ·
                refine ⟨20277706755019945739096749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27036942340026594318795665 20277706755019945739096749)
                ·
                  refine ⟨7604140033132479652161281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20277706755019945739096749 7604140033132479652161281)
                  ·
                    refine ⟨5703105024849359739120961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7604140033132479652161281 5703105024849359739120961)
                    ·
                      refine ⟨4277328768637019804340721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703105024849359739120961 4277328768637019804340721)
                      ·
                        rfl

theorem cell23_8330068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_8330068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330068 prefixEnd_8330068 := by exact prefixLift 8330068
  have htrace : WordTrace (prefixWord ++ tailWord_8330068) baseStart_8330068 baseEnd_8330068 := by
    simpa [prefixWord, tailWord_8330068, baseEnd_8330068] using wordTrace_append hprefix tailTrace_8330068
  have hstable : (prefixWord ++ tailWord_8330068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330068).length < 2 ^ (prefixWord ++ tailWord_8330068).sum := by decide
  have hdescent : baseEnd_8330068 < baseStart_8330068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330084 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_8330084 : Nat := 118140960795 + 8330084 * 2 ^ 59
def prefixEnd_8330084 : Nat := 4983230072969 + 3 ^ 40 * 8330084 * 2
def baseEnd_8330084 : Nat := 4277336984327491741740647

theorem tailTrace_8330084 : CollatzResearch.WordTrace tailWord_8330084 prefixEnd_8330084 4277336984327491741740647 := by
  unfold tailWord_8330084
  simp only [CollatzResearch.WordTrace]
  refine ⟨151911561776767903964078653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202548749035690538618771537 151911561776767903964078653)
  ·
    refine ⟨56966835666287963986529495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151911561776767903964078653 56966835666287963986529495)
    ·
      refine ⟨85450253499431945979794243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56966835666287963986529495 85450253499431945979794243)
      ·
        refine ⟨128175380249147918969691365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85450253499431945979794243 128175380249147918969691365)
        ·
          refine ⟨24032883796715234806817131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128175380249147918969691365 24032883796715234806817131)
          ·
            refine ⟨36049325695072852210225697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24032883796715234806817131 36049325695072852210225697)
            ·
              refine ⟨27036994271304639157669273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36049325695072852210225697 27036994271304639157669273)
              ·
                refine ⟨20277745703478479368251955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27036994271304639157669273 20277745703478479368251955)
                ·
                  refine ⟨30416618555217719052377933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20277745703478479368251955 30416618555217719052377933)
                  ·
                    refine ⟨11406231958206644644641725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30416618555217719052377933 11406231958206644644641725)
                    ·
                      refine ⟨4277336984327491741740647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406231958206644644641725 4277336984327491741740647)
                      ·
                        rfl

theorem cell23_8330084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_8330084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330084 prefixEnd_8330084 := by exact prefixLift 8330084
  have htrace : WordTrace (prefixWord ++ tailWord_8330084) baseStart_8330084 baseEnd_8330084 := by
    simpa [prefixWord, tailWord_8330084, baseEnd_8330084] using wordTrace_append hprefix tailTrace_8330084
  have hstable : (prefixWord ++ tailWord_8330084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330084).length < 2 ^ (prefixWord ++ tailWord_8330084).sum := by decide
  have hdescent : baseEnd_8330084 < baseStart_8330084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330088 : List Nat := [2, 1, 4, 2, 1, 4, 2, 1, 1, 2, 3]
def baseStart_8330088 : Nat := 118140960795 + 8330088 * 2 ^ 59
def prefixEnd_8330088 : Nat := 4983230072969 + 3 ^ 40 * 8330088 * 2
def baseEnd_8330088 : Nat := 4277339038250109726090629

theorem tailTrace_8330088 : CollatzResearch.WordTrace tailWord_8330088 prefixEnd_8330088 4277339038250109726090629 := by
  unfold tailWord_8330088
  simp only [CollatzResearch.WordTrace]
  refine ⟨151911634722760658305651459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202548846297014211074201945 151911634722760658305651459)
  ·
    refine ⟨227867452084140987458477189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151911634722760658305651459 227867452084140987458477189)
    ·
      refine ⟨42725147265776435148464473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227867452084140987458477189 42725147265776435148464473)
      ·
        refine ⟨32043860449332326361348355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42725147265776435148464473 32043860449332326361348355)
        ·
          refine ⟨48065790673998489542022533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32043860449332326361348355 48065790673998489542022533)
          ·
            refine ⟨9012335751374716789129225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48065790673998489542022533 9012335751374716789129225)
            ·
              refine ⟨6759251813531037591846919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9012335751374716789129225 6759251813531037591846919)
              ·
                refine ⟨10138877720296556387770379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6759251813531037591846919 10138877720296556387770379)
                ·
                  refine ⟨15208316580444834581655569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10138877720296556387770379 15208316580444834581655569)
                  ·
                    refine ⟨11406237435333625936241677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15208316580444834581655569 11406237435333625936241677)
                    ·
                      refine ⟨4277339038250109726090629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406237435333625936241677 4277339038250109726090629)
                      ·
                        rfl

theorem cell23_8330088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_8330088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330088 prefixEnd_8330088 := by exact prefixLift 8330088
  have htrace : WordTrace (prefixWord ++ tailWord_8330088) baseStart_8330088 baseEnd_8330088 := by
    simpa [prefixWord, tailWord_8330088, baseEnd_8330088] using wordTrace_append hprefix tailTrace_8330088
  have hstable : (prefixWord ++ tailWord_8330088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330088).length < 2 ^ (prefixWord ++ tailWord_8330088).sum := by decide
  have hdescent : baseEnd_8330088 < baseStart_8330088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330101 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 3]
def baseStart_8330101 : Nat := 118140960795 + 8330101 * 2 ^ 59
def prefixEnd_8330101 : Nat := 4983230072969 + 3 ^ 40 * 8330101 * 2
def baseEnd_8330101 : Nat := 4277345713498618175228069

theorem tailTrace_8330101 : CollatzResearch.WordTrace tailWord_8330101 prefixEnd_8330101 4277345713498618175228069 := by
  unfold tailWord_8330101
  simp only [CollatzResearch.WordTrace]
  refine ⟨303823743594474219831526157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202549162396316146554350771 303823743594474219831526157)
  ·
    refine ⟨113933903847927832436822309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303823743594474219831526157 113933903847927832436822309)
    ·
      refine ⟨21362606971486468581904183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113933903847927832436822309 21362606971486468581904183)
      ·
        refine ⟨32043910457229702872856275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21362606971486468581904183 32043910457229702872856275)
        ·
          refine ⟨48065865685844554309284413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32043910457229702872856275 48065865685844554309284413)
          ·
            refine ⟨18024699632191707865981655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48065865685844554309284413 18024699632191707865981655)
            ·
              refine ⟨27037049448287561798972483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18024699632191707865981655 27037049448287561798972483)
              ·
                refine ⟨40555574172431342698458725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27037049448287561798972483 40555574172431342698458725)
                ·
                  refine ⟨7604170157330876755961011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40555574172431342698458725 7604170157330876755961011)
                  ·
                    refine ⟨11406255235996315133941517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7604170157330876755961011 11406255235996315133941517)
                    ·
                      refine ⟨4277345713498618175228069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406255235996315133941517 4277345713498618175228069)
                      ·
                        rfl

theorem cell23_8330101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_8330101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330101 prefixEnd_8330101 := by exact prefixLift 8330101
  have htrace : WordTrace (prefixWord ++ tailWord_8330101) baseStart_8330101 baseEnd_8330101 := by
    simpa [prefixWord, tailWord_8330101, baseEnd_8330101] using wordTrace_append hprefix tailTrace_8330101
  have hstable : (prefixWord ++ tailWord_8330101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330101).length < 2 ^ (prefixWord ++ tailWord_8330101).sum := by decide
  have hdescent : baseEnd_8330101 < baseStart_8330101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330117 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_8330117 : Nat := 118140960795 + 8330117 * 2 ^ 59
def prefixEnd_8330117 : Nat := 4983230072969 + 3 ^ 40 * 8330117 * 2
def baseEnd_8330117 : Nat := 1425784643063030037542665

theorem tailTrace_8330117 : CollatzResearch.WordTrace tailWord_8330117 prefixEnd_8330117 1425784643063030037542665 := by
  unfold tailWord_8330117
  simp only [CollatzResearch.WordTrace]
  refine ⟨303824327162416254564108605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202549551441610836376072403 303824327162416254564108605)
  ·
    refine ⟨113934122685906095461540727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303824327162416254564108605 113934122685906095461540727)
    ·
      refine ⟨170901184028859143192311091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113934122685906095461540727 170901184028859143192311091)
      ·
        refine ⟨256351776043288714788466637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170901184028859143192311091 256351776043288714788466637)
        ·
          refine ⟨96131916016233268045674989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256351776043288714788466637 96131916016233268045674989)
          ·
            refine ⟨36049468506087475517128121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96131916016233268045674989 36049468506087475517128121)
            ·
              refine ⟨27037101379565606637846091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36049468506087475517128121 27037101379565606637846091)
              ·
                refine ⟨40555652069348409956769137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27037101379565606637846091 40555652069348409956769137)
                ·
                  refine ⟨30416739052011307467576853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40555652069348409956769137 30416739052011307467576853)
                  ·
                    refine ⟨1425784643063030037542665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30416739052011307467576853 1425784643063030037542665)
                    ·
                      rfl

theorem cell23_8330117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_8330117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330117 prefixEnd_8330117 := by exact prefixLift 8330117
  have htrace : WordTrace (prefixWord ++ tailWord_8330117) baseStart_8330117 baseEnd_8330117 := by
    simpa [prefixWord, tailWord_8330117, baseEnd_8330117] using wordTrace_append hprefix tailTrace_8330117
  have hstable : (prefixWord ++ tailWord_8330117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330117).length < 2 ^ (prefixWord ++ tailWord_8330117).sum := by decide
  have hdescent : baseEnd_8330117 < baseStart_8330117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330141 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_8330141 : Nat := 118140960795 + 8330141 * 2 ^ 59
def prefixEnd_8330141 : Nat := 4983230072969 + 3 ^ 40 * 8330141 * 2
def baseEnd_8330141 : Nat := 4277366252724798018727885

theorem tailTrace_8330141 : CollatzResearch.WordTrace tailWord_8330141 prefixEnd_8330141 4277366252724798018727885 := by
  unfold tailWord_8330141
  simp only [CollatzResearch.WordTrace]
  refine ⟨303825202514329306662982277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202550135009552871108654851 303825202514329306662982277)
  ·
    refine ⟨56967225471436744999309177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303825202514329306662982277 56967225471436744999309177)
    ·
      refine ⟨42725419103577558749481883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56967225471436744999309177 42725419103577558749481883)
      ·
        refine ⟨64088128655366338124222825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42725419103577558749481883 64088128655366338124222825)
        ·
          refine ⟨48066096491524753593167119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64088128655366338124222825 48066096491524753593167119)
          ·
            refine ⟨72099144737287130389750679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48066096491524753593167119 72099144737287130389750679)
            ·
              refine ⟨108148717105930695584626019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72099144737287130389750679 108148717105930695584626019)
              ·
                refine ⟨162223075658896043376939029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108148717105930695584626019 162223075658896043376939029)
                ·
                  refine ⟨7604206671510752033294017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 162223075658896043376939029 7604206671510752033294017)
                  ·
                    refine ⟨5703155003633064024970513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7604206671510752033294017 5703155003633064024970513)
                    ·
                      refine ⟨4277366252724798018727885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703155003633064024970513 4277366252724798018727885)
                      ·
                        rfl

theorem cell23_8330141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_8330141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330141 prefixEnd_8330141 := by exact prefixLift 8330141
  have htrace : WordTrace (prefixWord ++ tailWord_8330141) baseStart_8330141 baseEnd_8330141 := by
    simpa [prefixWord, tailWord_8330141, baseEnd_8330141] using wordTrace_append hprefix tailTrace_8330141
  have hstable : (prefixWord ++ tailWord_8330141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330141).length < 2 ^ (prefixWord ++ tailWord_8330141).sum := by decide
  have hdescent : baseEnd_8330141 < baseStart_8330141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330174 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_8330174 : Nat := 118140960795 + 8330174 * 2 ^ 59
def prefixEnd_8330174 : Nat := 4983230072969 + 3 ^ 40 * 8330174 * 2
def baseEnd_8330174 : Nat := 4277383197586396389615233

theorem tailTrace_8330174 : CollatzResearch.WordTrace tailWord_8330174 prefixEnd_8330174 4277383197586396389615233 := by
  unfold tailWord_8330174
  simp only [CollatzResearch.WordTrace]
  refine ⟨37978300765401219162366697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202550937415473168865955717 37978300765401219162366697)
  ·
    refine ⟨28483725574050914371775023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37978300765401219162366697 28483725574050914371775023)
    ·
      refine ⟨42725588361076371557662535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28483725574050914371775023 42725588361076371557662535)
      ·
        refine ⟨64088382541614557336493803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42725588361076371557662535 64088382541614557336493803)
        ·
          refine ⟨96132573812421836004740705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64088382541614557336493803 96132573812421836004740705)
          ·
            refine ⟨72099430359316377003555529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96132573812421836004740705 72099430359316377003555529)
            ·
              refine ⟨54074572769487282752666647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72099430359316377003555529 54074572769487282752666647)
              ·
                refine ⟨81111859154230924128999971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54074572769487282752666647 81111859154230924128999971)
                ·
                  refine ⟨121667788731346386193499957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81111859154230924128999971 121667788731346386193499957)
                  ·
                    refine ⟨11406355193563723705640621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121667788731346386193499957 11406355193563723705640621)
                    ·
                      refine ⟨4277383197586396389615233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406355193563723705640621 4277383197586396389615233)
                      ·
                        rfl

theorem cell23_8330174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_8330174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330174 prefixEnd_8330174 := by exact prefixLift 8330174
  have htrace : WordTrace (prefixWord ++ tailWord_8330174) baseStart_8330174 baseEnd_8330174 := by
    simpa [prefixWord, tailWord_8330174, baseEnd_8330174] using wordTrace_append hprefix tailTrace_8330174
  have hstable : (prefixWord ++ tailWord_8330174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330174).length < 2 ^ (prefixWord ++ tailWord_8330174).sum := by decide
  have hdescent : baseEnd_8330174 < baseStart_8330174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330224 : List Nat := [2, 1, 1, 1, 3, 2, 1, 5, 3, 4]
def baseStart_8330224 : Nat := 118140960795 + 8330224 * 2 ^ 59
def prefixEnd_8330224 : Nat := 4983230072969 + 3 ^ 40 * 8330224 * 2
def baseEnd_8330224 : Nat := 1425802957206373731330001

theorem tailTrace_8330224 : CollatzResearch.WordTrace tailWord_8330224 prefixEnd_8330224 1425802957206373731330001 := by
  unfold tailWord_8330224
  simp only [CollatzResearch.WordTrace]
  refine ⟨151914114886514305919126863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202552153182019074558835817 151914114886514305919126863)
  ·
    refine ⟨227871172329771458878690295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151914114886514305919126863 227871172329771458878690295)
    ·
      refine ⟨341806758494657188318035443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227871172329771458878690295 341806758494657188318035443)
      ·
        refine ⟨512710137741985782477053165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341806758494657188318035443 512710137741985782477053165)
        ·
          refine ⟨192266301653244668428894937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512710137741985782477053165 192266301653244668428894937)
          ·
            refine ⟨144199726239933501321671203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192266301653244668428894937 144199726239933501321671203)
            ·
              refine ⟨216299589359900251982506805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144199726239933501321671203 216299589359900251982506805)
              ·
                refine ⟨20278086502490648623360013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216299589359900251982506805 20278086502490648623360013)
                ·
                  refine ⟨7604282438433993233760005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20278086502490648623360013 7604282438433993233760005)
                  ·
                    refine ⟨1425802957206373731330001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7604282438433993233760005 1425802957206373731330001)
                    ·
                      rfl

theorem cell23_8330224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_8330224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330224 prefixEnd_8330224 := by exact prefixLift 8330224
  have htrace : WordTrace (prefixWord ++ tailWord_8330224) baseStart_8330224 baseEnd_8330224 := by
    simpa [prefixWord, tailWord_8330224, baseEnd_8330224] using wordTrace_append hprefix tailTrace_8330224
  have hstable : (prefixWord ++ tailWord_8330224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330224).length < 2 ^ (prefixWord ++ tailWord_8330224).sum := by decide
  have hdescent : baseEnd_8330224 < baseStart_8330224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330227 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4]
def baseStart_8330227 : Nat := 118140960795 + 8330227 * 2 ^ 59
def prefixEnd_8330227 : Nat := 4983230072969 + 3 ^ 40 * 8330227 * 2
def baseEnd_8330227 : Nat := 4277410412061084682252489

theorem tailTrace_8330227 : CollatzResearch.WordTrace tailWord_8330227 prefixEnd_8330227 4277410412061084682252489 := by
  unfold tailWord_8330227
  simp only [CollatzResearch.WordTrace]
  refine ⟨303828339192017743350612935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202552226128011828900408623 303828339192017743350612935)
  ·
    refine ⟨455742508788026615025919403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303828339192017743350612935 455742508788026615025919403)
    ·
      refine ⟨683613763182039922538879105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455742508788026615025919403 683613763182039922538879105)
      ·
        refine ⟨512710322386529941904159329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683613763182039922538879105 512710322386529941904159329)
        ·
          refine ⟨384532741789897456428119497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512710322386529941904159329 384532741789897456428119497)
          ·
            refine ⟨288399556342423092321089623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384532741789897456428119497 288399556342423092321089623)
            ·
              refine ⟨432599334513634638481634435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288399556342423092321089623 432599334513634638481634435)
              ·
                refine ⟨648899001770451957722451653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432599334513634638481634435 648899001770451957722451653)
                ·
                  refine ⟨121668562831959742072959685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648899001770451957722451653 121668562831959742072959685)
                  ·
                    refine ⟨22812855530992451638679941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121668562831959742072959685 22812855530992451638679941)
                    ·
                      refine ⟨4277410412061084682252489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22812855530992451638679941 4277410412061084682252489)
                      ·
                        rfl

theorem cell23_8330227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 4].length) (baseStart_8330227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330227 prefixEnd_8330227 := by exact prefixLift 8330227
  have htrace : WordTrace (prefixWord ++ tailWord_8330227) baseStart_8330227 baseEnd_8330227 := by
    simpa [prefixWord, tailWord_8330227, baseEnd_8330227] using wordTrace_append hprefix tailTrace_8330227
  have hstable : (prefixWord ++ tailWord_8330227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330227).length < 2 ^ (prefixWord ++ tailWord_8330227).sum := by decide
  have hdescent : baseEnd_8330227 < baseStart_8330227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330234 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3]
def baseStart_8330234 : Nat := 118140960795 + 8330234 * 2 ^ 59
def prefixEnd_8330234 : Nat := 4983230072969 + 3 ^ 40 * 8330234 * 2
def baseEnd_8330234 : Nat := 4277414006425666154864957

theorem tailTrace_8330234 : CollatzResearch.WordTrace tailWord_8330234 prefixEnd_8330234 4277414006425666154864957 := by
  unfold tailWord_8330234
  simp only [CollatzResearch.WordTrace]
  refine ⟨75957148625748095886529439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202552396335328255697411837 75957148625748095886529439)
  ·
    refine ⟨113935722938622143829794159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75957148625748095886529439 113935722938622143829794159)
    ·
      refine ⟨170903584407933215744691239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113935722938622143829794159 170903584407933215744691239)
      ·
        refine ⟨256355376611899823617036859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170903584407933215744691239 256355376611899823617036859)
        ·
          refine ⟨384533064917849735425555289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256355376611899823617036859 384533064917849735425555289)
          ·
            refine ⟨288399798688387301569166467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384533064917849735425555289 288399798688387301569166467)
            ·
              refine ⟨432599698032580952353749701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288399798688387301569166467 432599698032580952353749701)
              ·
                refine ⟨81112443381108928566328069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432599698032580952353749701 81112443381108928566328069)
                ·
                  refine ⟨15208583133957924106186513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81112443381108928566328069 15208583133957924106186513)
                  ·
                    refine ⟨11406437350468443079639885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15208583133957924106186513 11406437350468443079639885)
                    ·
                      refine ⟨4277414006425666154864957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406437350468443079639885 4277414006425666154864957)
                      ·
                        rfl

theorem cell23_8330234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3].length) (baseStart_8330234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330234 prefixEnd_8330234 := by exact prefixLift 8330234
  have htrace : WordTrace (prefixWord ++ tailWord_8330234) baseStart_8330234 baseEnd_8330234 := by
    simpa [prefixWord, tailWord_8330234, baseEnd_8330234] using wordTrace_append hprefix tailTrace_8330234
  have hstable : (prefixWord ++ tailWord_8330234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330234).length < 2 ^ (prefixWord ++ tailWord_8330234).sum := by decide
  have hdescent : baseEnd_8330234 < baseStart_8330234 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330237 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 10]
def baseStart_8330237 : Nat := 118140960795 + 8330237 * 2 ^ 59
def prefixEnd_8330237 : Nat := 4983230072969 + 3 ^ 40 * 8330237 * 2
def baseEnd_8330237 : Nat := 475268394096403293680827

theorem tailTrace_8330237 : CollatzResearch.WordTrace tailWord_8330237 prefixEnd_8330237 475268394096403293680827 := by
  unfold tailWord_8330237
  simp only [CollatzResearch.WordTrace]
  refine ⟨303828703921981515058476965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202552469281321010038984643 303828703921981515058476965)
  ·
    refine ⟨56967881985371534073464431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303828703921981515058476965 56967881985371534073464431)
    ·
      refine ⟨85451822978057301110196647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56967881985371534073464431 85451822978057301110196647)
      ·
        refine ⟨128177734467085951665294971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85451822978057301110196647 128177734467085951665294971)
        ·
          refine ⟨192266601700628927497942457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128177734467085951665294971 192266601700628927497942457)
          ·
            refine ⟨144199951275471695623456843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192266601700628927497942457 144199951275471695623456843)
            ·
              refine ⟨216299926913207543435185265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144199951275471695623456843 216299926913207543435185265)
              ·
                refine ⟨162224945184905657576388949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216299926913207543435185265 162224945184905657576388949)
                ·
                  refine ⟨475268394096403293680827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 162224945184905657576388949 475268394096403293680827)
                  ·
                    rfl

theorem cell23_8330237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_8330237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330237 prefixEnd_8330237 := by exact prefixLift 8330237
  have htrace : WordTrace (prefixWord ++ tailWord_8330237) baseStart_8330237 baseEnd_8330237 := by
    simpa [prefixWord, tailWord_8330237, baseEnd_8330237] using wordTrace_append hprefix tailTrace_8330237
  have hstable : (prefixWord ++ tailWord_8330237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330237).length < 2 ^ (prefixWord ++ tailWord_8330237).sum := by decide
  have hdescent : baseEnd_8330237 < baseStart_8330237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330241 : List Nat := [1, 2, 4, 1, 2, 3, 1, 2, 3, 4]
def baseStart_8330241 : Nat := 118140960795 + 8330241 * 2 ^ 59
def prefixEnd_8330241 : Nat := 4983230072969 + 3 ^ 40 * 8330241 * 2
def baseEnd_8330241 : Nat := 1425805866930082542492475

theorem tailTrace_8330241 : CollatzResearch.WordTrace tailWord_8330241 prefixEnd_8330241 1425805866930082542492475 := by
  unfold tailWord_8330241
  simp only [CollatzResearch.WordTrace]
  refine ⟨303828849813967023741622577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202552566542644682494415051 303828849813967023741622577)
  ·
    refine ⟨227871637360475267806216933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303828849813967023741622577 227871637360475267806216933)
    ·
      refine ⟨42725932005089112713665675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227871637360475267806216933 42725932005089112713665675)
      ·
        refine ⟨64088898007633669070498513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42725932005089112713665675 64088898007633669070498513)
        ·
          refine ⟨48066673505725251802873885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64088898007633669070498513 48066673505725251802873885)
          ·
            refine ⟨18025002564646969426077707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48066673505725251802873885 18025002564646969426077707)
            ·
              refine ⟨27037503846970454139116561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18025002564646969426077707 27037503846970454139116561)
              ·
                refine ⟨20278127885227840604337421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27037503846970454139116561 20278127885227840604337421)
                ·
                  refine ⟨7604297956960440226626533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20278127885227840604337421 7604297956960440226626533)
                  ·
                    refine ⟨1425805866930082542492475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7604297956960440226626533 1425805866930082542492475)
                    ·
                      rfl

theorem cell23_8330241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_8330241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330241 prefixEnd_8330241 := by exact prefixLift 8330241
  have htrace : WordTrace (prefixWord ++ tailWord_8330241) baseStart_8330241 baseEnd_8330241 := by
    simpa [prefixWord, tailWord_8330241, baseEnd_8330241] using wordTrace_append hprefix tailTrace_8330241
  have hstable : (prefixWord ++ tailWord_8330241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330241).length < 2 ^ (prefixWord ++ tailWord_8330241).sum := by decide
  have hdescent : baseEnd_8330241 < baseStart_8330241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330251 : List Nat := [1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 3]
def baseStart_8330251 : Nat := 118140960795 + 8330251 * 2 ^ 59
def prefixEnd_8330251 : Nat := 4983230072969 + 3 ^ 40 * 8330251 * 2
def baseEnd_8330251 : Nat := 4277422735596792588352379

theorem tailTrace_8330251 : CollatzResearch.WordTrace tailWord_8330251 prefixEnd_8330251 4277422735596792588352379 := by
  unfold tailWord_8330251
  simp only [CollatzResearch.WordTrace]
  refine ⟨303829214543930795449486607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202552809695953863632991071 303829214543930795449486607)
  ·
    refine ⟨455743821815896193174229911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303829214543930795449486607 455743821815896193174229911)
    ·
      refine ⟨683615732723844289761344867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455743821815896193174229911 683615732723844289761344867)
      ·
        refine ⟨1025423599085766434642017301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683615732723844289761344867 1025423599085766434642017301)
        ·
          refine ⟨48066731207145301623844561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1025423599085766434642017301 48066731207145301623844561)
          ·
            refine ⟨36050048405358976217883421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48066731207145301623844561 36050048405358976217883421)
            ·
              refine ⟨13518768152009616081706283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36050048405358976217883421 13518768152009616081706283)
              ·
                refine ⟨20278152228014424122559425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13518768152009616081706283 20278152228014424122559425)
                ·
                  refine ⟨15208614171010818091919569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20278152228014424122559425 15208614171010818091919569)
                  ·
                    refine ⟨11406460628258113568939677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15208614171010818091919569 11406460628258113568939677)
                    ·
                      refine ⟨4277422735596792588352379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406460628258113568939677 4277422735596792588352379)
                      ·
                        rfl

theorem cell23_8330251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2, 3].length) (baseStart_8330251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330251 prefixEnd_8330251 := by exact prefixLift 8330251
  have htrace : WordTrace (prefixWord ++ tailWord_8330251) baseStart_8330251 baseEnd_8330251 := by
    simpa [prefixWord, tailWord_8330251, baseEnd_8330251] using wordTrace_append hprefix tailTrace_8330251
  have hstable : (prefixWord ++ tailWord_8330251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330251).length < 2 ^ (prefixWord ++ tailWord_8330251).sum := by decide
  have hdescent : baseEnd_8330251 < baseStart_8330251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330257 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_8330257 : Nat := 118140960795 + 8330257 * 2 ^ 59
def prefixEnd_8330257 : Nat := 4983230072969 + 3 ^ 40 * 8330257 * 2
def baseEnd_8330257 : Nat := 4277425816480719564877351

theorem tailTrace_8330257 : CollatzResearch.WordTrace tailWord_8330257 prefixEnd_8330257 4277425816480719564877351 := by
  unfold tailWord_8330257
  simp only [CollatzResearch.WordTrace]
  refine ⟨303829433381909058474205025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202552955587939372316136683 303829433381909058474205025)
  ·
    refine ⟨227872075036431793855653769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303829433381909058474205025 227872075036431793855653769)
    ·
      refine ⟨170904056277323845391740327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227872075036431793855653769 170904056277323845391740327)
      ·
        refine ⟨256356084415985768087610491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170904056277323845391740327 256356084415985768087610491)
        ·
          refine ⟨384534126623978652131415737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256356084415985768087610491 384534126623978652131415737)
          ·
            refine ⟨288400594967983989098561803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384534126623978652131415737 288400594967983989098561803)
            ·
              refine ⟨432600892451975983647842705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288400594967983989098561803 432600892451975983647842705)
              ·
                refine ⟨324450669338981987735882029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432600892451975983647842705 324450669338981987735882029)
                ·
                  refine ⟨121669001002118245400955761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324450669338981987735882029 121669001002118245400955761)
                  ·
                    refine ⟨91251750751588684050716821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121669001002118245400955761 91251750751588684050716821)
                    ·
                      refine ⟨4277425816480719564877351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91251750751588684050716821 4277425816480719564877351)
                      ·
                        rfl

theorem cell23_8330257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_8330257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330257 prefixEnd_8330257 := by exact prefixLift 8330257
  have htrace : WordTrace (prefixWord ++ tailWord_8330257) baseStart_8330257 baseEnd_8330257 := by
    simpa [prefixWord, tailWord_8330257, baseEnd_8330257] using wordTrace_append hprefix tailTrace_8330257
  have hstable : (prefixWord ++ tailWord_8330257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330257).length < 2 ^ (prefixWord ++ tailWord_8330257).sum := by decide
  have hdescent : baseEnd_8330257 < baseStart_8330257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330271 : List Nat := [1, 1, 2, 4, 1, 5, 1, 2, 6]
def baseStart_8330271 : Nat := 118140960795 + 8330271 * 2 ^ 59
def prefixEnd_8330271 : Nat := 4983230072969 + 3 ^ 40 * 8330271 * 2
def baseEnd_8330271 : Nat := 475270333912209167789143

theorem tailTrace_8330271 : CollatzResearch.WordTrace tailWord_8330271 prefixEnd_8330271 475270333912209167789143 := by
  unfold tailWord_8330271
  simp only [CollatzResearch.WordTrace]
  refine ⟨303829944003858338865214667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202553296002572225910143111 303829944003858338865214667)
  ·
    refine ⟨455744916005787508297822001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303829944003858338865214667 455744916005787508297822001)
    ·
      refine ⟨341808687004340631223366501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455744916005787508297822001 341808687004340631223366501)
      ·
        refine ⟨64089128813313868354381219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341808687004340631223366501 64089128813313868354381219)
        ·
          refine ⟨96133693219970802531571829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64089128813313868354381219 96133693219970802531571829)
          ·
            refine ⟨9012533739372262737334859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96133693219970802531571829 9012533739372262737334859)
            ·
              refine ⟨13518800609058394106002289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012533739372262737334859 13518800609058394106002289)
              ·
                refine ⟨10139100456793795579501717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13518800609058394106002289 10139100456793795579501717)
                ·
                  refine ⟨475270333912209167789143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10139100456793795579501717 475270333912209167789143)
                  ·
                    rfl

theorem cell23_8330271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 6].length) (baseStart_8330271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330271 prefixEnd_8330271 := by exact prefixLift 8330271
  have htrace : WordTrace (prefixWord ++ tailWord_8330271) baseStart_8330271 baseEnd_8330271 := by
    simpa [prefixWord, tailWord_8330271, baseEnd_8330271] using wordTrace_append hprefix tailTrace_8330271
  have hstable : (prefixWord ++ tailWord_8330271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330271).length < 2 ^ (prefixWord ++ tailWord_8330271).sum := by decide
  have hdescent : baseEnd_8330271 < baseStart_8330271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330274 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_8330274 : Nat := 118140960795 + 8330274 * 2 ^ 59
def prefixEnd_8330274 : Nat := 4983230072969 + 3 ^ 40 * 8330274 * 2
def baseEnd_8330274 : Nat := 4277434545651845998364773

theorem tailTrace_8330274 : CollatzResearch.WordTrace tailWord_8330274 prefixEnd_8330274 4277434545651845998364773 := by
  unfold tailWord_8330274
  simp only [CollatzResearch.WordTrace]
  refine ⟨75957513355711867594393469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202553368948564980251715917 75957513355711867594393469)
  ·
    refine ⟨28484067508391950347897551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75957513355711867594393469 28484067508391950347897551)
    ·
      refine ⟨42726101262587925521846327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28484067508391950347897551 42726101262587925521846327)
      ·
        refine ⟨64089151893881888282769491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42726101262587925521846327 64089151893881888282769491)
        ·
          refine ⟨96133727840822832424154237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64089151893881888282769491 96133727840822832424154237)
          ·
            refine ⟨36050147940308562159057839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96133727840822832424154237 36050147940308562159057839)
            ·
              refine ⟨54075221910462843238586759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36050147940308562159057839 54075221910462843238586759)
              ·
                refine ⟨81112832865694264857880139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54075221910462843238586759 81112832865694264857880139)
                ·
                  refine ⟨121669249298541397286820209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81112832865694264857880139 121669249298541397286820209)
                  ·
                    refine ⟨91251936973906047965115157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121669249298541397286820209 91251936973906047965115157)
                    ·
                      refine ⟨4277434545651845998364773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91251936973906047965115157 4277434545651845998364773)
                      ·
                        rfl

theorem cell23_8330274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_8330274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330274 prefixEnd_8330274 := by exact prefixLift 8330274
  have htrace : WordTrace (prefixWord ++ tailWord_8330274) baseStart_8330274 baseEnd_8330274 := by
    simpa [prefixWord, tailWord_8330274, baseEnd_8330274] using wordTrace_append hprefix tailTrace_8330274
  have hstable : (prefixWord ++ tailWord_8330274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330274).length < 2 ^ (prefixWord ++ tailWord_8330274).sum := by decide
  have hdescent : baseEnd_8330274 < baseStart_8330274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330301 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_8330301 : Nat := 118140960795 + 8330301 * 2 ^ 59
def prefixEnd_8330301 : Nat := 4983230072969 + 3 ^ 40 * 8330301 * 2
def baseEnd_8330301 : Nat := 1425816136543172464242383

theorem tailTrace_8330301 : CollatzResearch.WordTrace tailWord_8330301 prefixEnd_8330301 1425816136543172464242383 := by
  unfold tailWord_8330301
  simp only [CollatzResearch.WordTrace]
  refine ⟨303831038193749653988806757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202554025462499769325871171 303831038193749653988806757)
  ·
    refine ⟨56968319661328060122901267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303831038193749653988806757 56968319661328060122901267)
    ·
      refine ⟨85452479491992090184351901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56968319661328060122901267 85452479491992090184351901)
      ·
        refine ⟨32044679809497033819131963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85452479491992090184351901 32044679809497033819131963)
        ·
          refine ⟨48067019714245550728697945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32044679809497033819131963 48067019714245550728697945)
          ·
            refine ⟨36050264785684163046523459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48067019714245550728697945 36050264785684163046523459)
            ·
              refine ⟨54075397178526244569785189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36050264785684163046523459 54075397178526244569785189)
              ·
                refine ⟨10139136970973670856834723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54075397178526244569785189 10139136970973670856834723)
                ·
                  refine ⟨15208705456460506285252085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139136970973670856834723 15208705456460506285252085)
                  ·
                    refine ⟨1425816136543172464242383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15208705456460506285252085 1425816136543172464242383)
                    ·
                      rfl

theorem cell23_8330301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_8330301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330301 prefixEnd_8330301 := by exact prefixLift 8330301
  have htrace : WordTrace (prefixWord ++ tailWord_8330301) baseStart_8330301 baseEnd_8330301 := by
    simpa [prefixWord, tailWord_8330301, baseEnd_8330301] using wordTrace_append hprefix tailTrace_8330301
  have hstable : (prefixWord ++ tailWord_8330301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330301).length < 2 ^ (prefixWord ++ tailWord_8330301).sum := by decide
  have hdescent : baseEnd_8330301 < baseStart_8330301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330314 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_8330314 : Nat := 118140960795 + 8330314 * 2 ^ 59
def prefixEnd_8330314 : Nat := 4983230072969 + 3 ^ 40 * 8330314 * 2
def baseEnd_8330314 : Nat := 1425818361626008613954863

theorem tailTrace_8330314 : CollatzResearch.WordTrace tailWord_8330314 prefixEnd_8330314 1425818361626008613954863 := by
  unfold tailWord_8330314
  simp only [CollatzResearch.WordTrace]
  refine ⟨75957878085675639302257499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202554341561801704806019997 75957878085675639302257499)
  ·
    refine ⟨113936817128513458953386249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75957878085675639302257499 113936817128513458953386249)
    ·
      refine ⟨85452612846385094215039687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113936817128513458953386249 85452612846385094215039687)
      ·
        refine ⟨128178919269577641322559531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85452612846385094215039687 128178919269577641322559531)
        ·
          refine ⟨192268378904366461983839297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128178919269577641322559531 192268378904366461983839297)
          ·
            refine ⟨144201284178274846487879473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192268378904366461983839297 144201284178274846487879473)
            ·
              refine ⟨108150963133706134865909605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144201284178274846487879473 108150963133706134865909605)
              ·
                refine ⟨20278305587569900287358051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108150963133706134865909605 20278305587569900287358051)
                ·
                  refine ⟨30417458381354850431037077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20278305587569900287358051 30417458381354850431037077)
                  ·
                    refine ⟨1425818361626008613954863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30417458381354850431037077 1425818361626008613954863)
                    ·
                      rfl

theorem cell23_8330314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_8330314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330314 prefixEnd_8330314 := by exact prefixLift 8330314
  have htrace : WordTrace (prefixWord ++ tailWord_8330314) baseStart_8330314 baseEnd_8330314 := by
    simpa [prefixWord, tailWord_8330314, baseEnd_8330314] using wordTrace_append hprefix tailTrace_8330314
  have hstable : (prefixWord ++ tailWord_8330314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330314).length < 2 ^ (prefixWord ++ tailWord_8330314).sum := by decide
  have hdescent : baseEnd_8330314 < baseStart_8330314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330321 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_8330321 : Nat := 118140960795 + 8330321 * 2 ^ 59
def prefixEnd_8330321 : Nat := 4983230072969 + 3 ^ 40 * 8330321 * 2
def baseEnd_8330321 : Nat := 4277458679242607314477057

theorem tailTrace_8330321 : CollatzResearch.WordTrace tailWord_8330321 prefixEnd_8330321 4277458679242607314477057 := by
  unfold tailWord_8330321
  simp only [CollatzResearch.WordTrace]
  refine ⟨303831767653677197404534817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202554511769118131603023211 303831767653677197404534817)
  ·
    refine ⟨227873825740257898053401113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303831767653677197404534817 227873825740257898053401113)
    ·
      refine ⟨170905369305193423540050835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227873825740257898053401113 170905369305193423540050835)
      ·
        refine ⟨256358053957790135310076253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170905369305193423540050835 256358053957790135310076253)
        ·
          refine ⟨96134270234171300741278595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256358053957790135310076253 96134270234171300741278595)
          ·
            refine ⟨144201405351256951111917893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96134270234171300741278595 144201405351256951111917893)
            ·
              refine ⟨27037763503360678333484605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 144201405351256951111917893 27037763503360678333484605)
              ·
                refine ⟨10139161313760254375056727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27037763503360678333484605 10139161313760254375056727)
                ·
                  refine ⟨15208741970640381562585091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139161313760254375056727 15208741970640381562585091)
                  ·
                    refine ⟨22813112955960572343877637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15208741970640381562585091 22813112955960572343877637)
                    ·
                      refine ⟨4277458679242607314477057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22813112955960572343877637 4277458679242607314477057)
                      ·
                        rfl

theorem cell23_8330321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_8330321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330321 prefixEnd_8330321 := by exact prefixLift 8330321
  have htrace : WordTrace (prefixWord ++ tailWord_8330321) baseStart_8330321 baseEnd_8330321 := by
    simpa [prefixWord, tailWord_8330321, baseEnd_8330321] using wordTrace_append hprefix tailTrace_8330321
  have hstable : (prefixWord ++ tailWord_8330321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330321).length < 2 ^ (prefixWord ++ tailWord_8330321).sum := by decide
  have hdescent : baseEnd_8330321 < baseStart_8330321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330332 : List Nat := [2, 2, 4, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_8330332 : Nat := 118140960795 + 8330332 * 2 ^ 59
def prefixEnd_8330332 : Nat := 4983230072969 + 3 ^ 40 * 8330332 * 2
def baseEnd_8330332 : Nat := 4277464327529806771439507

theorem tailTrace_8330332 : CollatzResearch.WordTrace tailWord_8330332 prefixEnd_8330332 4277464327529806771439507 := by
  unfold tailWord_8330332
  simp only [CollatzResearch.WordTrace]
  refine ⟨151916084428318673141592625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202554779237758230855456833 151916084428318673141592625)
  ·
    refine ⟨113937063321239004856194469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151916084428318673141592625 113937063321239004856194469)
    ·
      refine ⟨21363199372732313410536463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113937063321239004856194469 21363199372732313410536463)
      ·
        refine ⟨32044799059098470115804695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21363199372732313410536463 32044799059098470115804695)
        ·
          refine ⟨48067198588647705173707043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32044799059098470115804695 48067198588647705173707043)
          ·
            refine ⟨72100797882971557760560565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48067198588647705173707043 72100797882971557760560565)
            ·
              refine ⟨6759449801528583540052553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72100797882971557760560565 6759449801528583540052553)
              ·
                refine ⟨5069587351146437655039415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6759449801528583540052553 5069587351146437655039415)
                ·
                  refine ⟨7604381026719656482559123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069587351146437655039415 7604381026719656482559123)
                  ·
                    refine ⟨11406571540079484723838685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7604381026719656482559123 11406571540079484723838685)
                    ·
                      refine ⟨4277464327529806771439507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406571540079484723838685 4277464327529806771439507)
                      ·
                        rfl

theorem cell23_8330332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_8330332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330332 prefixEnd_8330332 := by exact prefixLift 8330332
  have htrace : WordTrace (prefixWord ++ tailWord_8330332) baseStart_8330332 baseEnd_8330332 := by
    simpa [prefixWord, tailWord_8330332, baseEnd_8330332] using wordTrace_append hprefix tailTrace_8330332
  have hstable : (prefixWord ++ tailWord_8330332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330332).length < 2 ^ (prefixWord ++ tailWord_8330332).sum := by decide
  have hdescent : baseEnd_8330332 < baseStart_8330332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330341 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 3]
def baseStart_8330341 : Nat := 118140960795 + 8330341 * 2 ^ 59
def prefixEnd_8330341 : Nat := 4983230072969 + 3 ^ 40 * 8330341 * 2
def baseEnd_8330341 : Nat := 4277468948855697236226965

theorem tailTrace_8330341 : CollatzResearch.WordTrace tailWord_8330341 prefixEnd_8330341 4277468948855697236226965 := by
  unfold tailWord_8330341
  simp only [CollatzResearch.WordTrace]
  refine ⟨303832497113604740820262877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202554998075736493880175251 303832497113604740820262877)
  ·
    refine ⟨113937186417601777807598579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303832497113604740820262877 113937186417601777807598579)
    ·
      refine ⟨170905779626402666711397869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113937186417601777807598579 170905779626402666711397869)
      ·
        refine ⟨64089667359901000016774201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170905779626402666711397869 64089667359901000016774201)
        ·
          refine ⟨48067250519925750012580651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64089667359901000016774201 48067250519925750012580651)
          ·
            refine ⟨72100875779888625018870977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48067250519925750012580651 72100875779888625018870977)
            ·
              refine ⟨54075656834916468764153233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72100875779888625018870977 54075656834916468764153233)
              ·
                refine ⟨40556742626187351573114925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54075656834916468764153233 40556742626187351573114925)
                ·
                  refine ⟨15208778484820256839918097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40556742626187351573114925 15208778484820256839918097)
                  ·
                    refine ⟨11406583863615192629938573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15208778484820256839918097 11406583863615192629938573)
                    ·
                      refine ⟨4277468948855697236226965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406583863615192629938573 4277468948855697236226965)
                      ·
                        rfl

theorem cell23_8330341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_8330341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330341 prefixEnd_8330341 := by exact prefixLift 8330341
  have htrace : WordTrace (prefixWord ++ tailWord_8330341) baseStart_8330341 baseEnd_8330341 := by
    simpa [prefixWord, tailWord_8330341, baseEnd_8330341] using wordTrace_append hprefix tailTrace_8330341
  have hstable : (prefixWord ++ tailWord_8330341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330341).length < 2 ^ (prefixWord ++ tailWord_8330341).sum := by decide
  have hdescent : baseEnd_8330341 < baseStart_8330341 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330358 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3]
def baseStart_8330358 : Nat := 118140960795 + 8330358 * 2 ^ 59
def prefixEnd_8330358 : Nat := 4983230072969 + 3 ^ 40 * 8330358 * 2
def baseEnd_8330358 : Nat := 4277477678026823669714387

theorem tailTrace_8330358 : CollatzResearch.WordTrace tailWord_8330358 prefixEnd_8330358 4277477678026823669714387 := by
  unfold tailWord_8330358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18989569822158947045226983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202555411436362101815754485 18989569822158947045226983)
  ·
    refine ⟨28484354733238420567840475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18989569822158947045226983 28484354733238420567840475)
    ·
      refine ⟨42726532099857630851760713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28484354733238420567840475 42726532099857630851760713)
      ·
        refine ⟨32044899074893223138820535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42726532099857630851760713 32044899074893223138820535)
        ·
          refine ⟨48067348612339834708230803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32044899074893223138820535 48067348612339834708230803)
          ·
            refine ⟨72101022918509752062346205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48067348612339834708230803 72101022918509752062346205)
            ·
              refine ⟨27037883594441157023379827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72101022918509752062346205 27037883594441157023379827)
              ·
                refine ⟨40556825391661735535069741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27037883594441157023379827 40556825391661735535069741)
                ·
                  refine ⟨15208809521873150825651153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40556825391661735535069741 15208809521873150825651153)
                  ·
                    refine ⟨11406607141404863119238365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15208809521873150825651153 11406607141404863119238365)
                    ·
                      refine ⟨4277477678026823669714387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406607141404863119238365 4277477678026823669714387)
                      ·
                        rfl

theorem cell23_8330358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_8330358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330358 prefixEnd_8330358 := by exact prefixLift 8330358
  have htrace : WordTrace (prefixWord ++ tailWord_8330358) baseStart_8330358 baseEnd_8330358 := by
    simpa [prefixWord, tailWord_8330358, baseEnd_8330358] using wordTrace_append hprefix tailTrace_8330358
  have hstable : (prefixWord ++ tailWord_8330358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330358).length < 2 ^ (prefixWord ++ tailWord_8330358).sum := by decide
  have hdescent : baseEnd_8330358 < baseStart_8330358 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330371 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 3]
def baseStart_8330371 : Nat := 118140960795 + 8330371 * 2 ^ 59
def prefixEnd_8330371 : Nat := 4983230072969 + 3 ^ 40 * 8330371 * 2
def baseEnd_8330371 : Nat := 4277484353275332118851827

theorem tailTrace_8330371 : CollatzResearch.WordTrace tailWord_8330371 prefixEnd_8330371 4277484353275332118851827 := by
  unfold tailWord_8330371
  simp only [CollatzResearch.WordTrace]
  refine ⟨303833591303496055943854967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202555727535664037295903311 303833591303496055943854967)
  ·
    refine ⟨455750386955244083915782451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303833591303496055943854967 455750386955244083915782451)
    ·
      refine ⟨683625580432866125873673677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455750386955244083915782451 683625580432866125873673677)
      ·
        refine ⟨256359592662324797202627629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 683625580432866125873673677 256359592662324797202627629)
        ·
          refine ⟨96134847248371798950985361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256359592662324797202627629 96134847248371798950985361)
          ·
            refine ⟨72101135436278849213239021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96134847248371798950985361 72101135436278849213239021)
            ·
              refine ⟨27037925788604568454964633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72101135436278849213239021 27037925788604568454964633)
              ·
                refine ⟨20278444341453426341223475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27037925788604568454964633 20278444341453426341223475)
                ·
                  refine ⟨30417666512180139511835213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20278444341453426341223475 30417666512180139511835213)
                  ·
                    refine ⟨11406624942067552316938205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30417666512180139511835213 11406624942067552316938205)
                    ·
                      refine ⟨4277484353275332118851827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406624942067552316938205 4277484353275332118851827)
                      ·
                        rfl

theorem cell23_8330371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3, 3].length) (baseStart_8330371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330371 prefixEnd_8330371 := by exact prefixLift 8330371
  have htrace : WordTrace (prefixWord ++ tailWord_8330371) baseStart_8330371 baseEnd_8330371 := by
    simpa [prefixWord, tailWord_8330371, baseEnd_8330371] using wordTrace_append hprefix tailTrace_8330371
  have hstable : (prefixWord ++ tailWord_8330371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330371).length < 2 ^ (prefixWord ++ tailWord_8330371).sum := by decide
  have hdescent : baseEnd_8330371 < baseStart_8330371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330481 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 2, 5]
def baseStart_8330481 : Nat := 118140960795 + 8330481 * 2 ^ 59
def prefixEnd_8330481 : Nat := 4983230072969 + 3 ^ 40 * 8330481 * 2
def baseEnd_8330481 : Nat := 1425846945382442229492107

theorem tailTrace_8330481 : CollatzResearch.WordTrace tailWord_8330481 prefixEnd_8330481 1425846945382442229492107 := by
  unfold tailWord_8330481
  simp only [CollatzResearch.WordTrace]
  refine ⟨303837603333097544730359297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202558402222065029820239531 303837603333097544730359297)
  ·
    refine ⟨227878202499823158547769473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303837603333097544730359297 227878202499823158547769473)
    ·
      refine ⟨170908651874867368910827105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227878202499823158547769473 170908651874867368910827105)
      ·
        refine ⟨128181488906150526683120329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170908651874867368910827105 128181488906150526683120329)
        ·
          refine ⟨96136116679612895012340247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128181488906150526683120329 96136116679612895012340247)
          ·
            refine ⟨144204175019419342518510371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96136116679612895012340247 144204175019419342518510371)
            ·
              refine ⟨216306262529129013777765557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144204175019419342518510371 216306262529129013777765557)
              ·
                refine ⟨20278712112105845041665521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 216306262529129013777765557 20278712112105845041665521)
                ·
                  refine ⟨15209034084079383781249141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20278712112105845041665521 15209034084079383781249141)
                  ·
                    refine ⟨1425846945382442229492107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15209034084079383781249141 1425846945382442229492107)
                    ·
                      rfl

theorem cell23_8330481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_8330481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330481 prefixEnd_8330481 := by exact prefixLift 8330481
  have htrace : WordTrace (prefixWord ++ tailWord_8330481) baseStart_8330481 baseEnd_8330481 := by
    simpa [prefixWord, tailWord_8330481, baseEnd_8330481] using wordTrace_append hprefix tailTrace_8330481
  have hstable : (prefixWord ++ tailWord_8330481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330481).length < 2 ^ (prefixWord ++ tailWord_8330481).sum := by decide
  have hdescent : baseEnd_8330481 < baseStart_8330481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330548 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_8330548 : Nat := 118140960795 + 8330548 * 2 ^ 59
def prefixEnd_8330548 : Nat := 4983230072969 + 3 ^ 40 * 8330548 * 2
def baseEnd_8330548 : Nat := 4277575239351177926338513

theorem tailTrace_8330548 : CollatzResearch.WordTrace tailWord_8330548 prefixEnd_8330548 4277575239351177926338513 := by
  unfold tailWord_8330548
  simp only [CollatzResearch.WordTrace]
  refine ⟨151920023511927407586524149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202560031349236543448698865 151920023511927407586524149)
  ·
    refine ⟨14242502204243194461236639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151920023511927407586524149 14242502204243194461236639)
    ·
      refine ⟨21363753306364791691854959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14242502204243194461236639 21363753306364791691854959)
      ·
        refine ⟨32045629959547187537782439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21363753306364791691854959 32045629959547187537782439)
        ·
          refine ⟨48068444939320781306673659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32045629959547187537782439 48068444939320781306673659)
          ·
            refine ⟨72102667408981171960010489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48068444939320781306673659 72102667408981171960010489)
            ·
              refine ⟨54077000556735878970007867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72102667408981171960010489 54077000556735878970007867)
              ·
                refine ⟨81115500835103818455011801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54077000556735878970007867 81115500835103818455011801)
                ·
                  refine ⟨60836625626327863841258851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81115500835103818455011801 60836625626327863841258851)
                  ·
                    refine ⟨91254938439491795761888277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60836625626327863841258851 91254938439491795761888277)
                    ·
                      refine ⟨4277575239351177926338513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91254938439491795761888277 4277575239351177926338513)
                      ·
                        rfl

theorem cell23_8330548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_8330548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330548 prefixEnd_8330548 := by exact prefixLift 8330548
  have htrace : WordTrace (prefixWord ++ tailWord_8330548) baseStart_8330548 baseEnd_8330548 := by
    simpa [prefixWord, tailWord_8330548, baseEnd_8330548] using wordTrace_append hprefix tailTrace_8330548
  have hstable : (prefixWord ++ tailWord_8330548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330548).length < 2 ^ (prefixWord ++ tailWord_8330548).sum := by decide
  have hdescent : baseEnd_8330548 < baseStart_8330548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330589 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8330589 : Nat := 118140960795 + 8330589 * 2 ^ 59
def prefixEnd_8330589 : Nat := 4983230072969 + 3 ^ 40 * 8330589 * 2
def baseEnd_8330589 : Nat := 4277596292058012265925825

theorem tailTrace_8330589 : CollatzResearch.WordTrace tailWord_8330589 prefixEnd_8330589 4277596292058012265925825 := by
  unfold tailWord_8330589
  simp only [CollatzResearch.WordTrace]
  refine ⟨303841542416706279175290821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202561028277804186116860547 303841542416706279175290821)
  ·
    refine ⟨56970289203132427345367029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303841542416706279175290821 56970289203132427345367029)
    ·
      refine ⟨5340964612793665063628159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56970289203132427345367029 5340964612793665063628159)
      ·
        refine ⟨8011446919190497595442239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5340964612793665063628159 8011446919190497595442239)
        ·
          refine ⟨12017170378785746393163359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8011446919190497595442239 12017170378785746393163359)
          ·
            refine ⟨18025755568178619589745039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12017170378785746393163359 18025755568178619589745039)
            ·
              refine ⟨27038633352267929384617559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18025755568178619589745039 27038633352267929384617559)
              ·
                refine ⟨40557950028401894076926339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27038633352267929384617559 40557950028401894076926339)
                ·
                  refine ⟨60836925042602841115389509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40557950028401894076926339 60836925042602841115389509)
                  ·
                    refine ⟨11406923445488032709135533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60836925042602841115389509 11406923445488032709135533)
                    ·
                      refine ⟨4277596292058012265925825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11406923445488032709135533 4277596292058012265925825)
                      ·
                        rfl

theorem cell23_8330589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8330589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330589 prefixEnd_8330589 := by exact prefixLift 8330589
  have htrace : WordTrace (prefixWord ++ tailWord_8330589) baseStart_8330589 baseEnd_8330589 := by
    simpa [prefixWord, tailWord_8330589, baseEnd_8330589] using wordTrace_append hprefix tailTrace_8330589
  have hstable : (prefixWord ++ tailWord_8330589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330589).length < 2 ^ (prefixWord ++ tailWord_8330589).sum := by decide
  have hdescent : baseEnd_8330589 < baseStart_8330589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330595 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 1, 5, 2]
def baseStart_8330595 : Nat := 118140960795 + 8330595 * 2 ^ 59
def prefixEnd_8330595 : Nat := 4983230072969 + 3 ^ 40 * 8330595 * 2
def baseEnd_8330595 : Nat := 4277599372941939242450797

theorem tailTrace_8330595 : CollatzResearch.WordTrace tailWord_8330595 prefixEnd_8330595 4277599372941939242450797 := by
  unfold tailWord_8330595
  simp only [CollatzResearch.WordTrace]
  refine ⟨303841761254684542200009239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202561174169789694800006159 303841761254684542200009239)
  ·
    refine ⟨455762641882026813300013859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303841761254684542200009239 455762641882026813300013859)
    ·
      refine ⟨683643962823040219950020789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455762641882026813300013859 683643962823040219950020789)
      ·
        refine ⟨64091621514660020620314449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 683643962823040219950020789 64091621514660020620314449)
        ·
          refine ⟨48068716135995015465235837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64091621514660020620314449 48068716135995015465235837)
          ·
            refine ⟨18025768550998130799463439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48068716135995015465235837 18025768550998130799463439)
            ·
              refine ⟨27038652826497196199195159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18025768550998130799463439 27038652826497196199195159)
              ·
                refine ⟨40557979239745794298792739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27038652826497196199195159 40557979239745794298792739)
                ·
                  refine ⟨60836968859618691448189109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40557979239745794298792739 60836968859618691448189109)
                  ·
                    refine ⟨5703465830589252323267729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60836968859618691448189109 5703465830589252323267729)
                    ·
                      refine ⟨4277599372941939242450797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703465830589252323267729 4277599372941939242450797)
                      ·
                        rfl

theorem cell23_8330595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_8330595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330595 prefixEnd_8330595 := by exact prefixLift 8330595
  have htrace : WordTrace (prefixWord ++ tailWord_8330595) baseStart_8330595 baseEnd_8330595 := by
    simpa [prefixWord, tailWord_8330595, baseEnd_8330595] using wordTrace_append hprefix tailTrace_8330595
  have hstable : (prefixWord ++ tailWord_8330595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330595).length < 2 ^ (prefixWord ++ tailWord_8330595).sum := by decide
  have hdescent : baseEnd_8330595 < baseStart_8330595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330601 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 3, 6]
def baseStart_8330601 : Nat := 118140960795 + 8330601 * 2 ^ 59
def prefixEnd_8330601 : Nat := 4983230072969 + 3 ^ 40 * 8330601 * 2
def baseEnd_8330601 : Nat := 1425867484608622072991923

theorem tailTrace_8330601 : CollatzResearch.WordTrace tailWord_8330601 prefixEnd_8330601 1425867484608622072991923 := by
  unfold tailWord_8330601
  simp only [CollatzResearch.WordTrace]
  refine ⟨303841980092662805224727657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202561320061775203483151771 303841980092662805224727657)
  ·
    refine ⟨227881485069497103918545743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303841980092662805224727657 227881485069497103918545743)
    ·
      refine ⟨341822227604245655877818615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227881485069497103918545743 341822227604245655877818615)
      ·
        refine ⟨512733341406368483816727923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341822227604245655877818615 512733341406368483816727923)
        ·
          refine ⟨769100012109552725725091885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512733341406368483816727923 769100012109552725725091885)
          ·
            refine ⟨288412504541082272146909457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 769100012109552725725091885 288412504541082272146909457)
            ·
              refine ⟨216309378405811704110182093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288412504541082272146909457 216309378405811704110182093)
              ·
                refine ⟨81116016902179389041318285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216309378405811704110182093 81116016902179389041318285)
                ·
                  refine ⟨30418506338317270890494357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81116016902179389041318285 30418506338317270890494357)
                  ·
                    refine ⟨1425867484608622072991923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30418506338317270890494357 1425867484608622072991923)
                    ·
                      rfl

theorem cell23_8330601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_8330601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330601 prefixEnd_8330601 := by exact prefixLift 8330601
  have htrace : WordTrace (prefixWord ++ tailWord_8330601) baseStart_8330601 baseEnd_8330601 := by
    simpa [prefixWord, tailWord_8330601, baseEnd_8330601] using wordTrace_append hprefix tailTrace_8330601
  have hstable : (prefixWord ++ tailWord_8330601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330601).length < 2 ^ (prefixWord ++ tailWord_8330601).sum := by decide
  have hdescent : baseEnd_8330601 < baseStart_8330601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330605 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_8330605 : Nat := 118140960795 + 8330605 * 2 ^ 59
def prefixEnd_8330605 : Nat := 4983230072969 + 3 ^ 40 * 8330605 * 2
def baseEnd_8330605 : Nat := 1425868169249494734441917

theorem tailTrace_8330605 : CollatzResearch.WordTrace tailWord_8330605 prefixEnd_8330605 1425868169249494734441917 := by
  unfold tailWord_8330605
  simp only [CollatzResearch.WordTrace]
  refine ⟨303842125984648313907873269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202561417323098875938582179 303842125984648313907873269)
  ·
    refine ⟨28485199311060779428863119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303842125984648313907873269 28485199311060779428863119)
    ·
      refine ⟨42727798966591169143294679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28485199311060779428863119 42727798966591169143294679)
      ·
        refine ⟨64091698449886753714942019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42727798966591169143294679 64091698449886753714942019)
        ·
          refine ⟨96137547674830130572413029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64091698449886753714942019 96137547674830130572413029)
          ·
            refine ⟨18025790189030649482327443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96137547674830130572413029 18025790189030649482327443)
            ·
              refine ⟨27038685283545974223491165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18025790189030649482327443 27038685283545974223491165)
              ·
                refine ⟨10139506981329740333809187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27038685283545974223491165 10139506981329740333809187)
                ·
                  refine ⟨15209260471994610500713781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139506981329740333809187 15209260471994610500713781)
                  ·
                    refine ⟨1425868169249494734441917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15209260471994610500713781 1425868169249494734441917)
                    ·
                      rfl

theorem cell23_8330605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_8330605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330605 prefixEnd_8330605 := by exact prefixLift 8330605
  have htrace : WordTrace (prefixWord ++ tailWord_8330605) baseStart_8330605 baseEnd_8330605 := by
    simpa [prefixWord, tailWord_8330605, baseEnd_8330605] using wordTrace_append hprefix tailTrace_8330605
  have hstable : (prefixWord ++ tailWord_8330605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330605).length < 2 ^ (prefixWord ++ tailWord_8330605).sum := by decide
  have hdescent : baseEnd_8330605 < baseStart_8330605 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330618 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_8330618 : Nat := 118140960795 + 8330618 * 2 ^ 59
def prefixEnd_8330618 : Nat := 4983230072969 + 3 ^ 40 * 8330618 * 2
def baseEnd_8330618 : Nat := 1425870394332330884154397

theorem tailTrace_8330618 : CollatzResearch.WordTrace tailWord_8330618 prefixEnd_8330618 1425870394332330884154397 := by
  unfold tailWord_8330618
  simp only [CollatzResearch.WordTrace]
  refine ⟨75960650033400304282024127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202561733422400811418731005 75960650033400304282024127)
  ·
    refine ⟨113940975050100456423036191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75960650033400304282024127 113940975050100456423036191)
    ·
      refine ⟨170911462575150684634554287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113940975050100456423036191 170911462575150684634554287)
      ·
        refine ⟨256367193862726026951831431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170911462575150684634554287 256367193862726026951831431)
        ·
          refine ⟨384550790794089040427747147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256367193862726026951831431 384550790794089040427747147)
          ·
            refine ⟨576826186191133560641620721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384550790794089040427747147 576826186191133560641620721)
            ·
              refine ⟨432619639643350170481215541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576826186191133560641620721 432619639643350170481215541)
              ·
                refine ⟨40558091216564078482613957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432619639643350170481215541 40558091216564078482613957)
                ·
                  refine ⟨7604642103105764715490117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40558091216564078482613957 7604642103105764715490117)
                  ·
                    refine ⟨1425870394332330884154397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7604642103105764715490117 1425870394332330884154397)
                    ·
                      rfl

theorem cell23_8330618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_8330618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330618 prefixEnd_8330618 := by exact prefixLift 8330618
  have htrace : WordTrace (prefixWord ++ tailWord_8330618) baseStart_8330618 baseEnd_8330618 := by
    simpa [prefixWord, tailWord_8330618, baseEnd_8330618] using wordTrace_append hprefix tailTrace_8330618
  have hstable : (prefixWord ++ tailWord_8330618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330618).length < 2 ^ (prefixWord ++ tailWord_8330618).sum := by decide
  have hdescent : baseEnd_8330618 < baseStart_8330618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330628 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_8330628 : Nat := 118140960795 + 8330628 * 2 ^ 59
def prefixEnd_8330628 : Nat := 4983230072969 + 3 ^ 40 * 8330628 * 2
def baseEnd_8330628 : Nat := 4277616317803537613338145

theorem tailTrace_8330628 : CollatzResearch.WordTrace tailWord_8330628 prefixEnd_8330628 4277616317803537613338145 := by
  unfold tailWord_8330628
  simp only [CollatzResearch.WordTrace]
  refine ⟨151921482431782494417980269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202561976575709992557307025 151921482431782494417980269)
  ·
    refine ⟨56970555911918435406742601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151921482431782494417980269 56970555911918435406742601)
    ·
      refine ⟨42727916933938826555056951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56970555911918435406742601 42727916933938826555056951)
      ·
        refine ⟨64091875400908239832585427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42727916933938826555056951 64091875400908239832585427)
        ·
          refine ⟨96137813101362359748878141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64091875400908239832585427 96137813101362359748878141)
          ·
            refine ⟨36051679913010884905829303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96137813101362359748878141 36051679913010884905829303)
            ·
              refine ⟨54077519869516327358743955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36051679913010884905829303 54077519869516327358743955)
              ·
                refine ⟨81116279804274491038115933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54077519869516327358743955 81116279804274491038115933)
                ·
                  refine ⟨30418604926602934139293475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81116279804274491038115933 30418604926602934139293475)
                  ·
                    refine ⟨45627907389904401208940213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30418604926602934139293475 45627907389904401208940213)
                    ·
                      refine ⟨4277616317803537613338145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45627907389904401208940213 4277616317803537613338145)
                      ·
                        rfl

theorem cell23_8330628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_8330628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330628 prefixEnd_8330628 := by exact prefixLift 8330628
  have htrace : WordTrace (prefixWord ++ tailWord_8330628) baseStart_8330628 baseEnd_8330628 := by
    simpa [prefixWord, tailWord_8330628, baseEnd_8330628] using wordTrace_append hprefix tailTrace_8330628
  have hstable : (prefixWord ++ tailWord_8330628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330628).length < 2 ^ (prefixWord ++ tailWord_8330628).sum := by decide
  have hdescent : baseEnd_8330628 < baseStart_8330628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330641 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_8330641 : Nat := 118140960795 + 8330641 * 2 ^ 59
def prefixEnd_8330641 : Nat := 4983230072969 + 3 ^ 40 * 8330641 * 2
def baseEnd_8330641 : Nat := 4277622993052046062475585

theorem tailTrace_8330641 : CollatzResearch.WordTrace tailWord_8330641 prefixEnd_8330641 4277622993052046062475585 := by
  unfold tailWord_8330641
  simp only [CollatzResearch.WordTrace]
  refine ⟨303843439012517892056183777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202562292675011928037455851 303843439012517892056183777)
  ·
    refine ⟨227882579259388419042137833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303843439012517892056183777 227882579259388419042137833)
    ·
      refine ⟨170911934444541314281603375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227882579259388419042137833 170911934444541314281603375)
      ·
        refine ⟨256367901666811971422405063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170911934444541314281603375 256367901666811971422405063)
        ·
          refine ⟨384551852500217957133607595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256367901666811971422405063 384551852500217957133607595)
          ·
            refine ⟨576827778750326935700411393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384551852500217957133607595 576827778750326935700411393)
            ·
              refine ⟨432620834062745201775308545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576827778750326935700411393 432620834062745201775308545)
              ·
                refine ⟨324465625547058901331481409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432620834062745201775308545 324465625547058901331481409)
                ·
                  refine ⟨243349219160294175998611057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 324465625547058901331481409 243349219160294175998611057)
                  ·
                    refine ⟨182511914370220631998958293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 243349219160294175998611057 182511914370220631998958293)
                    ·
                      refine ⟨4277622993052046062475585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182511914370220631998958293 4277622993052046062475585)
                      ·
                        rfl

theorem cell23_8330641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_8330641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330641 prefixEnd_8330641 := by exact prefixLift 8330641
  have htrace : WordTrace (prefixWord ++ tailWord_8330641) baseStart_8330641 baseEnd_8330641 := by
    simpa [prefixWord, tailWord_8330641, baseEnd_8330641] using wordTrace_append hprefix tailTrace_8330641
  have hstable : (prefixWord ++ tailWord_8330641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330641).length < 2 ^ (prefixWord ++ tailWord_8330641).sum := by decide
  have hdescent : baseEnd_8330641 < baseStart_8330641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330645 : List Nat := [1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 3]
def baseStart_8330645 : Nat := 118140960795 + 8330645 * 2 ^ 59
def prefixEnd_8330645 : Nat := 4983230072969 + 3 ^ 40 * 8330645 * 2
def baseEnd_8330645 : Nat := 4277625046974664046825567

theorem tailTrace_8330645 : CollatzResearch.WordTrace tailWord_8330645 prefixEnd_8330645 4277625046974664046825567 := by
  unfold tailWord_8330645
  simp only [CollatzResearch.WordTrace]
  refine ⟨303843584904503400739329389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202562389936335600492886259 303843584904503400739329389)
  ·
    refine ⟨113941344339188775277248521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303843584904503400739329389 113941344339188775277248521)
    ·
      refine ⟨85456008254391581457936391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113941344339188775277248521 85456008254391581457936391)
      ·
        refine ⟨128184012381587372186904587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85456008254391581457936391 128184012381587372186904587)
        ·
          refine ⟨192276018572381058280356881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128184012381587372186904587 192276018572381058280356881)
          ·
            refine ⟨144207013929285793710267661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192276018572381058280356881 144207013929285793710267661)
            ·
              refine ⟨54077630223482172641350373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144207013929285793710267661 54077630223482172641350373)
              ·
                refine ⟨10139555666902907370253195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54077630223482172641350373 10139555666902907370253195)
                ·
                  refine ⟨15209333500354361055379793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139555666902907370253195 15209333500354361055379793)
                  ·
                    refine ⟨11407000125265770791534845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15209333500354361055379793 11407000125265770791534845)
                    ·
                      refine ⟨4277625046974664046825567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11407000125265770791534845 4277625046974664046825567)
                      ·
                        rfl

theorem cell23_8330645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_8330645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330645 prefixEnd_8330645 := by exact prefixLift 8330645
  have htrace : WordTrace (prefixWord ++ tailWord_8330645) baseStart_8330645 baseEnd_8330645 := by
    simpa [prefixWord, tailWord_8330645, baseEnd_8330645] using wordTrace_append hprefix tailTrace_8330645
  have hstable : (prefixWord ++ tailWord_8330645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330645).length < 2 ^ (prefixWord ++ tailWord_8330645).sum := by decide
  have hdescent : baseEnd_8330645 < baseStart_8330645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330651 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6]
def baseStart_8330651 : Nat := 118140960795 + 8330651 * 2 ^ 59
def prefixEnd_8330651 : Nat := 4983230072969 + 3 ^ 40 * 8330651 * 2
def baseEnd_8330651 : Nat := 4277628127858591023350539

theorem tailTrace_8330651 : CollatzResearch.WordTrace tailWord_8330651 prefixEnd_8330651 4277628127858591023350539 := by
  unfold tailWord_8330651
  simp only [CollatzResearch.WordTrace]
  refine ⟨303843803742481663764047807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202562535828321109176031871 303843803742481663764047807)
  ·
    refine ⟨455765705613722495646071711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303843803742481663764047807 455765705613722495646071711)
    ·
      refine ⟨683648558420583743469107567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455765705613722495646071711 683648558420583743469107567)
      ·
        refine ⟨1025472837630875615203661351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683648558420583743469107567 1025472837630875615203661351)
        ·
          refine ⟨1538209256446313422805492027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025472837630875615203661351 1538209256446313422805492027)
          ·
            refine ⟨2307313884669470134208238041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538209256446313422805492027 2307313884669470134208238041)
            ·
              refine ⟨1730485413502102600656178531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2307313884669470134208238041 1730485413502102600656178531)
              ·
                refine ⟨2595728120253153900984267797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730485413502102600656178531 2595728120253153900984267797)
                ·
                  refine ⟨121674755636866589108637553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2595728120253153900984267797 121674755636866589108637553)
                  ·
                    refine ⟨91256066727649941831478165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121674755636866589108637553 91256066727649941831478165)
                    ·
                      refine ⟨4277628127858591023350539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91256066727649941831478165 4277628127858591023350539)
                      ·
                        rfl

theorem cell23_8330651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_8330651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330651 prefixEnd_8330651 := by exact prefixLift 8330651
  have htrace : WordTrace (prefixWord ++ tailWord_8330651) baseStart_8330651 baseEnd_8330651 := by
    simpa [prefixWord, tailWord_8330651, baseEnd_8330651] using wordTrace_append hprefix tailTrace_8330651
  have hstable : (prefixWord ++ tailWord_8330651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330651).length < 2 ^ (prefixWord ++ tailWord_8330651).sum := by decide
  have hdescent : baseEnd_8330651 < baseStart_8330651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330690 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_8330690 : Nat := 118140960795 + 8330690 * 2 ^ 59
def prefixEnd_8330690 : Nat := 4983230072969 + 3 ^ 40 * 8330690 * 2
def baseEnd_8330690 : Nat := 1425882717868038790254287

theorem tailTrace_8330690 : CollatzResearch.WordTrace tailWord_8330690 prefixEnd_8330690 1425882717868038790254287 := by
  unfold tailWord_8330690
  simp only [CollatzResearch.WordTrace]
  refine ⟨75961306547335093356179381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202563484126226915616478349 75961306547335093356179381)
  ·
    refine ⟨7121372488812665002141817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75961306547335093356179381 7121372488812665002141817)
    ·
      refine ⟨5341029366609498751606363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7121372488812665002141817 5341029366609498751606363)
      ·
        refine ⟨8011544049914248127409545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5341029366609498751606363 8011544049914248127409545)
        ·
          refine ⟨6008658037435686095557159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8011544049914248127409545 6008658037435686095557159)
          ·
            refine ⟨9012987056153529143335739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008658037435686095557159 9012987056153529143335739)
            ·
              refine ⟨13519480584230293715003609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9012987056153529143335739 13519480584230293715003609)
              ·
                refine ⟨10139610438172720286252707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13519480584230293715003609 10139610438172720286252707)
                ·
                  refine ⟨15209415657259080429379061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139610438172720286252707 15209415657259080429379061)
                  ·
                    refine ⟨1425882717868038790254287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15209415657259080429379061 1425882717868038790254287)
                    ·
                      rfl

theorem cell23_8330690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_8330690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330690 prefixEnd_8330690 := by exact prefixLift 8330690
  have htrace : WordTrace (prefixWord ++ tailWord_8330690) baseStart_8330690 baseEnd_8330690 := by
    simpa [prefixWord, tailWord_8330690, baseEnd_8330690] using wordTrace_append hprefix tailTrace_8330690
  have hstable : (prefixWord ++ tailWord_8330690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330690).length < 2 ^ (prefixWord ++ tailWord_8330690).sum := by decide
  have hdescent : baseEnd_8330690 < baseStart_8330690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330719 : List Nat := [1, 1, 2, 3, 3, 1, 5, 1, 1, 3, 2]
def baseStart_8330719 : Nat := 118140960795 + 8330719 * 2 ^ 59
def prefixEnd_8330719 : Nat := 4983230072969 + 3 ^ 40 * 8330719 * 2
def baseEnd_8330719 : Nat := 4277663044543096757300227

theorem tailTrace_8330719 : CollatzResearch.WordTrace tailWord_8330719 prefixEnd_8330719 4277663044543096757300227 := by
  unfold tailWord_8330719
  simp only [CollatzResearch.WordTrace]
  refine ⟨303846283906235311377523211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202564189270823540918348807 303846283906235311377523211)
  ·
    refine ⟨455769425859352967066284817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303846283906235311377523211 455769425859352967066284817)
    ·
      refine ⟨341827069394514725299713613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455769425859352967066284817 341827069394514725299713613)
      ·
        refine ⟨128185151022943021987392605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341827069394514725299713613 128185151022943021987392605)
        ·
          refine ⟨48069431633603633245272227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128185151022943021987392605 48069431633603633245272227)
          ·
            refine ⟨72104147450405449867908341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48069431633603633245272227 72104147450405449867908341)
            ·
              refine ⟨6759763823475510925116407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72104147450405449867908341 6759763823475510925116407)
              ·
                refine ⟨10139645735213266387674611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6759763823475510925116407 10139645735213266387674611)
                ·
                  refine ⟨15209468602819899581511917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139645735213266387674611 15209468602819899581511917)
                  ·
                    refine ⟨5703550726057462343066969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15209468602819899581511917 5703550726057462343066969)
                    ·
                      refine ⟨4277663044543096757300227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703550726057462343066969 4277663044543096757300227)
                      ·
                        rfl

theorem cell23_8330719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_8330719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330719 prefixEnd_8330719 := by exact prefixLift 8330719
  have htrace : WordTrace (prefixWord ++ tailWord_8330719) baseStart_8330719 baseEnd_8330719 := by
    simpa [prefixWord, tailWord_8330719, baseEnd_8330719] using wordTrace_append hprefix tailTrace_8330719
  have hstable : (prefixWord ++ tailWord_8330719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330719).length < 2 ^ (prefixWord ++ tailWord_8330719).sum := by decide
  have hdescent : baseEnd_8330719 < baseStart_8330719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330749 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_8330749 : Nat := 118140960795 + 8330749 * 2 ^ 59
def prefixEnd_8330749 : Nat := 4983230072969 + 3 ^ 40 * 8330749 * 2
def baseEnd_8330749 : Nat := 4277678448962731639925089

theorem tailTrace_8330749 : CollatzResearch.WordTrace tailWord_8330749 prefixEnd_8330749 4277678448962731639925089 := by
  unfold tailWord_8330749
  simp only [CollatzResearch.WordTrace]
  refine ⟨303847378096126626501115301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202564918730751084334076867 303847378096126626501115301)
  ·
    refine ⟨56971383393023742468959119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303847378096126626501115301 56971383393023742468959119)
    ·
      refine ⟨85457075089535613703438679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56971383393023742468959119 85457075089535613703438679)
      ·
        refine ⟨128185612634303420555158019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85457075089535613703438679 128185612634303420555158019)
        ·
          refine ⟨192278418951455130832737029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128185612634303420555158019 192278418951455130832737029)
          ·
            refine ⟨36052203553397837031138193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192278418951455130832737029 36052203553397837031138193)
            ·
              refine ⟨27039152665048377773353645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36052203553397837031138193 27039152665048377773353645)
              ·
                refine ⟨10139682249393141665007617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27039152665048377773353645 10139682249393141665007617)
                ·
                  refine ⟨7604761687044856248755713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10139682249393141665007617 7604761687044856248755713)
                  ·
                    refine ⟨5703571265283642186566785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7604761687044856248755713 5703571265283642186566785)
                    ·
                      refine ⟨4277678448962731639925089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703571265283642186566785 4277678448962731639925089)
                      ·
                        rfl

theorem cell23_8330749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_8330749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330749 prefixEnd_8330749 := by exact prefixLift 8330749
  have htrace : WordTrace (prefixWord ++ tailWord_8330749) baseStart_8330749 baseEnd_8330749 := by
    simpa [prefixWord, tailWord_8330749, baseEnd_8330749] using wordTrace_append hprefix tailTrace_8330749
  have hstable : (prefixWord ++ tailWord_8330749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330749).length < 2 ^ (prefixWord ++ tailWord_8330749).sum := by decide
  have hdescent : baseEnd_8330749 < baseStart_8330749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330805 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 4]
def baseStart_8330805 : Nat := 118140960795 + 8330805 * 2 ^ 59
def prefixEnd_8330805 : Nat := 4983230072969 + 3 ^ 40 * 8330805 * 2
def baseEnd_8330805 : Nat := 4277707203879383420824831

theorem tailTrace_8330805 : CollatzResearch.WordTrace tailWord_8330805 prefixEnd_8330805 4277707203879383420824831 := by
  unfold tailWord_8330805
  simp only [CollatzResearch.WordTrace]
  refine ⟨303849420583923748065153869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202566280389282498710102579 303849420583923748065153869)
  ·
    refine ⟨113943532718971405524432701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303849420583923748065153869 113943532718971405524432701)
    ·
      refine ⟨42728824769614277071662263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113943532718971405524432701 42728824769614277071662263)
      ·
        refine ⟨64093237154421415607493395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42728824769614277071662263 64093237154421415607493395)
        ·
          refine ⟨96139855731632123411240093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64093237154421415607493395 96139855731632123411240093)
          ·
            refine ⟨36052445899362046279215035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96139855731632123411240093 36052445899362046279215035)
            ·
              refine ⟨54078668849043069418822553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36052445899362046279215035 54078668849043069418822553)
              ·
                refine ⟨40559001636782302064116915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54078668849043069418822553 40559001636782302064116915)
                ·
                  refine ⟨60838502455173453096175373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40559001636782302064116915 60838502455173453096175373)
                  ·
                    refine ⟨22814438420690044911065765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60838502455173453096175373 22814438420690044911065765)
                    ·
                      refine ⟨4277707203879383420824831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22814438420690044911065765 4277707203879383420824831)
                      ·
                        rfl

theorem cell23_8330805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_8330805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330805 prefixEnd_8330805 := by exact prefixLift 8330805
  have htrace : WordTrace (prefixWord ++ tailWord_8330805) baseStart_8330805 baseEnd_8330805 := by
    simpa [prefixWord, tailWord_8330805, baseEnd_8330805] using wordTrace_append hprefix tailTrace_8330805
  have hstable : (prefixWord ++ tailWord_8330805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330805).length < 2 ^ (prefixWord ++ tailWord_8330805).sum := by decide
  have hdescent : baseEnd_8330805 < baseStart_8330805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330825 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 3]
def baseStart_8330825 : Nat := 118140960795 + 8330825 * 2 ^ 59
def prefixEnd_8330825 : Nat := 4983230072969 + 3 ^ 40 * 8330825 * 2
def baseEnd_8330825 : Nat := 4277717473492473342574739

theorem tailTrace_8330825 : CollatzResearch.WordTrace tailWord_8330825 prefixEnd_8330825 4277717473492473342574739 := by
  unfold tailWord_8330825
  simp only [CollatzResearch.WordTrace]
  refine ⟨303850150043851291480881929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202566766695900860987254619 303850150043851291480881929)
  ·
    refine ⟨227887612532888468610661447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303850150043851291480881929 227887612532888468610661447)
    ·
      refine ⟨341831418799332702915992171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227887612532888468610661447 341831418799332702915992171)
      ·
        refine ⟨512747128198999054373988257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341831418799332702915992171 512747128198999054373988257)
        ·
          refine ⟨384560346149249290780491193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512747128198999054373988257 384560346149249290780491193)
          ·
            refine ⟨288420259611936968085368395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384560346149249290780491193 288420259611936968085368395)
            ·
              refine ⟨432630389417905452128052593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288420259611936968085368395 432630389417905452128052593)
              ·
                refine ⟨324472792063429089096039445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432630389417905452128052593 324472792063429089096039445)
                ·
                  refine ⟨15209662127973238551376849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 324472792063429089096039445 15209662127973238551376849)
                  ·
                    refine ⟨11407246595979928913532637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15209662127973238551376849 11407246595979928913532637)
                    ·
                      refine ⟨4277717473492473342574739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11407246595979928913532637 4277717473492473342574739)
                      ·
                        rfl

theorem cell23_8330825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_8330825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330825 prefixEnd_8330825 := by exact prefixLift 8330825
  have htrace : WordTrace (prefixWord ++ tailWord_8330825) baseStart_8330825 baseEnd_8330825 := by
    simpa [prefixWord, tailWord_8330825, baseEnd_8330825] using wordTrace_append hprefix tailTrace_8330825
  have hstable : (prefixWord ++ tailWord_8330825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330825).length < 2 ^ (prefixWord ++ tailWord_8330825).sum := by decide
  have hdescent : baseEnd_8330825 < baseStart_8330825 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330875 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 3, 5]
def baseStart_8330875 : Nat := 118140960795 + 8330875 * 2 ^ 59
def prefixEnd_8330875 : Nat := 4983230072969 + 3 ^ 40 * 8330875 * 2
def baseEnd_8330875 : Nat := 1425914382508399382316503

theorem tailTrace_8330875 : CollatzResearch.WordTrace tailWord_8330875 prefixEnd_8330875 1425914382508399382316503 := by
  unfold tailWord_8330875
  simp only [CollatzResearch.WordTrace]
  refine ⟨303851973693670150020202079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202567982462446766680134719 303851973693670150020202079)
  ·
    refine ⟨455777960540505225030303119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303851973693670150020202079 455777960540505225030303119)
    ·
      refine ⟨683666940810757837545454679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455777960540505225030303119 683666940810757837545454679)
      ·
        refine ⟨1025500411216136756318182019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683666940810757837545454679 1025500411216136756318182019)
        ·
          refine ⟨1538250616824205134477273029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025500411216136756318182019 1538250616824205134477273029)
          ·
            refine ⟨288421990654538462714488693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1538250616824205134477273029 288421990654538462714488693)
            ·
              refine ⟨27039561623862980879483315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 288421990654538462714488693 27039561623862980879483315)
              ·
                refine ⟨40559342435794471319224973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27039561623862980879483315 40559342435794471319224973)
                ·
                  refine ⟨15209753413422926744709365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40559342435794471319224973 15209753413422926744709365)
                  ·
                    refine ⟨1425914382508399382316503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15209753413422926744709365 1425914382508399382316503)
                    ·
                      rfl

theorem cell23_8330875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 5].length) (baseStart_8330875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330875 prefixEnd_8330875 := by exact prefixLift 8330875
  have htrace : WordTrace (prefixWord ++ tailWord_8330875) baseStart_8330875 baseEnd_8330875 := by
    simpa [prefixWord, tailWord_8330875, baseEnd_8330875] using wordTrace_append hprefix tailTrace_8330875
  have hstable : (prefixWord ++ tailWord_8330875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330875).length < 2 ^ (prefixWord ++ tailWord_8330875).sum := by decide
  have hdescent : baseEnd_8330875 < baseStart_8330875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330895 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 4]
def baseStart_8330895 : Nat := 118140960795 + 8330895 * 2 ^ 59
def prefixEnd_8330895 : Nat := 4983230072969 + 3 ^ 40 * 8330895 * 2
def baseEnd_8330895 : Nat := 4277753417138288068699417

theorem tailTrace_8330895 : CollatzResearch.WordTrace tailWord_8330895 prefixEnd_8330895 4277753417138288068699417 := by
  unfold tailWord_8330895
  simp only [CollatzResearch.WordTrace]
  refine ⟨303852703153597693435930139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202568468769065128957286759 303852703153597693435930139)
  ·
    refine ⟨455779054730396540153895209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303852703153597693435930139 455779054730396540153895209)
    ·
      refine ⟨341834291047797405115421407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455779054730396540153895209 341834291047797405115421407)
      ·
        refine ⟨512751436571696107673132111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341834291047797405115421407 512751436571696107673132111)
        ·
          refine ⟨769127154857544161509698167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512751436571696107673132111 769127154857544161509698167)
          ·
            refine ⟨1153690732286316242264547251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769127154857544161509698167 1153690732286316242264547251)
            ·
              refine ⟨1730536098429474363396820877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153690732286316242264547251 1730536098429474363396820877)
              ·
                refine ⟨648951036911052886273807829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1730536098429474363396820877 648951036911052886273807829)
                ·
                  refine ⟨15209789927602802022042371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 648951036911052886273807829 15209789927602802022042371)
                  ·
                    refine ⟨22814684891404203033063557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15209789927602802022042371 22814684891404203033063557)
                    ·
                      refine ⟨4277753417138288068699417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22814684891404203033063557 4277753417138288068699417)
                      ·
                        rfl

theorem cell23_8330895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_8330895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330895 prefixEnd_8330895 := by exact prefixLift 8330895
  have htrace : WordTrace (prefixWord ++ tailWord_8330895) baseStart_8330895 baseEnd_8330895 := by
    simpa [prefixWord, tailWord_8330895, baseEnd_8330895] using wordTrace_append hprefix tailTrace_8330895
  have hstable : (prefixWord ++ tailWord_8330895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330895).length < 2 ^ (prefixWord ++ tailWord_8330895).sum := by decide
  have hdescent : baseEnd_8330895 < baseStart_8330895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330900 : List Nat := [2, 4, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_8330900 : Nat := 118140960795 + 8330900 * 2 ^ 59
def prefixEnd_8330900 : Nat := 4983230072969 + 3 ^ 40 * 8330900 * 2
def baseEnd_8330900 : Nat := 1425918661513853516378965

theorem tailTrace_8330900 : CollatzResearch.WordTrace tailWord_8330900 prefixEnd_8330900 1425918661513853516378965 := by
  unfold tailWord_8330900
  simp only [CollatzResearch.WordTrace]
  refine ⟨151926442759289789644931077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202568590345719719526574769 151926442759289789644931077)
  ·
    refine ⟨28486208017366835558424577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151926442759289789644931077 28486208017366835558424577)
    ·
      refine ⟨21364656013025126668818433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28486208017366835558424577 21364656013025126668818433)
      ·
        refine ⟨16023492009768845001613825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21364656013025126668818433 16023492009768845001613825)
        ·
          refine ⟨12017619007326633751210369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16023492009768845001613825 12017619007326633751210369)
          ·
            refine ⟨9013214255494975313407777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12017619007326633751210369 9013214255494975313407777)
            ·
              refine ⟨6759910691621231485055833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9013214255494975313407777 6759910691621231485055833)
              ·
                refine ⟨5069933018715923613791875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6759910691621231485055833 5069933018715923613791875)
                ·
                  refine ⟨7604899528073885420687813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5069933018715923613791875 7604899528073885420687813)
                  ·
                    refine ⟨1425918661513853516378965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7604899528073885420687813 1425918661513853516378965)
                    ·
                      rfl

theorem cell23_8330900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_8330900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330900 prefixEnd_8330900 := by exact prefixLift 8330900
  have htrace : WordTrace (prefixWord ++ tailWord_8330900) baseStart_8330900 baseEnd_8330900 := by
    simpa [prefixWord, tailWord_8330900, baseEnd_8330900] using wordTrace_append hprefix tailTrace_8330900
  have hstable : (prefixWord ++ tailWord_8330900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330900).length < 2 ^ (prefixWord ++ tailWord_8330900).sum := by decide
  have hdescent : baseEnd_8330900 < baseStart_8330900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330912 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_8330912 : Nat := 118140960795 + 8330912 * 2 ^ 59
def prefixEnd_8330912 : Nat := 4983230072969 + 3 ^ 40 * 8330912 * 2
def baseEnd_8330912 : Nat := 4277762146309414502186839

theorem tailTrace_8330912 : CollatzResearch.WordTrace tailWord_8330912 prefixEnd_8330912 4277762146309414502186839 := by
  unfold tailWord_8330912
  simp only [CollatzResearch.WordTrace]
  refine ⟨151926661597268052669649495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202568882129690736892865993 151926661597268052669649495)
  ·
    refine ⟨227889992395902079004474243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151926661597268052669649495 227889992395902079004474243)
    ·
      refine ⟨341834988593853118506711365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227889992395902079004474243 341834988593853118506711365)
      ·
        refine ⟨64094060361347459720008381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341834988593853118506711365 64094060361347459720008381)
        ·
          refine ⟨24035272635505297395003143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64094060361347459720008381 24035272635505297395003143)
          ·
            refine ⟨36052908953257946092504715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24035272635505297395003143 36052908953257946092504715)
            ·
              refine ⟨54079363429886919138757073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36052908953257946092504715 54079363429886919138757073)
              ·
                refine ⟨40559522572415189354067805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54079363429886919138757073 40559522572415189354067805)
                ·
                  refine ⟨15209820964655696007775427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40559522572415189354067805 15209820964655696007775427)
                  ·
                    refine ⟨22814731446983544011663141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15209820964655696007775427 22814731446983544011663141)
                    ·
                      refine ⟨4277762146309414502186839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22814731446983544011663141 4277762146309414502186839)
                      ·
                        rfl

theorem cell23_8330912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_8330912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330912 prefixEnd_8330912 := by exact prefixLift 8330912
  have htrace : WordTrace (prefixWord ++ tailWord_8330912) baseStart_8330912 baseEnd_8330912 := by
    simpa [prefixWord, tailWord_8330912, baseEnd_8330912] using wordTrace_append hprefix tailTrace_8330912
  have hstable : (prefixWord ++ tailWord_8330912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330912).length < 2 ^ (prefixWord ++ tailWord_8330912).sum := by decide
  have hdescent : baseEnd_8330912 < baseStart_8330912 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330915 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5]
def baseStart_8330915 : Nat := 118140960795 + 8330915 * 2 ^ 59
def prefixEnd_8330915 : Nat := 4983230072969 + 3 ^ 40 * 8330915 * 2
def baseEnd_8330915 : Nat := 4277763686751377990449325

theorem tailTrace_8330915 : CollatzResearch.WordTrace tailWord_8330915 prefixEnd_8330915 4277763686751377990449325 := by
  unfold tailWord_8330915
  simp only [CollatzResearch.WordTrace]
  refine ⟨303853432613525236851658199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202568955075683491234438799 303853432613525236851658199)
  ·
    refine ⟨455780148920287855277487299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303853432613525236851658199 455780148920287855277487299)
    ·
      refine ⟨683670223380431782916230949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455780148920287855277487299 683670223380431782916230949)
      ·
        refine ⟨128188166883830959296793303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 683670223380431782916230949 128188166883830959296793303)
        ·
          refine ⟨192282250325746438945189955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128188166883830959296793303 192282250325746438945189955)
          ·
            refine ⟨288423375488619658417784933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192282250325746438945189955 288423375488619658417784933)
            ·
              refine ⟨54079382904116185953334675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288423375488619658417784933 54079382904116185953334675)
              ·
                refine ⟨81119074356174278930002013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54079382904116185953334675 81119074356174278930002013)
                ·
                  refine ⟨30419652883565354598750755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81119074356174278930002013 30419652883565354598750755)
                  ·
                    refine ⟨45629479325348031898126133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30419652883565354598750755 45629479325348031898126133)
                    ·
                      refine ⟨4277763686751377990449325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45629479325348031898126133 4277763686751377990449325)
                      ·
                        rfl

theorem cell23_8330915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_8330915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330915 prefixEnd_8330915 := by exact prefixLift 8330915
  have htrace : WordTrace (prefixWord ++ tailWord_8330915) baseStart_8330915 baseEnd_8330915 := by
    simpa [prefixWord, tailWord_8330915, baseEnd_8330915] using wordTrace_append hprefix tailTrace_8330915
  have hstable : (prefixWord ++ tailWord_8330915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330915).length < 2 ^ (prefixWord ++ tailWord_8330915).sum := by decide
  have hdescent : baseEnd_8330915 < baseStart_8330915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330933 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 2, 3, 2]
def baseStart_8330933 : Nat := 118140960795 + 8330933 * 2 ^ 59
def prefixEnd_8330933 : Nat := 4983230072969 + 3 ^ 40 * 8330933 * 2
def baseEnd_8330933 : Nat := 4277772929403158920024243

theorem tailTrace_8330933 : CollatzResearch.WordTrace tailWord_8330933 prefixEnd_8330933 4277772929403158920024243 := by
  unfold tailWord_8330933
  simp only [CollatzResearch.WordTrace]
  refine ⟨303854089127460025925813453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202569392751640017283875635 303854089127460025925813453)
  ·
    refine ⟨113945283422797509722180045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303854089127460025925813453 113945283422797509722180045)
    ·
      refine ⟨42729481283549066145817517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113945283422797509722180045 42729481283549066145817517)
      ·
        refine ⟨16023555481330899804681569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42729481283549066145817517 16023555481330899804681569)
        ·
          refine ⟨12017666610998174853511177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16023555481330899804681569 12017666610998174853511177)
          ·
            refine ⟨9013249958248631140133383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12017666610998174853511177 9013249958248631140133383)
            ·
              refine ⟨13519874937372946710200075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9013249958248631140133383 13519874937372946710200075)
              ·
                refine ⟨20279812406059420065300113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13519874937372946710200075 20279812406059420065300113)
                ·
                  refine ⟨15209859304544565048975085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20279812406059420065300113 15209859304544565048975085)
                  ·
                    refine ⟨5703697239204211893365657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15209859304544565048975085 5703697239204211893365657)
                    ·
                      refine ⟨4277772929403158920024243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703697239204211893365657 4277772929403158920024243)
                      ·
                        rfl

theorem cell23_8330933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_8330933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330933 prefixEnd_8330933 := by exact prefixLift 8330933
  have htrace : WordTrace (prefixWord ++ tailWord_8330933) baseStart_8330933 baseEnd_8330933 := by
    simpa [prefixWord, tailWord_8330933, baseEnd_8330933] using wordTrace_append hprefix tailTrace_8330933
  have hstable : (prefixWord ++ tailWord_8330933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330933).length < 2 ^ (prefixWord ++ tailWord_8330933).sum := by decide
  have hdescent : baseEnd_8330933 < baseStart_8330933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330973 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_8330973 : Nat := 118140960795 + 8330973 * 2 ^ 59
def prefixEnd_8330973 : Nat := 4983230072969 + 3 ^ 40 * 8330973 * 2
def baseEnd_8330973 : Nat := 1425931156209779587841353

theorem tailTrace_8330973 : CollatzResearch.WordTrace tailWord_8330973 prefixEnd_8330973 1425931156209779587841353 := by
  unfold tailWord_8330973
  simp only [CollatzResearch.WordTrace]
  refine ⟨303855548047315112757269573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202570365364876741838179715 303855548047315112757269573)
  ·
    refine ⟨56972915258871583641988045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303855548047315112757269573 56972915258871583641988045)
    ·
      refine ⟨21364843222076843865745517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56972915258871583641988045 21364843222076843865745517)
      ·
        refine ⟨8011816208278816449654569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21364843222076843865745517 8011816208278816449654569)
        ·
          refine ⟨6008862156209112337240927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8011816208278816449654569 6008862156209112337240927)
          ·
            refine ⟨9013293234313668505861391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6008862156209112337240927 9013293234313668505861391)
            ·
              refine ⟨13519939851470502758792087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9013293234313668505861391 13519939851470502758792087)
              ·
                refine ⟨20279909777205754138188131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13519939851470502758792087 20279909777205754138188131)
                ·
                  refine ⟨30419864665808631207282197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20279909777205754138188131 30419864665808631207282197)
                  ·
                    refine ⟨1425931156209779587841353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30419864665808631207282197 1425931156209779587841353)
                    ·
                      rfl

theorem cell23_8330973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_8330973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330973 prefixEnd_8330973 := by exact prefixLift 8330973
  have htrace : WordTrace (prefixWord ++ tailWord_8330973) baseStart_8330973 baseEnd_8330973 := by
    simpa [prefixWord, tailWord_8330973, baseEnd_8330973] using wordTrace_append hprefix tailTrace_8330973
  have hstable : (prefixWord ++ tailWord_8330973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330973).length < 2 ^ (prefixWord ++ tailWord_8330973).sum := by decide
  have hdescent : baseEnd_8330973 < baseStart_8330973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330983 : List Nat := [1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8330983 : Nat := 118140960795 + 8330983 * 2 ^ 59
def prefixEnd_8330983 : Nat := 4983230072969 + 3 ^ 40 * 8330983 * 2
def baseEnd_8330983 : Nat := 4277798603435883724399013

theorem tailTrace_8330983 : CollatzResearch.WordTrace tailWord_8330983 prefixEnd_8330983 4277798603435883724399013 := by
  unfold tailWord_8330983
  simp only [CollatzResearch.WordTrace]
  refine ⟨303855912777278884465133603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202570608518185922976755735 303855912777278884465133603)
  ·
    refine ⟨455783869165918326697700405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303855912777278884465133603 455783869165918326697700405)
    ·
      refine ⟨42729737734304843127909413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 455783869165918326697700405 42729737734304843127909413)
      ·
        refine ⟨8011825825182158086483015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42729737734304843127909413 8011825825182158086483015)
        ·
          refine ⟨12017738737773237129724523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8011825825182158086483015 12017738737773237129724523)
          ·
            refine ⟨18026608106659855694586785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12017738737773237129724523 18026608106659855694586785)
            ·
              refine ⟨13519956079994891770940089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18026608106659855694586785 13519956079994891770940089)
              ·
                refine ⟨10139967059996168828205067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13519956079994891770940089 10139967059996168828205067)
                ·
                  refine ⟨15209950589994253242307601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10139967059996168828205067 15209950589994253242307601)
                  ·
                    refine ⟨11407462942495689931730701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15209950589994253242307601 11407462942495689931730701)
                    ·
                      refine ⟨4277798603435883724399013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11407462942495689931730701 4277798603435883724399013)
                      ·
                        rfl

theorem cell23_8330983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8330983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330983 prefixEnd_8330983 := by exact prefixLift 8330983
  have htrace : WordTrace (prefixWord ++ tailWord_8330983) baseStart_8330983 baseEnd_8330983 := by
    simpa [prefixWord, tailWord_8330983, baseEnd_8330983] using wordTrace_append hprefix tailTrace_8330983
  have hstable : (prefixWord ++ tailWord_8330983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330983).length < 2 ^ (prefixWord ++ tailWord_8330983).sum := by decide
  have hdescent : baseEnd_8330983 < baseStart_8330983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8330995 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 1, 8]
def baseStart_8330995 : Nat := 118140960795 + 8330995 * 2 ^ 59
def prefixEnd_8330995 : Nat := 4983230072969 + 3 ^ 40 * 8330995 * 2
def baseEnd_8330995 : Nat := 1425934921734579225816319

theorem tailTrace_8330995 : CollatzResearch.WordTrace tailWord_8330995 prefixEnd_8330995 1425934921734579225816319 := by
  unfold tailWord_8330995
  simp only [CollatzResearch.WordTrace]
  refine ⟨303856350453235410514570439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202570900302156940343046959 303856350453235410514570439)
  ·
    refine ⟨455784525679853115771855659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303856350453235410514570439 455784525679853115771855659)
    ·
      refine ⟨683676788519779673657783489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455784525679853115771855659 683676788519779673657783489)
      ·
        refine ⟨512757591389834755243337617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683676788519779673657783489 512757591389834755243337617)
        ·
          refine ⟨384568193542376066432503213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512757591389834755243337617 384568193542376066432503213)
          ·
            refine ⟨144213072578391024912188705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384568193542376066432503213 144213072578391024912188705)
            ·
              refine ⟨108159804433793268684141529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144213072578391024912188705 108159804433793268684141529)
              ·
                refine ⟨81119853325344951513106147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108159804433793268684141529 81119853325344951513106147)
                ·
                  refine ⟨121679779988017427269659221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81119853325344951513106147 121679779988017427269659221)
                  ·
                    refine ⟨1425934921734579225816319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 121679779988017427269659221 1425934921734579225816319)
                    ·
                      rfl

theorem cell23_8330995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 8].length) (baseStart_8330995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8330995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8330995 prefixEnd_8330995 := by exact prefixLift 8330995
  have htrace : WordTrace (prefixWord ++ tailWord_8330995) baseStart_8330995 baseEnd_8330995 := by
    simpa [prefixWord, tailWord_8330995, baseEnd_8330995] using wordTrace_append hprefix tailTrace_8330995
  have hstable : (prefixWord ++ tailWord_8330995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8330995).length < 2 ^ (prefixWord ++ tailWord_8330995).sum := by decide
  have hdescent : baseEnd_8330995 < baseStart_8330995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8330995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331032 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_8331032 : Nat := 118140960795 + 8331032 * 2 ^ 59
def prefixEnd_8331032 : Nat := 4983230072969 + 3 ^ 40 * 8331032 * 2
def baseEnd_8331032 : Nat := 4277823763987954032686287

theorem tailTrace_8331032 : CollatzResearch.WordTrace tailWord_8331032 prefixEnd_8331032 4277823763987954032686287 := by
  unfold tailWord_8331032
  simp only [CollatzResearch.WordTrace]
  refine ⟨151928849977050682916833675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202571799969400910555778233 151928849977050682916833675)
  ·
    refine ⟨227893274965576024375250513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151928849977050682916833675 227893274965576024375250513)
    ·
      refine ⟨170919956224182018281437885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227893274965576024375250513 170919956224182018281437885)
      ·
        refine ⟨64094983584068256855539207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170919956224182018281437885 64094983584068256855539207)
        ·
          refine ⟨96142475376102385283308811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64094983584068256855539207 96142475376102385283308811)
          ·
            refine ⟨144213713064153577924963217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96142475376102385283308811 144213713064153577924963217)
            ·
              refine ⟨108160284798115183443722413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144213713064153577924963217 108160284798115183443722413)
              ·
                refine ⟨40560106799293193791395905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108160284798115183443722413 40560106799293193791395905)
                ·
                  refine ⟨30420080099469895343546929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40560106799293193791395905 30420080099469895343546929)
                  ·
                    refine ⟨22815060074602421507660197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30420080099469895343546929 22815060074602421507660197)
                    ·
                      refine ⟨4277823763987954032686287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22815060074602421507660197 4277823763987954032686287)
                      ·
                        rfl

theorem cell23_8331032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_8331032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331032 prefixEnd_8331032 := by exact prefixLift 8331032
  have htrace : WordTrace (prefixWord ++ tailWord_8331032) baseStart_8331032 baseEnd_8331032 := by
    simpa [prefixWord, tailWord_8331032, baseEnd_8331032] using wordTrace_append hprefix tailTrace_8331032
  have hstable : (prefixWord ++ tailWord_8331032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331032).length < 2 ^ (prefixWord ++ tailWord_8331032).sum := by decide
  have hdescent : baseEnd_8331032 < baseStart_8331032 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331035 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9]
def baseStart_8331035 : Nat := 118140960795 + 8331035 * 2 ^ 59
def prefixEnd_8331035 : Nat := 4983230072969 + 3 ^ 40 * 8331035 * 2
def baseEnd_8331035 : Nat := 4277825304429917520948773

theorem tailTrace_8331035 : CollatzResearch.WordTrace tailWord_8331035 prefixEnd_8331035 4277825304429917520948773 := by
  unfold tailWord_8331035
  simp only [CollatzResearch.WordTrace]
  refine ⟨303857809373090497346026559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202571872915393664897351039 303857809373090497346026559)
  ·
    refine ⟨455786714059635746019039839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303857809373090497346026559 455786714059635746019039839)
    ·
      refine ⟨683680071089453619028559759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455786714059635746019039839 683680071089453619028559759)
      ·
        refine ⟨1025520106634180428542839639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683680071089453619028559759 1025520106634180428542839639)
        ·
          refine ⟨1538280159951270642814259459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025520106634180428542839639 1538280159951270642814259459)
          ·
            refine ⟨2307420239926905964221389189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1538280159951270642814259459 2307420239926905964221389189)
            ·
              refine ⟨432641294986294868291510473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2307420239926905964221389189 432641294986294868291510473)
              ·
                refine ⟨324480971239721151218632855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432641294986294868291510473 324480971239721151218632855)
                ·
                  refine ⟨486721456859581726827949283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324480971239721151218632855 486721456859581726827949283)
                  ·
                    refine ⟨730082185289372590241923925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 486721456859581726827949283 730082185289372590241923925)
                    ·
                      refine ⟨4277825304429917520948773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 730082185289372590241923925 4277825304429917520948773)
                      ·
                        rfl

theorem cell23_8331035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 9].length) (baseStart_8331035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331035 prefixEnd_8331035 := by exact prefixLift 8331035
  have htrace : WordTrace (prefixWord ++ tailWord_8331035) baseStart_8331035 baseEnd_8331035 := by
    simpa [prefixWord, tailWord_8331035, baseEnd_8331035] using wordTrace_append hprefix tailTrace_8331035
  have hstable : (prefixWord ++ tailWord_8331035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331035).length < 2 ^ (prefixWord ++ tailWord_8331035).sum := by decide
  have hdescent : baseEnd_8331035 < baseStart_8331035 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331042 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 9]
def baseStart_8331042 : Nat := 118140960795 + 8331042 * 2 ^ 59
def prefixEnd_8331042 : Nat := 4983230072969 + 3 ^ 40 * 8331042 * 2
def baseEnd_8331042 : Nat := 475314322088277665951249

theorem tailTrace_8331042 : CollatzResearch.WordTrace tailWord_8331042 prefixEnd_8331042 475314322088277665951249 := by
  unfold tailWord_8331042
  simp only [CollatzResearch.WordTrace]
  refine ⟨75964516171016284385382845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202572043122710091694354253 75964516171016284385382845)
  ·
    refine ⟨28486693564131106644518567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75964516171016284385382845 28486693564131106644518567)
    ·
      refine ⟨42730040346196659966777851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28486693564131106644518567 42730040346196659966777851)
      ·
        refine ⟨64095060519294989950166777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42730040346196659966777851 64095060519294989950166777)
        ·
          refine ⟨48071295389471242462625083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64095060519294989950166777 48071295389471242462625083)
          ·
            refine ⟨72106943084206863693937625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48071295389471242462625083 72106943084206863693937625)
            ·
              refine ⟨54080207313155147770453219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72106943084206863693937625 54080207313155147770453219)
              ·
                refine ⟨81120310969732721655679829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54080207313155147770453219 81120310969732721655679829)
                ·
                  refine ⟨475314322088277665951249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 81120310969732721655679829 475314322088277665951249)
                  ·
                    rfl

theorem cell23_8331042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_8331042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331042 prefixEnd_8331042 := by exact prefixLift 8331042
  have htrace : WordTrace (prefixWord ++ tailWord_8331042) baseStart_8331042 baseEnd_8331042 := by
    simpa [prefixWord, tailWord_8331042, baseEnd_8331042] using wordTrace_append hprefix tailTrace_8331042
  have hstable : (prefixWord ++ tailWord_8331042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331042).length < 2 ^ (prefixWord ++ tailWord_8331042).sum := by decide
  have hdescent : baseEnd_8331042 < baseStart_8331042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331070 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_8331070 : Nat := 118140960795 + 8331070 * 2 ^ 59
def prefixEnd_8331070 : Nat := 4983230072969 + 3 ^ 40 * 8331070 * 2
def baseEnd_8331070 : Nat := 4277843276252824884011113

theorem tailTrace_8331070 : CollatzResearch.WordTrace tailWord_8331070 prefixEnd_8331070 4277843276252824884011113 := by
  unfold tailWord_8331070
  simp only [CollatzResearch.WordTrace]
  refine ⟨37982385740995462290443833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202572723951975798882367109 37982385740995462290443833)
  ·
    refine ⟨28486789305746596717832875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37982385740995462290443833 28486789305746596717832875)
    ·
      refine ⟨42730183958619895076749313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28486789305746596717832875 42730183958619895076749313)
      ·
        refine ⟨32047637968964921307561985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42730183958619895076749313 32047637968964921307561985)
        ·
          refine ⟨24035728476723690980671489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32047637968964921307561985 24035728476723690980671489)
          ·
            refine ⟨18026796357542768235503617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24035728476723690980671489 18026796357542768235503617)
            ·
              refine ⟨13520097268157076176627713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18026796357542768235503617 13520097268157076176627713)
              ·
                refine ⟨10140072951117807132470785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13520097268157076176627713 10140072951117807132470785)
                ·
                  refine ⟨7605054713338355349353089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10140072951117807132470785 7605054713338355349353089)
                  ·
                    refine ⟨5703791035003766512014817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605054713338355349353089 5703791035003766512014817)
                    ·
                      refine ⟨4277843276252824884011113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703791035003766512014817 4277843276252824884011113)
                      ·
                        rfl

theorem cell23_8331070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_8331070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331070 prefixEnd_8331070 := by exact prefixLift 8331070
  have htrace : WordTrace (prefixWord ++ tailWord_8331070) baseStart_8331070 baseEnd_8331070 := by
    simpa [prefixWord, tailWord_8331070, baseEnd_8331070] using wordTrace_append hprefix tailTrace_8331070
  have hstable : (prefixWord ++ tailWord_8331070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331070).length < 2 ^ (prefixWord ++ tailWord_8331070).sum := by decide
  have hdescent : baseEnd_8331070 < baseStart_8331070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331079 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_8331079 : Nat := 118140960795 + 8331079 * 2 ^ 59
def prefixEnd_8331079 : Nat := 4983230072969 + 3 ^ 40 * 8331079 * 2
def baseEnd_8331079 : Nat := 4277847897578715348798571

theorem tailTrace_8331079 : CollatzResearch.WordTrace tailWord_8331079 prefixEnd_8331079 4277847897578715348798571 := by
  unfold tailWord_8331079
  simp only [CollatzResearch.WordTrace]
  refine ⟨303859414184931092860628291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202572942789954061907085527 303859414184931092860628291)
  ·
    refine ⟨455789121277396639290942437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303859414184931092860628291 455789121277396639290942437)
    ·
      refine ⟨85460460239511869867051707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455789121277396639290942437 85460460239511869867051707)
      ·
        refine ⟨128190690359267804800577561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85460460239511869867051707 128190690359267804800577561)
        ·
          refine ⟨96143017769450853600433171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128190690359267804800577561 96143017769450853600433171)
          ·
            refine ⟨144214526654176280400649757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96143017769450853600433171 144214526654176280400649757)
            ·
              refine ⟨54080447495316105150243659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144214526654176280400649757 54080447495316105150243659)
              ·
                refine ⟨81120671242974157725365489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54080447495316105150243659 81120671242974157725365489)
                ·
                  refine ⟨60840503432230618294024117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81120671242974157725365489 60840503432230618294024117)
                  ·
                    refine ⟨5703797196771620465064761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60840503432230618294024117 5703797196771620465064761)
                    ·
                      refine ⟨4277847897578715348798571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703797196771620465064761 4277847897578715348798571)
                      ·
                        rfl

theorem cell23_8331079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_8331079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331079 prefixEnd_8331079 := by exact prefixLift 8331079
  have htrace : WordTrace (prefixWord ++ tailWord_8331079) baseStart_8331079 baseEnd_8331079 := by
    simpa [prefixWord, tailWord_8331079, baseEnd_8331079] using wordTrace_append hprefix tailTrace_8331079
  have hstable : (prefixWord ++ tailWord_8331079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331079).length < 2 ^ (prefixWord ++ tailWord_8331079).sum := by decide
  have hdescent : baseEnd_8331079 < baseStart_8331079 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331082 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5]
def baseStart_8331082 : Nat := 118140960795 + 8331082 * 2 ^ 59
def prefixEnd_8331082 : Nat := 4983230072969 + 3 ^ 40 * 8331082 * 2
def baseEnd_8331082 : Nat := 4277849438020678837061057

theorem tailTrace_8331082 : CollatzResearch.WordTrace tailWord_8331082 prefixEnd_8331082 4277849438020678837061057 := by
  unfold tailWord_8331082
  simp only [CollatzResearch.WordTrace]
  refine ⟨75964880900980056093246875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202573015735946816248658333 75964880900980056093246875)
  ·
    refine ⟨113947321351470084139870313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75964880900980056093246875 113947321351470084139870313)
    ·
      refine ⟨85460491013602563104902735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113947321351470084139870313 85460491013602563104902735)
      ·
        refine ⟨128190736520403844657354103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85460491013602563104902735 128190736520403844657354103)
        ·
          refine ⟨192286104780605766986031155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128190736520403844657354103 192286104780605766986031155)
          ·
            refine ⟨288429157170908650479046733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192286104780605766986031155 288429157170908650479046733)
            ·
              refine ⟨108160933939090743929642525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288429157170908650479046733 108160933939090743929642525)
              ·
                refine ⟨40560350227159028973615947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108160933939090743929642525 40560350227159028973615947)
                ·
                  refine ⟨60840525340738543460423921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40560350227159028973615947 60840525340738543460423921)
                  ·
                    refine ⟨45630394005553907595317941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60840525340738543460423921 45630394005553907595317941)
                    ·
                      refine ⟨4277849438020678837061057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45630394005553907595317941 4277849438020678837061057)
                      ·
                        rfl

theorem cell23_8331082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_8331082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331082 prefixEnd_8331082 := by exact prefixLift 8331082
  have htrace : WordTrace (prefixWord ++ tailWord_8331082) baseStart_8331082 baseEnd_8331082 := by
    simpa [prefixWord, tailWord_8331082, baseEnd_8331082] using wordTrace_append hprefix tailTrace_8331082
  have hstable : (prefixWord ++ tailWord_8331082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331082).length < 2 ^ (prefixWord ++ tailWord_8331082).sum := by decide
  have hdescent : baseEnd_8331082 < baseStart_8331082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331106 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_8331106 : Nat := 118140960795 + 8331106 * 2 ^ 59
def prefixEnd_8331106 : Nat := 4983230072969 + 3 ^ 40 * 8331106 * 2
def baseEnd_8331106 : Nat := 1425953920518795581053649

theorem tailTrace_8331106 : CollatzResearch.WordTrace tailWord_8331106 prefixEnd_8331106 1425953920518795581053649 := by
  unfold tailWord_8331106
  simp only [CollatzResearch.WordTrace]
  refine ⟨75965099738958319117965293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202573599303888850981240781 75965099738958319117965293)
  ·
    refine ⟨28486912402109369669236985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75965099738958319117965293 28486912402109369669236985)
    ·
      refine ⟨21365184301582027251927739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28486912402109369669236985 21365184301582027251927739)
      ·
        refine ⟨32047776452373040877891609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21365184301582027251927739 32047776452373040877891609)
        ·
          refine ⟨24035832339279780658418707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32047776452373040877891609 24035832339279780658418707)
          ·
            refine ⟨36053748508919670987628061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24035832339279780658418707 36053748508919670987628061)
            ·
              refine ⟨13520155690844876620360523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36053748508919670987628061 13520155690844876620360523)
              ·
                refine ⟨20280233536267314930540785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13520155690844876620360523 20280233536267314930540785)
                ·
                  refine ⟨15210175152200486197905589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20280233536267314930540785 15210175152200486197905589)
                  ·
                    refine ⟨1425953920518795581053649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15210175152200486197905589 1425953920518795581053649)
                    ·
                      rfl

theorem cell23_8331106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_8331106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331106 prefixEnd_8331106 := by exact prefixLift 8331106
  have htrace : WordTrace (prefixWord ++ tailWord_8331106) baseStart_8331106 baseEnd_8331106 := by
    simpa [prefixWord, tailWord_8331106, baseEnd_8331106] using wordTrace_append hprefix tailTrace_8331106
  have hstable : (prefixWord ++ tailWord_8331106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331106).length < 2 ^ (prefixWord ++ tailWord_8331106).sum := by decide
  have hdescent : baseEnd_8331106 < baseStart_8331106 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331109 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 3, 6, 2]
def baseStart_8331109 : Nat := 118140960795 + 8331109 * 2 ^ 59
def prefixEnd_8331109 : Nat := 4983230072969 + 3 ^ 40 * 8331109 * 2
def baseEnd_8331109 : Nat := 4277863301998350231423433

theorem tailTrace_8331109 : CollatzResearch.WordTrace tailWord_8331109 prefixEnd_8331109 4277863301998350231423433 := by
  unfold tailWord_8331109
  simp only [CollatzResearch.WordTrace]
  refine ⟨303860508374822407984220381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202573672249881605322813587 303860508374822407984220381)
  ·
    refine ⟨113947690640558402994082643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303860508374822407984220381 113947690640558402994082643)
    ·
      refine ⟨170921535960837604491123965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113947690640558402994082643 170921535960837604491123965)
      ·
        refine ⟨64095575985314101684171487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170921535960837604491123965 64095575985314101684171487)
        ·
          refine ⟨96143363977971152526257231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64095575985314101684171487 96143363977971152526257231)
          ·
            refine ⟨144215045966956728789385847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96143363977971152526257231 144215045966956728789385847)
            ·
              refine ⟨216322568950435093184078771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144215045966956728789385847 216322568950435093184078771)
              ·
                refine ⟨324483853425652639776118157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216322568950435093184078771 324483853425652639776118157)
                ·
                  refine ⟨121681445034619739916044309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324483853425652639776118157 121681445034619739916044309)
                  ·
                    refine ⟨5703817735997800308564577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121681445034619739916044309 5703817735997800308564577)
                    ·
                      refine ⟨4277863301998350231423433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703817735997800308564577 4277863301998350231423433)
                      ·
                        rfl

theorem cell23_8331109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_8331109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331109 prefixEnd_8331109 := by exact prefixLift 8331109
  have htrace : WordTrace (prefixWord ++ tailWord_8331109) baseStart_8331109 baseEnd_8331109 := by
    simpa [prefixWord, tailWord_8331109, baseEnd_8331109] using wordTrace_append hprefix tailTrace_8331109
  have hstable : (prefixWord ++ tailWord_8331109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331109).length < 2 ^ (prefixWord ++ tailWord_8331109).sum := by decide
  have hdescent : baseEnd_8331109 < baseStart_8331109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331129 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 3]
def baseStart_8331129 : Nat := 118140960795 + 8331129 * 2 ^ 59
def prefixEnd_8331129 : Nat := 4983230072969 + 3 ^ 40 * 8331129 * 2
def baseEnd_8331129 : Nat := 4277873571611440153173341

theorem tailTrace_8331129 : CollatzResearch.WordTrace tailWord_8331129 prefixEnd_8331129 4277873571611440153173341 := by
  unfold tailWord_8331129
  simp only [CollatzResearch.WordTrace]
  refine ⟨303861237834749951399948441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202574158556499967599965627 303861237834749951399948441)
  ·
    refine ⟨227895928376062463549961331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303861237834749951399948441 227895928376062463549961331)
    ·
      refine ⟨341843892564093695324941997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227895928376062463549961331 341843892564093695324941997)
      ·
        refine ⟨128191459711535135746853249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341843892564093695324941997 128191459711535135746853249)
        ·
          refine ⟨96143594783651351810139937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128191459711535135746853249 96143594783651351810139937)
          ·
            refine ⟨72107696087738513857604953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96143594783651351810139937 72107696087738513857604953)
            ·
              refine ⟨54080772065803885393203715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72107696087738513857604953 54080772065803885393203715)
              ·
                refine ⟨81121158098705828089805573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54080772065803885393203715 81121158098705828089805573)
                ·
                  refine ⟨15210217143507342766838545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81121158098705828089805573 15210217143507342766838545)
                  ·
                    refine ⟨11407662857630507075128909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15210217143507342766838545 11407662857630507075128909)
                    ·
                      refine ⟨4277873571611440153173341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11407662857630507075128909 4277873571611440153173341)
                      ·
                        rfl

theorem cell23_8331129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_8331129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331129 prefixEnd_8331129 := by exact prefixLift 8331129
  have htrace : WordTrace (prefixWord ++ tailWord_8331129) baseStart_8331129 baseEnd_8331129 := by
    simpa [prefixWord, tailWord_8331129, baseEnd_8331129] using wordTrace_append hprefix tailTrace_8331129
  have hstable : (prefixWord ++ tailWord_8331129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331129).length < 2 ^ (prefixWord ++ tailWord_8331129).sum := by decide
  have hdescent : baseEnd_8331129 < baseStart_8331129 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331136 : List Nat := [2, 1, 1, 2, 1, 2, 3, 6, 1, 4]
def baseStart_8331136 : Nat := 118140960795 + 8331136 * 2 ^ 59
def prefixEnd_8331136 : Nat := 4983230072969 + 3 ^ 40 * 8331136 * 2
def baseEnd_8331136 : Nat := 1425959055325340541928603

theorem tailTrace_8331136 : CollatzResearch.WordTrace tailWord_8331136 prefixEnd_8331136 1425959055325340541928603 := by
  unfold tailWord_8331136
  simp only [CollatzResearch.WordTrace]
  refine ⟨151930746572862295797726631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202574328763816394396968841 151930746572862295797726631)
  ·
    refine ⟨227896119859293443696589947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151930746572862295797726631 227896119859293443696589947)
    ·
      refine ⟨341844179788940165544884921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227896119859293443696589947 341844179788940165544884921)
      ·
        refine ⟨256383134841705124158663691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341844179788940165544884921 256383134841705124158663691)
        ·
          refine ⟨384574702262557686237995537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256383134841705124158663691 384574702262557686237995537)
          ·
            refine ⟨288431026696918264678496653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384574702262557686237995537 288431026696918264678496653)
            ·
              refine ⟨108161635011344349254436245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288431026696918264678496653 108161635011344349254436245)
              ·
                refine ⟨5070076641156766371301699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108161635011344349254436245 5070076641156766371301699)
                ·
                  refine ⟨7605114961735149556952549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070076641156766371301699 7605114961735149556952549)
                  ·
                    refine ⟨1425959055325340541928603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7605114961735149556952549 1425959055325340541928603)
                    ·
                      rfl

theorem cell23_8331136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 4].length) (baseStart_8331136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331136 prefixEnd_8331136 := by exact prefixLift 8331136
  have htrace : WordTrace (prefixWord ++ tailWord_8331136) baseStart_8331136 baseEnd_8331136 := by
    simpa [prefixWord, tailWord_8331136, baseEnd_8331136] using wordTrace_append hprefix tailTrace_8331136
  have hstable : (prefixWord ++ tailWord_8331136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331136).length < 2 ^ (prefixWord ++ tailWord_8331136).sum := by decide
  have hdescent : baseEnd_8331136 < baseStart_8331136 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331199 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_8331199 : Nat := 118140960795 + 8331199 * 2 ^ 59
def prefixEnd_8331199 : Nat := 4983230072969 + 3 ^ 40 * 8331199 * 2
def baseEnd_8331199 : Nat := 4277909515257254879298019

theorem tailTrace_8331199 : CollatzResearch.WordTrace tailWord_8331199 prefixEnd_8331199 4277909515257254879298019 := by
  unfold tailWord_8331199
  simp only [CollatzResearch.WordTrace]
  refine ⟨303863790944496353354996651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202575860629664235569997767 303863790944496353354996651)
  ·
    refine ⟨455795686416744530032494977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303863790944496353354996651 455795686416744530032494977)
    ·
      refine ⟨341846764812558397524371233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455795686416744530032494977 341846764812558397524371233)
      ·
        refine ⟨256385073609418798143278425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341846764812558397524371233 256385073609418798143278425)
        ·
          refine ⟨192288805207064098607458819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256385073609418798143278425 192288805207064098607458819)
          ·
            refine ⟨288433207810596147911188229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192288805207064098607458819 288433207810596147911188229)
            ·
              refine ⟨54081226464486777733347793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288433207810596147911188229 54081226464486777733347793)
              ·
                refine ⟨40560919848365083300010845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54081226464486777733347793 40560919848365083300010845)
                ·
                  refine ⟨15210344943136906237504067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40560919848365083300010845 15210344943136906237504067)
                  ·
                    refine ⟨22815517414705359356256101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15210344943136906237504067 22815517414705359356256101)
                    ·
                      refine ⟨4277909515257254879298019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22815517414705359356256101 4277909515257254879298019)
                      ·
                        rfl

theorem cell23_8331199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_8331199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331199 prefixEnd_8331199 := by exact prefixLift 8331199
  have htrace : WordTrace (prefixWord ++ tailWord_8331199) baseStart_8331199 baseEnd_8331199 := by
    simpa [prefixWord, tailWord_8331199, baseEnd_8331199] using wordTrace_append hprefix tailTrace_8331199
  have hstable : (prefixWord ++ tailWord_8331199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331199).length < 2 ^ (prefixWord ++ tailWord_8331199).sum := by decide
  have hdescent : baseEnd_8331199 < baseStart_8331199 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331216 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4]
def baseStart_8331216 : Nat := 118140960795 + 8331216 * 2 ^ 59
def prefixEnd_8331216 : Nat := 4983230072969 + 3 ^ 40 * 8331216 * 2
def baseEnd_8331216 : Nat := 4277918244428381312785441

theorem tailTrace_8331216 : CollatzResearch.WordTrace tailWord_8331216 prefixEnd_8331216 4277918244428381312785441 := by
  unfold tailWord_8331216
  simp only [CollatzResearch.WordTrace]
  refine ⟨151932205492717382629182751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202576273990289843505577001 151932205492717382629182751)
  ·
    refine ⟨227898308239076073943774127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151932205492717382629182751 227898308239076073943774127)
    ·
      refine ⟨341847462358614110915661191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227898308239076073943774127 341847462358614110915661191)
      ·
        refine ⟨512771193537921166373491787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341847462358614110915661191 512771193537921166373491787)
        ·
          refine ⟨769156790306881749560237681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512771193537921166373491787 769156790306881749560237681)
          ·
            refine ⟨576867592730161312170178261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769156790306881749560237681 576867592730161312170178261)
            ·
              refine ⟨13520334204613155753988553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 576867592730161312170178261 13520334204613155753988553)
              ·
                refine ⟨10140250653459866815491415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13520334204613155753988553 10140250653459866815491415)
                ·
                  refine ⟨15210375980189800223237123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10140250653459866815491415 15210375980189800223237123)
                  ·
                    refine ⟨22815563970284700334855685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15210375980189800223237123 22815563970284700334855685)
                    ·
                      refine ⟨4277918244428381312785441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22815563970284700334855685 4277918244428381312785441)
                      ·
                        rfl

theorem cell23_8331216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_8331216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331216 prefixEnd_8331216 := by exact prefixLift 8331216
  have htrace : WordTrace (prefixWord ++ tailWord_8331216) baseStart_8331216 baseEnd_8331216 := by
    simpa [prefixWord, tailWord_8331216, baseEnd_8331216] using wordTrace_append hprefix tailTrace_8331216
  have hstable : (prefixWord ++ tailWord_8331216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331216).length < 2 ^ (prefixWord ++ tailWord_8331216).sum := by decide
  have hdescent : baseEnd_8331216 < baseStart_8331216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331226 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_8331226 : Nat := 118140960795 + 8331226 * 2 ^ 59
def prefixEnd_8331226 : Nat := 4983230072969 + 3 ^ 40 * 8331226 * 2
def baseEnd_8331226 : Nat := 1425974459744975424553465

theorem tailTrace_8331226 : CollatzResearch.WordTrace tailWord_8331226 prefixEnd_8331226 1425974459744975424553465 := by
  unfold tailWord_8331226
  simp only [CollatzResearch.WordTrace]
  refine ⟨75966193928849634241557383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202576517143599024644153021 75966193928849634241557383)
  ·
    refine ⟨113949290893274451362336075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75966193928849634241557383 113949290893274451362336075)
    ·
      refine ⟨170923936339911677043504113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113949290893274451362336075 170923936339911677043504113)
      ·
        refine ⟨128192952254933757782628085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170923936339911677043504113 128192952254933757782628085)
        ·
          refine ⟨12018089273900039792121383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128192952254933757782628085 12018089273900039792121383)
          ·
            refine ⟨18027133910850059688182075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018089273900039792121383 18027133910850059688182075)
            ·
              refine ⟨27040700866275089532273113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18027133910850059688182075 27040700866275089532273113)
              ·
                refine ⟨20280525649706317149204835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27040700866275089532273113 20280525649706317149204835)
                ·
                  refine ⟨30420788474559475723807253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20280525649706317149204835 30420788474559475723807253)
                  ·
                    refine ⟨1425974459744975424553465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30420788474559475723807253 1425974459744975424553465)
                    ·
                      rfl

theorem cell23_8331226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_8331226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331226 prefixEnd_8331226 := by exact prefixLift 8331226
  have htrace : WordTrace (prefixWord ++ tailWord_8331226) baseStart_8331226 baseEnd_8331226 := by
    simpa [prefixWord, tailWord_8331226, baseEnd_8331226] using wordTrace_append hprefix tailTrace_8331226
  have hstable : (prefixWord ++ tailWord_8331226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331226).length < 2 ^ (prefixWord ++ tailWord_8331226).sum := by decide
  have hdescent : baseEnd_8331226 < baseStart_8331226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331239 : List Nat := [1, 1, 5, 2, 3, 11]
def baseStart_8331239 : Nat := 118140960795 + 8331239 * 2 ^ 59
def prefixEnd_8331239 : Nat := 4983230072969 + 3 ^ 40 * 8331239 * 2
def baseEnd_8331239 : Nat := 17604650429972982398345

theorem tailTrace_8331239 : CollatzResearch.WordTrace tailWord_8331239 prefixEnd_8331239 17604650429972982398345 := by
  unfold tailWord_8331239
  simp only [CollatzResearch.WordTrace]
  refine ⟨303865249864351440186452771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202576833242900960124301847 303865249864351440186452771)
  ·
    refine ⟨455797874796527160279679157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303865249864351440186452771 455797874796527160279679157)
    ·
      refine ⟨42731050762174421276219921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 455797874796527160279679157 42731050762174421276219921)
      ·
        refine ⟨32048288071630815957164941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42731050762174421276219921 32048288071630815957164941)
        ·
          refine ⟨12018108026861555983936853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32048288071630815957164941 12018108026861555983936853)
          ·
            refine ⟨17604650429972982398345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 12018108026861555983936853 17604650429972982398345)
            ·
              rfl

theorem cell23_8331239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 11].length) (baseStart_8331239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331239 prefixEnd_8331239 := by exact prefixLift 8331239
  have htrace : WordTrace (prefixWord ++ tailWord_8331239) baseStart_8331239 baseEnd_8331239 := by
    simpa [prefixWord, tailWord_8331239, baseEnd_8331239] using wordTrace_append hprefix tailTrace_8331239
  have hstable : (prefixWord ++ tailWord_8331239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331239).length < 2 ^ (prefixWord ++ tailWord_8331239).sum := by decide
  have hdescent : baseEnd_8331239 < baseStart_8331239 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331284 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_8331284 : Nat := 118140960795 + 8331284 * 2 ^ 59
def prefixEnd_8331284 : Nat := 4983230072969 + 3 ^ 40 * 8331284 * 2
def baseEnd_8331284 : Nat := 4277953161112887046735129

theorem tailTrace_8331284 : CollatzResearch.WordTrace tailWord_8331284 prefixEnd_8331284 4277953161112887046735129 := by
  unfold tailWord_8331284
  simp only [CollatzResearch.WordTrace]
  refine ⟨151933445574594206435920453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202577927432792275247893937 151933445574594206435920453)
  ·
    refine ⟨28487521045236413706735085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151933445574594206435920453 28487521045236413706735085)
    ·
      refine ⟨10682820391963655140025657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28487521045236413706735085 10682820391963655140025657)
      ·
        refine ⟨8012115293972741355019243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10682820391963655140025657 8012115293972741355019243)
        ·
          refine ⟨12018172940959112032528865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012115293972741355019243 12018172940959112032528865)
          ·
            refine ⟨9013629705719334024396649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12018172940959112032528865 9013629705719334024396649)
            ·
              refine ⟨6760222279289500518297487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9013629705719334024396649 6760222279289500518297487)
              ·
                refine ⟨10140333418934250777446231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760222279289500518297487 10140333418934250777446231)
                ·
                  refine ⟨15210500128401376166169347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10140333418934250777446231 15210500128401376166169347)
                  ·
                    refine ⟨22815750192602064249254021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15210500128401376166169347 22815750192602064249254021)
                    ·
                      refine ⟨4277953161112887046735129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22815750192602064249254021 4277953161112887046735129)
                      ·
                        rfl

theorem cell23_8331284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_8331284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331284 prefixEnd_8331284 := by exact prefixLift 8331284
  have htrace : WordTrace (prefixWord ++ tailWord_8331284) baseStart_8331284 baseEnd_8331284 := by
    simpa [prefixWord, tailWord_8331284, baseEnd_8331284] using wordTrace_append hprefix tailTrace_8331284
  have hstable : (prefixWord ++ tailWord_8331284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331284).length < 2 ^ (prefixWord ++ tailWord_8331284).sum := by decide
  have hdescent : baseEnd_8331284 < baseStart_8331284 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331287 : List Nat := [1, 1, 3, 5, 2, 2, 2, 1, 1, 2, 3]
def baseStart_8331287 : Nat := 118140960795 + 8331287 * 2 ^ 59
def prefixEnd_8331287 : Nat := 4983230072969 + 3 ^ 40 * 8331287 * 2
def baseEnd_8331287 : Nat := 4277954701554850534997615

theorem tailTrace_8331287 : CollatzResearch.WordTrace tailWord_8331287 prefixEnd_8331287 4277954701554850534997615 := by
  unfold tailWord_8331287
  simp only [CollatzResearch.WordTrace]
  refine ⟨303867000568177544384200115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202578000378785029589466743 303867000568177544384200115)
  ·
    refine ⟨455800500852266316576300173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303867000568177544384200115 455800500852266316576300173)
    ·
      refine ⟨170925187819599868716112565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455800500852266316576300173 170925187819599868716112565)
      ·
        refine ⟨16024236358087487692135553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170925187819599868716112565 16024236358087487692135553)
        ·
          refine ⟨12018177268565615769101665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16024236358087487692135553 12018177268565615769101665)
          ·
            refine ⟨9013632951424211826826249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12018177268565615769101665 9013632951424211826826249)
            ·
              refine ⟨6760224713568158870119687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9013632951424211826826249 6760224713568158870119687)
              ·
                refine ⟨10140337070352238305179531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760224713568158870119687 10140337070352238305179531)
                ·
                  refine ⟨15210505605528357457769297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10140337070352238305179531 15210505605528357457769297)
                  ·
                    refine ⟨11407879204146268093326973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15210505605528357457769297 11407879204146268093326973)
                    ·
                      refine ⟨4277954701554850534997615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11407879204146268093326973 4277954701554850534997615)
                      ·
                        rfl

theorem cell23_8331287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_8331287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331287 prefixEnd_8331287 := by exact prefixLift 8331287
  have htrace : WordTrace (prefixWord ++ tailWord_8331287) baseStart_8331287 baseEnd_8331287 := by
    simpa [prefixWord, tailWord_8331287, baseEnd_8331287] using wordTrace_append hprefix tailTrace_8331287
  have hstable : (prefixWord ++ tailWord_8331287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331287).length < 2 ^ (prefixWord ++ tailWord_8331287).sum := by decide
  have hdescent : baseEnd_8331287 < baseStart_8331287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331299 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 4, 6]
def baseStart_8331299 : Nat := 118140960795 + 8331299 * 2 ^ 59
def prefixEnd_8331299 : Nat := 4983230072969 + 3 ^ 40 * 8331299 * 2
def baseEnd_8331299 : Nat := 1425986954440901496015853

theorem tailTrace_8331299 : CollatzResearch.WordTrace tailWord_8331299 prefixEnd_8331299 1425986954440901496015853 := by
  unfold tailWord_8331299
  simp only [CollatzResearch.WordTrace]
  refine ⟨303867438244134070433636951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202578292162756046955757967 303867438244134070433636951)
  ·
    refine ⟨455801157366201105650455427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303867438244134070433636951 455801157366201105650455427)
    ·
      refine ⟨683701736049301658475683141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455801157366201105650455427 683701736049301658475683141)
      ·
        refine ⟨128194075509244060964190589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 683701736049301658475683141 128194075509244060964190589)
        ·
          refine ⟨48072778315966522861571471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128194075509244060964190589 48072778315966522861571471)
          ·
            refine ⟨72109167473949784292357207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48072778315966522861571471 72109167473949784292357207)
            ·
              refine ⟨108163751210924676438535811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72109167473949784292357207 108163751210924676438535811)
              ·
                refine ⟨162245626816387014657803717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108163751210924676438535811 162245626816387014657803717)
                ·
                  refine ⟨30421055028072565248338197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162245626816387014657803717 30421055028072565248338197)
                  ·
                    refine ⟨1425986954440901496015853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30421055028072565248338197 1425986954440901496015853)
                    ·
                      rfl

theorem cell23_8331299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 6].length) (baseStart_8331299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331299 prefixEnd_8331299 := by exact prefixLift 8331299
  have htrace : WordTrace (prefixWord ++ tailWord_8331299) baseStart_8331299 baseEnd_8331299 := by
    simpa [prefixWord, tailWord_8331299, baseEnd_8331299] using wordTrace_append hprefix tailTrace_8331299
  have hstable : (prefixWord ++ tailWord_8331299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331299).length < 2 ^ (prefixWord ++ tailWord_8331299).sum := by decide
  have hdescent : baseEnd_8331299 < baseStart_8331299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331300 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_8331300 : Nat := 118140960795 + 8331300 * 2 ^ 59
def prefixEnd_8331300 : Nat := 4983230072969 + 3 ^ 40 * 8331300 * 2
def baseEnd_8331300 : Nat := 4277961376803358984135055

theorem tailTrace_8331300 : CollatzResearch.WordTrace tailWord_8331300 prefixEnd_8331300 4277961376803358984135055 := by
  unfold tailWord_8331300
  simp only [CollatzResearch.WordTrace]
  refine ⟨151933737358565223802211677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202578316478086965069615569 151933737358565223802211677)
  ·
    refine ⟨56975151509461958925829379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151933737358565223802211677 56975151509461958925829379)
    ·
      refine ⟨85462727264192938388744069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56975151509461958925829379 85462727264192938388744069)
      ·
        refine ⟨16024261362036175947889513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85462727264192938388744069 16024261362036175947889513)
        ·
          refine ⟨12018196021527131960917135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16024261362036175947889513 12018196021527131960917135)
          ·
            refine ⟨18027294032290697941375703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018196021527131960917135 18027294032290697941375703)
            ·
              refine ⟨27040941048436046912063555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18027294032290697941375703 27040941048436046912063555)
              ·
                refine ⟨40561411572654070368095333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27040941048436046912063555 40561411572654070368095333)
                ·
                  refine ⟨7605264669872638194017875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40561411572654070368095333 7605264669872638194017875)
                  ·
                    refine ⟨11407897004808957291026813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7605264669872638194017875 11407897004808957291026813)
                    ·
                      refine ⟨4277961376803358984135055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11407897004808957291026813 4277961376803358984135055)
                      ·
                        rfl

theorem cell23_8331300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_8331300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331300 prefixEnd_8331300 := by exact prefixLift 8331300
  have htrace : WordTrace (prefixWord ++ tailWord_8331300) baseStart_8331300 baseEnd_8331300 := by
    simpa [prefixWord, tailWord_8331300, baseEnd_8331300] using wordTrace_append hprefix tailTrace_8331300
  have hstable : (prefixWord ++ tailWord_8331300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331300).length < 2 ^ (prefixWord ++ tailWord_8331300).sum := by decide
  have hdescent : baseEnd_8331300 < baseStart_8331300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331357 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_8331357 : Nat := 118140960795 + 8331357 * 2 ^ 59
def prefixEnd_8331357 : Nat := 4983230072969 + 3 ^ 40 * 8331357 * 2
def baseEnd_8331357 : Nat := 4277990645200665261122293

theorem tailTrace_8331357 : CollatzResearch.WordTrace tailWord_8331357 prefixEnd_8331357 4277990645200665261122293 := by
  unfold tailWord_8331357
  simp only [CollatzResearch.WordTrace]
  refine ⟨303869553677923946339248325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202579702451949297559498883 303869553677923946339248325)
  ·
    refine ⟨56975541314610739938609061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303869553677923946339248325 56975541314610739938609061)
    ·
      refine ⟨10682913996489513738489199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56975541314610739938609061 10682913996489513738489199)
      ·
        refine ⟨16024370994734270607733799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10682913996489513738489199 16024370994734270607733799)
        ·
          refine ⟨24036556492101405911600699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16024370994734270607733799 24036556492101405911600699)
          ·
            refine ⟨36054834738152108867401049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24036556492101405911600699 36054834738152108867401049)
            ·
              refine ⟨27041126053614081650550787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36054834738152108867401049 27041126053614081650550787)
              ·
                refine ⟨40561689080421122475826181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27041126053614081650550787 40561689080421122475826181)
                ·
                  refine ⟨7605316702578960464217409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40561689080421122475826181 7605316702578960464217409)
                  ·
                    refine ⟨5703987526934220348163057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605316702578960464217409 5703987526934220348163057)
                    ·
                      refine ⟨4277990645200665261122293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5703987526934220348163057 4277990645200665261122293)
                      ·
                        rfl

theorem cell23_8331357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_8331357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331357 prefixEnd_8331357 := by exact prefixLift 8331357
  have htrace : WordTrace (prefixWord ++ tailWord_8331357) baseStart_8331357 baseEnd_8331357 := by
    simpa [prefixWord, tailWord_8331357, baseEnd_8331357] using wordTrace_append hprefix tailTrace_8331357
  have hstable : (prefixWord ++ tailWord_8331357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331357).length < 2 ^ (prefixWord ++ tailWord_8331357).sum := by decide
  have hdescent : baseEnd_8331357 < baseStart_8331357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331359 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 3, 7]
def baseStart_8331359 : Nat := 118140960795 + 8331359 * 2 ^ 59
def prefixEnd_8331359 : Nat := 4983230072969 + 3 ^ 40 * 8331359 * 2
def baseEnd_8331359 : Nat := 1425997224053991417765761

theorem tailTrace_8331359 : CollatzResearch.WordTrace tailWord_8331359 prefixEnd_8331359 1425997224053991417765761 := by
  unfold tailWord_8331359
  simp only [CollatzResearch.WordTrace]
  refine ⟨303869626623916700680821131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202579751082611133787214087 303869626623916700680821131)
  ·
    refine ⟨455804439935875051021231697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303869626623916700680821131 455804439935875051021231697)
    ·
      refine ⟨341853329951906288265923773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455804439935875051021231697 341853329951906288265923773)
      ·
        refine ⟨128194998731964858099721415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341853329951906288265923773 128194998731964858099721415)
        ·
          refine ⟨192292498097947287149582123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128194998731964858099721415 192292498097947287149582123)
          ·
            refine ⟨288438747146920930724373185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192292498097947287149582123 288438747146920930724373185)
            ·
              refine ⟨216329060360190698043279889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288438747146920930724373185 216329060360190698043279889)
              ·
                refine ⟨162246795270143023532459917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216329060360190698043279889 162246795270143023532459917)
                ·
                  refine ⟨60842548226303633824672469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162246795270143023532459917 60842548226303633824672469)
                  ·
                    refine ⟨1425997224053991417765761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60842548226303633824672469 1425997224053991417765761)
                    ·
                      rfl

theorem cell23_8331359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_8331359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331359 prefixEnd_8331359 := by exact prefixLift 8331359
  have htrace : WordTrace (prefixWord ++ tailWord_8331359) baseStart_8331359 baseEnd_8331359 := by
    simpa [prefixWord, tailWord_8331359, baseEnd_8331359] using wordTrace_append hprefix tailTrace_8331359
  have hstable : (prefixWord ++ tailWord_8331359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331359).length < 2 ^ (prefixWord ++ tailWord_8331359).sum := by decide
  have hdescent : baseEnd_8331359 < baseStart_8331359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331413 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 2, 4, 2]
def baseStart_8331413 : Nat := 118140960795 + 8331413 * 2 ^ 59
def prefixEnd_8331413 : Nat := 4983230072969 + 3 ^ 40 * 8331413 * 2
def baseEnd_8331413 : Nat := 4278019400117317042022035

theorem tailTrace_8331413 : CollatzResearch.WordTrace tailWord_8331413 prefixEnd_8331413 4278019400117317042022035 := by
  unfold tailWord_8331413
  simp only [CollatzResearch.WordTrace]
  refine ⟨303871596165721067903286893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202581064110480711935524595 303871596165721067903286893)
  ·
    refine ⟨113951848562145400463732585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303871596165721067903286893 113951848562145400463732585)
    ·
      refine ⟨85463886421609050347799439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113951848562145400463732585 85463886421609050347799439)
      ·
        refine ⟨128195829632413575521699159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85463886421609050347799439 128195829632413575521699159)
        ·
          refine ⟨192293744448620363282548739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128195829632413575521699159 192293744448620363282548739)
          ·
            refine ⟨288440616672930544923823109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192293744448620363282548739 288440616672930544923823109)
            ·
              refine ⟨54082615626174477173216833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288440616672930544923823109 54082615626174477173216833)
              ·
                refine ⟨40561961719630857879912625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54082615626174477173216833 40561961719630857879912625)
                ·
                  refine ⟨30421471289723143409934469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40561961719630857879912625 30421471289723143409934469)
                  ·
                    refine ⟨5704025866823089389362713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30421471289723143409934469 5704025866823089389362713)
                    ·
                      refine ⟨4278019400117317042022035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704025866823089389362713 4278019400117317042022035)
                      ·
                        rfl

theorem cell23_8331413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_8331413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331413 prefixEnd_8331413 := by exact prefixLift 8331413
  have htrace : WordTrace (prefixWord ++ tailWord_8331413) baseStart_8331413 baseEnd_8331413 := by
    simpa [prefixWord, tailWord_8331413, baseEnd_8331413] using wordTrace_append hprefix tailTrace_8331413
  have hstable : (prefixWord ++ tailWord_8331413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331413).length < 2 ^ (prefixWord ++ tailWord_8331413).sum := by decide
  have hdescent : baseEnd_8331413 < baseStart_8331413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331470 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_8331470 : Nat := 118140960795 + 8331470 * 2 ^ 59
def prefixEnd_8331470 : Nat := 4983230072969 + 3 ^ 40 * 8331470 * 2
def baseEnd_8331470 : Nat := 475338740946069257667697

theorem tailTrace_8331470 : CollatzResearch.WordTrace tailWord_8331470 prefixEnd_8331470 475338740946069257667697 := by
  unfold tailWord_8331470
  simp only [CollatzResearch.WordTrace]
  refine ⟨37984209390814320829763983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202582450084343044425407909 37984209390814320829763983)
  ·
    refine ⟨56976314086221481244645975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37984209390814320829763983 56976314086221481244645975)
    ·
      refine ⟨85464471129332221866968963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56976314086221481244645975 85464471129332221866968963)
      ·
        refine ⟨128196706693998332800453445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85464471129332221866968963 128196706693998332800453445)
        ·
          refine ⟨24036882505124687400085021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128196706693998332800453445 24036882505124687400085021)
          ·
            refine ⟨9013830939421757775031883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24036882505124687400085021 9013830939421757775031883)
            ·
              refine ⟨13520746409132636662547825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9013830939421757775031883 13520746409132636662547825)
              ·
                refine ⟨10140559806849477496910869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13520746409132636662547825 10140559806849477496910869)
                ·
                  refine ⟨475338740946069257667697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10140559806849477496910869 475338740946069257667697)
                  ·
                    rfl

theorem cell23_8331470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_8331470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331470 prefixEnd_8331470 := by exact prefixLift 8331470
  have htrace : WordTrace (prefixWord ++ tailWord_8331470) baseStart_8331470 baseEnd_8331470 := by
    simpa [prefixWord, tailWord_8331470, baseEnd_8331470] using wordTrace_append hprefix tailTrace_8331470
  have hstable : (prefixWord ++ tailWord_8331470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331470).length < 2 ^ (prefixWord ++ tailWord_8331470).sum := by decide
  have hdescent : baseEnd_8331470 < baseStart_8331470 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331480 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_8331480 : Nat := 118140960795 + 8331480 * 2 ^ 59
def prefixEnd_8331480 : Nat := 4983230072969 + 3 ^ 40 * 8331480 * 2
def baseEnd_8331480 : Nat := 4278053803321168279884227

theorem tailTrace_8331480 : CollatzResearch.WordTrace tailWord_8331480 prefixEnd_8331480 4278053803321168279884227 := by
  unfold tailWord_8331480
  simp only [CollatzResearch.WordTrace]
  refine ⟨151937019928239169172987947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202582693237652225563983929 151937019928239169172987947)
  ·
    refine ⟨227905529892358753759481921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151937019928239169172987947 227905529892358753759481921)
    ·
      refine ⟨170929147419269065319611441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227905529892358753759481921 170929147419269065319611441)
      ·
        refine ⟨128196860564451798989708581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170929147419269065319611441 128196860564451798989708581)
        ·
          refine ⟨24036911355834712310570359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128196860564451798989708581 24036911355834712310570359)
          ·
            refine ⟨36055367033752068465855539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24036911355834712310570359 36055367033752068465855539)
            ·
              refine ⟨54083050550628102698783309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36055367033752068465855539 54083050550628102698783309)
              ·
                refine ⟨20281143956485538512043741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54083050550628102698783309 20281143956485538512043741)
                ·
                  refine ⟨7605428983682076942016403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20281143956485538512043741 7605428983682076942016403)
                  ·
                    refine ⟨11408143475523115413024605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7605428983682076942016403 11408143475523115413024605)
                    ·
                      refine ⟨4278053803321168279884227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408143475523115413024605 4278053803321168279884227)
                      ·
                        rfl

theorem cell23_8331480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_8331480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331480 prefixEnd_8331480 := by exact prefixLift 8331480
  have htrace : WordTrace (prefixWord ++ tailWord_8331480) baseStart_8331480 baseEnd_8331480 := by
    simpa [prefixWord, tailWord_8331480, baseEnd_8331480] using wordTrace_append hprefix tailTrace_8331480
  have hstable : (prefixWord ++ tailWord_8331480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331480).length < 2 ^ (prefixWord ++ tailWord_8331480).sum := by decide
  have hdescent : baseEnd_8331480 < baseStart_8331480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331514 : List Nat := [3, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3]
def baseStart_8331514 : Nat := 118140960795 + 8331514 * 2 ^ 59
def prefixEnd_8331514 : Nat := 4983230072969 + 3 ^ 40 * 8331514 * 2
def baseEnd_8331514 : Nat := 4278071261663421146859071

theorem tailTrace_8331514 : CollatzResearch.WordTrace tailWord_8331514 prefixEnd_8331514 4278071261663421146859071 := by
  unfold tailWord_8331514
  simp only [CollatzResearch.WordTrace]
  refine ⟨75968819984588790538178399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202583519958903441435142397 75968819984588790538178399)
  ·
    refine ⟨113953229976883185807267599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75968819984588790538178399 113953229976883185807267599)
    ·
      refine ⟨170929844965324778710901399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113953229976883185807267599 170929844965324778710901399)
      ·
        refine ⟨256394767447987168066352099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170929844965324778710901399 256394767447987168066352099)
        ·
          refine ⟨384592151171980752099528149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256394767447987168066352099 384592151171980752099528149)
          ·
            refine ⟨9013878543093298877332691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 384592151171980752099528149 9013878543093298877332691)
            ·
              refine ⟨13520817814639948315999037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9013878543093298877332691 13520817814639948315999037)
              ·
                refine ⟨5070306680489980618499639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13520817814639948315999037 5070306680489980618499639)
                ·
                  refine ⟨7605460020734970927749459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070306680489980618499639 7605460020734970927749459)
                  ·
                    refine ⟨11408190031102456391624189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7605460020734970927749459 11408190031102456391624189)
                    ·
                      refine ⟨4278071261663421146859071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408190031102456391624189 4278071261663421146859071)
                      ·
                        rfl

theorem cell23_8331514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 3, 1, 1, 3].length) (baseStart_8331514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331514 prefixEnd_8331514 := by exact prefixLift 8331514
  have htrace : WordTrace (prefixWord ++ tailWord_8331514) baseStart_8331514 baseEnd_8331514 := by
    simpa [prefixWord, tailWord_8331514, baseEnd_8331514] using wordTrace_append hprefix tailTrace_8331514
  have hstable : (prefixWord ++ tailWord_8331514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331514).length < 2 ^ (prefixWord ++ tailWord_8331514).sum := by decide
  have hdescent : baseEnd_8331514 < baseStart_8331514 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331520 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 5, 2, 2]
def baseStart_8331520 : Nat := 118140960795 + 8331520 * 2 ^ 59
def prefixEnd_8331520 : Nat := 4983230072969 + 3 ^ 40 * 8331520 * 2
def baseEnd_8331520 : Nat := 4278074342547348123384043

theorem tailTrace_8331520 : CollatzResearch.WordTrace tailWord_8331520 prefixEnd_8331520 4278074342547348123384043 := by
  unfold tailWord_8331520
  simp only [CollatzResearch.WordTrace]
  refine ⟨151937749388166712588716007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202583665850888950118288009 151937749388166712588716007)
  ·
    refine ⟨227906624082250068883074011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151937749388166712588716007 227906624082250068883074011)
    ·
      refine ⟨341859936123375103324611017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227906624082250068883074011 341859936123375103324611017)
      ·
        refine ⟨256394952092531327493458263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341859936123375103324611017 256394952092531327493458263)
        ·
          refine ⟨384592428138796991240187395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256394952092531327493458263 384592428138796991240187395)
          ·
            refine ⟨576888642208195486860281093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384592428138796991240187395 576888642208195486860281093)
            ·
              refine ⟨108166620414036653786302705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 576888642208195486860281093 108166620414036653786302705)
              ·
                refine ⟨81124965310527490339727029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108166620414036653786302705 81124965310527490339727029)
                ·
                  refine ⟨7605465497861952219349409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81124965310527490339727029 7605465497861952219349409)
                  ·
                    refine ⟨5704099123396464164512057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605465497861952219349409 5704099123396464164512057)
                    ·
                      refine ⟨4278074342547348123384043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704099123396464164512057 4278074342547348123384043)
                      ·
                        rfl

theorem cell23_8331520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 5, 2, 2].length) (baseStart_8331520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331520 prefixEnd_8331520 := by exact prefixLift 8331520
  have htrace : WordTrace (prefixWord ++ tailWord_8331520) baseStart_8331520 baseEnd_8331520 := by
    simpa [prefixWord, tailWord_8331520, baseEnd_8331520] using wordTrace_append hprefix tailTrace_8331520
  have hstable : (prefixWord ++ tailWord_8331520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331520).length < 2 ^ (prefixWord ++ tailWord_8331520).sum := by decide
  have hdescent : baseEnd_8331520 < baseStart_8331520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331523 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 5]
def baseStart_8331523 : Nat := 118140960795 + 8331523 * 2 ^ 59
def prefixEnd_8331523 : Nat := 4983230072969 + 3 ^ 40 * 8331523 * 2
def baseEnd_8331523 : Nat := 4278075882989311611646529

theorem tailTrace_8331523 : CollatzResearch.WordTrace tailWord_8331523 prefixEnd_8331523 4278075882989311611646529 := by
  unfold tailWord_8331523
  simp only [CollatzResearch.WordTrace]
  refine ⟨303875608195322556689791223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202583738796881704459860815 303875608195322556689791223)
  ·
    refine ⟨455813412292983835034686835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303875608195322556689791223 455813412292983835034686835)
    ·
      refine ⟨683720118439475752552030253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455813412292983835034686835 683720118439475752552030253)
      ·
        refine ⟨256395044414803407207011345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 683720118439475752552030253 256395044414803407207011345)
        ·
          refine ⟨192296283311102555405258509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256395044414803407207011345 192296283311102555405258509)
          ·
            refine ⟨72111106241663458276971941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192296283311102555405258509 72111106241663458276971941)
            ·
              refine ⟨13520832420311898426932239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72111106241663458276971941 13520832420311898426932239)
              ·
                refine ⟨20281248630467847640398359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13520832420311898426932239 20281248630467847640398359)
                ·
                  refine ⟨30421872945701771460597539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20281248630467847640398359 30421872945701771460597539)
                  ·
                    refine ⟨45632809418552657190896309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30421872945701771460597539 45632809418552657190896309)
                    ·
                      refine ⟨4278075882989311611646529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45632809418552657190896309 4278075882989311611646529)
                      ·
                        rfl

theorem cell23_8331523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 5].length) (baseStart_8331523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331523 prefixEnd_8331523 := by exact prefixLift 8331523
  have htrace : WordTrace (prefixWord ++ tailWord_8331523) baseStart_8331523 baseEnd_8331523 := by
    simpa [prefixWord, tailWord_8331523, baseEnd_8331523] using wordTrace_append hprefix tailTrace_8331523
  have hstable : (prefixWord ++ tailWord_8331523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331523).length < 2 ^ (prefixWord ++ tailWord_8331523).sum := by decide
  have hdescent : baseEnd_8331523 < baseStart_8331523 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331537 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 3, 2, 2]
def baseStart_8331537 : Nat := 118140960795 + 8331537 * 2 ^ 59
def prefixEnd_8331537 : Nat := 4983230072969 + 3 ^ 40 * 8331537 * 2
def baseEnd_8331537 : Nat := 4278083071718474556871465

theorem tailTrace_8331537 : CollatzResearch.WordTrace tailWord_8331537 prefixEnd_8331537 4278083071718474556871465 := by
  unfold tailWord_8331537
  simp only [CollatzResearch.WordTrace]
  refine ⟨303876118817271837080800865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202584079211514558053867243 303876118817271837080800865)
  ·
    refine ⟨227907089112953877810600649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303876118817271837080800865 227907089112953877810600649)
    ·
      refine ⟨170930316834715408357950487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227907089112953877810600649 170930316834715408357950487)
      ·
        refine ⟨256395475252073112536925731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170930316834715408357950487 256395475252073112536925731)
        ·
          refine ⟨384593212878109668805388597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256395475252073112536925731 384593212878109668805388597)
          ·
            refine ⟨36055613707322781450505181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384593212878109668805388597 36055613707322781450505181)
            ·
              refine ⟨13520855140246043043939443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36055613707322781450505181 13520855140246043043939443)
              ·
                refine ⟨20281282710369064565909165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13520855140246043043939443 20281282710369064565909165)
                ·
                  refine ⟨7605481016388399212215937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20281282710369064565909165 7605481016388399212215937)
                  ·
                    refine ⟨5704110762291299409161953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605481016388399212215937 5704110762291299409161953)
                    ·
                      refine ⟨4278083071718474556871465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704110762291299409161953 4278083071718474556871465)
                      ·
                        rfl

theorem cell23_8331537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_8331537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331537 prefixEnd_8331537 := by exact prefixLift 8331537
  have htrace : WordTrace (prefixWord ++ tailWord_8331537) baseStart_8331537 baseEnd_8331537 := by
    simpa [prefixWord, tailWord_8331537, baseEnd_8331537] using wordTrace_append hprefix tailTrace_8331537
  have hstable : (prefixWord ++ tailWord_8331537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331537).length < 2 ^ (prefixWord ++ tailWord_8331537).sum := by decide
  have hdescent : baseEnd_8331537 < baseStart_8331537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331543 : List Nat := [1, 1, 3, 4, 1, 3, 2, 8]
def baseStart_8331543 : Nat := 118140960795 + 8331543 * 2 ^ 59
def prefixEnd_8331543 : Nat := 4983230072969 + 3 ^ 40 * 8331543 * 2
def baseEnd_8331543 : Nat := 158447635281570427162831

theorem tailTrace_8331543 : CollatzResearch.WordTrace tailWord_8331543 prefixEnd_8331543 158447635281570427162831 := by
  unfold tailWord_8331543
  simp only [CollatzResearch.WordTrace]
  refine ⟨303876337655250100105519283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202584225103500066737012855 303876337655250100105519283)
  ·
    refine ⟨455814506482875150158278925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303876337655250100105519283 455814506482875150158278925)
    ·
      refine ⟨170930439931078181309354597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455814506482875150158278925 170930439931078181309354597)
      ·
        refine ⟨32049457487077158995503987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170930439931078181309354597 32049457487077158995503987)
        ·
          refine ⟨48074186230615738493255981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32049457487077158995503987 48074186230615738493255981)
          ·
            refine ⟨18027819836480901934970993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48074186230615738493255981 18027819836480901934970993)
            ·
              refine ⟨13520864877360676451228245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18027819836480901934970993 13520864877360676451228245)
              ·
                refine ⟨158447635281570427162831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13520864877360676451228245 158447635281570427162831)
                ·
                  rfl

theorem cell23_8331543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 8].length) (baseStart_8331543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331543 prefixEnd_8331543 := by exact prefixLift 8331543
  have htrace : WordTrace (prefixWord ++ tailWord_8331543) baseStart_8331543 baseEnd_8331543 := by
    simpa [prefixWord, tailWord_8331543, baseEnd_8331543] using wordTrace_append hprefix tailTrace_8331543
  have hstable : (prefixWord ++ tailWord_8331543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331543).length < 2 ^ (prefixWord ++ tailWord_8331543).sum := by decide
  have hdescent : baseEnd_8331543 < baseStart_8331543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331588 : List Nat := [2, 3, 4, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_8331588 : Nat := 118140960795 + 8331588 * 2 ^ 59
def prefixEnd_8331588 : Nat := 4983230072969 + 3 ^ 40 * 8331588 * 2
def baseEnd_8331588 : Nat := 4278109259231853857333731

theorem tailTrace_8331588 : CollatzResearch.WordTrace tailWord_8331588 prefixEnd_8331588 4278109259231853857333731 := by
  unfold tailWord_8331588
  simp only [CollatzResearch.WordTrace]
  refine ⟨151938989470043536395453709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202585319293391381860604945 151938989470043536395453709)
  ·
    refine ⟨56977121051266326148295141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151938989470043536395453709 56977121051266326148295141)
    ·
      refine ⟨10683210197112436152805339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56977121051266326148295141 10683210197112436152805339)
      ·
        refine ⟨16024815295668654229208009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683210197112436152805339 16024815295668654229208009)
        ·
          refine ⟨12018611471751490671906007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16024815295668654229208009 12018611471751490671906007)
          ·
            refine ⟨18027917207627236007859011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12018611471751490671906007 18027917207627236007859011)
            ·
              refine ⟨27041875811440854011788517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18027917207627236007859011 27041875811440854011788517)
              ·
                refine ⟨5070351714645160127210347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27041875811440854011788517 5070351714645160127210347)
                ·
                  refine ⟨7605527571967740190815521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070351714645160127210347 7605527571967740190815521)
                  ·
                    refine ⟨5704145678975805143111641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605527571967740190815521 5704145678975805143111641)
                    ·
                      refine ⟨4278109259231853857333731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704145678975805143111641 4278109259231853857333731)
                      ·
                        rfl

theorem cell23_8331588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_8331588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331588 prefixEnd_8331588 := by exact prefixLift 8331588
  have htrace : WordTrace (prefixWord ++ tailWord_8331588) baseStart_8331588 baseEnd_8331588 := by
    simpa [prefixWord, tailWord_8331588, baseEnd_8331588] using wordTrace_append hprefix tailTrace_8331588
  have hstable : (prefixWord ++ tailWord_8331588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331588).length < 2 ^ (prefixWord ++ tailWord_8331588).sum := by decide
  have hdescent : baseEnd_8331588 < baseStart_8331588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331638 : List Nat := [5, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3]
def baseStart_8331638 : Nat := 118140960795 + 8331638 * 2 ^ 59
def prefixEnd_8331638 : Nat := 4983230072969 + 3 ^ 40 * 8331638 * 2
def baseEnd_8331638 : Nat := 4278134933264578661708501

theorem tailTrace_8331638 : CollatzResearch.WordTrace tailWord_8331638 prefixEnd_8331638 4278134933264578661708501 := by
  unfold tailWord_8331638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18992487661869120708139223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202586535059937287553485045 18992487661869120708139223)
  ·
    refine ⟨28488731492803681062208835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18992487661869120708139223 28488731492803681062208835)
    ·
      refine ⟨42733097239205521593313253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28488731492803681062208835 42733097239205521593313253)
      ·
        refine ⟨8012455732351035298746235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42733097239205521593313253 8012455732351035298746235)
        ·
          refine ⟨12018683598526552948119353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8012455732351035298746235 12018683598526552948119353)
          ·
            refine ⟨9014012698894914711089515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12018683598526552948119353 9014012698894914711089515)
            ·
              refine ⟨13521019048342372066634273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014012698894914711089515 13521019048342372066634273)
              ·
                refine ⟨10140764286256779049975705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13521019048342372066634273 10140764286256779049975705)
                ·
                  refine ⟨7605573214692584287481779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10140764286256779049975705 7605573214692584287481779)
                  ·
                    refine ⟨11408359822038876431222669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7605573214692584287481779 11408359822038876431222669)
                    ·
                      refine ⟨4278134933264578661708501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408359822038876431222669 4278134933264578661708501)
                      ·
                        rfl

theorem cell23_8331638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_8331638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331638 prefixEnd_8331638 := by exact prefixLift 8331638
  have htrace : WordTrace (prefixWord ++ tailWord_8331638) baseStart_8331638 baseEnd_8331638 := by
    simpa [prefixWord, tailWord_8331638, baseEnd_8331638] using wordTrace_append hprefix tailTrace_8331638
  have hstable : (prefixWord ++ tailWord_8331638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331638).length < 2 ^ (prefixWord ++ tailWord_8331638).sum := by decide
  have hdescent : baseEnd_8331638 < baseStart_8331638 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331660 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_8331660 : Nat := 118140960795 + 8331660 * 2 ^ 59
def prefixEnd_8331660 : Nat := 4983230072969 + 3 ^ 40 * 8331660 * 2
def baseEnd_8331660 : Nat := 4278146229838977575633399

theorem tailTrace_8331660 : CollatzResearch.WordTrace tailWord_8331660 prefixEnd_8331660 4278146229838977575633399 := by
  unfold tailWord_8331660
  simp only [CollatzResearch.WordTrace]
  refine ⟨151940302497913114543764217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202587069997217486058352289 151940302497913114543764217)
  ·
    refine ⟨113955226873434835907823163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151940302497913114543764217 113955226873434835907823163)
    ·
      refine ⟨170932840310152253861734745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113955226873434835907823163 170932840310152253861734745)
      ·
        refine ⟨128199630232614190396301059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170932840310152253861734745 128199630232614190396301059)
        ·
          refine ⟨192299445348921285594451589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128199630232614190396301059 192299445348921285594451589)
          ·
            refine ⟨36056146002922741048959673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192299445348921285594451589 36056146002922741048959673)
            ·
              refine ⟨27042109502192055786719755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36056146002922741048959673 27042109502192055786719755)
              ·
                refine ⟨40563164253288083680079633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27042109502192055786719755 40563164253288083680079633)
                ·
                  refine ⟨30422373189966062760059725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40563164253288083680079633 30422373189966062760059725)
                  ·
                    refine ⟨11408389946237273535022397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30422373189966062760059725 11408389946237273535022397)
                    ·
                      refine ⟨4278146229838977575633399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408389946237273535022397 4278146229838977575633399)
                      ·
                        rfl

theorem cell23_8331660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_8331660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331660 prefixEnd_8331660 := by exact prefixLift 8331660
  have htrace : WordTrace (prefixWord ++ tailWord_8331660) baseStart_8331660 baseEnd_8331660 := by
    simpa [prefixWord, tailWord_8331660, baseEnd_8331660] using wordTrace_append hprefix tailTrace_8331660
  have hstable : (prefixWord ++ tailWord_8331660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331660).length < 2 ^ (prefixWord ++ tailWord_8331660).sum := by decide
  have hdescent : baseEnd_8331660 < baseStart_8331660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331734 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_8331734 : Nat := 118140960795 + 8331734 * 2 ^ 59
def prefixEnd_8331734 : Nat := 4983230072969 + 3 ^ 40 * 8331734 * 2
def baseEnd_8331734 : Nat := 4278184227407410286108059

theorem tailTrace_8331734 : CollatzResearch.WordTrace tailWord_8331734 prefixEnd_8331734 4278184227407410286108059 := by
  unfold tailWord_8331734
  simp only [CollatzResearch.WordTrace]
  refine ⟨18992706499847383732857641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202588869331705426483814837 18992706499847383732857641)
  ·
    refine ⟨14244529874885537799643231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18992706499847383732857641 14244529874885537799643231)
    ·
      refine ⟨21366794812328306699464847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14244529874885537799643231 21366794812328306699464847)
      ·
        refine ⟨32050192218492460049197271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21366794812328306699464847 32050192218492460049197271)
        ·
          refine ⟨48075288327738690073795907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32050192218492460049197271 48075288327738690073795907)
          ·
            refine ⟨72112932491608035110693861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48075288327738690073795907 72112932491608035110693861)
            ·
              refine ⟨13521174842176506583255099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72112932491608035110693861 13521174842176506583255099)
              ·
                refine ⟨20281762263264759874882649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13521174842176506583255099 20281762263264759874882649)
                ·
                  refine ⟨15211321697448569906161987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20281762263264759874882649 15211321697448569906161987)
                  ·
                    refine ⟨22816982546172854859242981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15211321697448569906161987 22816982546172854859242981)
                    ·
                      refine ⟨4278184227407410286108059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22816982546172854859242981 4278184227407410286108059)
                      ·
                        rfl

theorem cell23_8331734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_8331734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331734 prefixEnd_8331734 := by exact prefixLift 8331734
  have htrace : WordTrace (prefixWord ++ tailWord_8331734) baseStart_8331734 baseEnd_8331734 := by
    simpa [prefixWord, tailWord_8331734, baseEnd_8331734] using wordTrace_append hprefix tailTrace_8331734
  have hstable : (prefixWord ++ tailWord_8331734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331734).length < 2 ^ (prefixWord ++ tailWord_8331734).sum := by decide
  have hdescent : baseEnd_8331734 < baseStart_8331734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331737 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 3]
def baseStart_8331737 : Nat := 118140960795 + 8331737 * 2 ^ 59
def prefixEnd_8331737 : Nat := 4983230072969 + 3 ^ 40 * 8331737 * 2
def baseEnd_8331737 : Nat := 4278185767849373774370545

theorem tailTrace_8331737 : CollatzResearch.WordTrace tailWord_8331737 prefixEnd_8331737 4278185767849373774370545 := by
  unfold tailWord_8331737
  simp only [CollatzResearch.WordTrace]
  refine ⟨303883413416547271238081465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202588942277698180825387643 303883413416547271238081465)
  ·
    refine ⟨227912560062410453428561099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303883413416547271238081465 227912560062410453428561099)
    ·
      refine ⟨341868840093615680142841649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227912560062410453428561099 341868840093615680142841649)
      ·
        refine ⟨256401630070211760107131237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341868840093615680142841649 256401630070211760107131237)
        ·
          refine ⟨48075305638164705020087107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256401630070211760107131237 48075305638164705020087107)
          ·
            refine ⟨72112958457247057530130661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48075305638164705020087107 72112958457247057530130661)
            ·
              refine ⟨13521179710733823286899499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72112958457247057530130661 13521179710733823286899499)
              ·
                refine ⟨20281769566100734930349249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13521179710733823286899499 20281769566100734930349249)
                ·
                  refine ⟨15211327174575551197761937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20281769566100734930349249 15211327174575551197761937)
                  ·
                    refine ⟨11408495380931663398321453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15211327174575551197761937 11408495380931663398321453)
                    ·
                      refine ⟨4278185767849373774370545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408495380931663398321453 4278185767849373774370545)
                      ·
                        rfl

theorem cell23_8331737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_8331737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331737 prefixEnd_8331737 := by exact prefixLift 8331737
  have htrace : WordTrace (prefixWord ++ tailWord_8331737) baseStart_8331737 baseEnd_8331737 := by
    simpa [prefixWord, tailWord_8331737, baseEnd_8331737] using wordTrace_append hprefix tailTrace_8331737
  have hstable : (prefixWord ++ tailWord_8331737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331737).length < 2 ^ (prefixWord ++ tailWord_8331737).sum := by decide
  have hdescent : baseEnd_8331737 < baseStart_8331737 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331757 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 6]
def baseStart_8331757 : Nat := 118140960795 + 8331757 * 2 ^ 59
def prefixEnd_8331757 : Nat := 4983230072969 + 3 ^ 40 * 8331757 * 2
def baseEnd_8331757 : Nat := 475355115273607077346717

theorem tailTrace_8331757 : CollatzResearch.WordTrace tailWord_8331757 prefixEnd_8331757 475355115273607077346717 := by
  unfold tailWord_8331757
  simp only [CollatzResearch.WordTrace]
  refine ⟨303884142876474814653809525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202589428584316543102539683 303884142876474814653809525)
  ·
    refine ⟨28489138394669513873794643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 303884142876474814653809525 28489138394669513873794643)
    ·
      refine ⟨42733707592004270810691965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28489138394669513873794643 42733707592004270810691965)
      ·
        refine ⟨16025140347001601554009487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42733707592004270810691965 16025140347001601554009487)
        ·
          refine ⟨24037710520502402331014231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16025140347001601554009487 24037710520502402331014231)
          ·
            refine ⟨36056565780753603496521347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24037710520502402331014231 36056565780753603496521347)
            ·
              refine ⟨54084848671130405244782021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36056565780753603496521347 54084848671130405244782021)
              ·
                refine ⟨10140909125836950983396629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54084848671130405244782021 10140909125836950983396629)
                ·
                  refine ⟨475355115273607077346717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10140909125836950983396629 475355115273607077346717)
                  ·
                    rfl

theorem cell23_8331757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_8331757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331757 prefixEnd_8331757 := by exact prefixLift 8331757
  have htrace : WordTrace (prefixWord ++ tailWord_8331757) baseStart_8331757 baseEnd_8331757 := by
    simpa [prefixWord, tailWord_8331757, baseEnd_8331757] using wordTrace_append hprefix tailTrace_8331757
  have hstable : (prefixWord ++ tailWord_8331757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331757).length < 2 ^ (prefixWord ++ tailWord_8331757).sum := by decide
  have hdescent : baseEnd_8331757 < baseStart_8331757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331804 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_8331804 : Nat := 118140960795 + 8331804 * 2 ^ 59
def prefixEnd_8331804 : Nat := 4983230072969 + 3 ^ 40 * 8331804 * 2
def baseEnd_8331804 : Nat := 1426073390351075004077579

theorem tailTrace_8331804 : CollatzResearch.WordTrace tailWord_8331804 prefixEnd_8331804 1426073390351075004077579 := by
  unfold tailWord_8331804
  simp only [CollatzResearch.WordTrace]
  refine ⟨151942928553652270840385233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202590571404869694453846977 151942928553652270840385233)
  ·
    refine ⟨113957196415239203130288925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151942928553652270840385233 113957196415239203130288925)
    ·
      refine ⟨42733948655714701173858347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113957196415239203130288925 42733948655714701173858347)
      ·
        refine ⟨64100922983572051760787521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42733948655714701173858347 64100922983572051760787521)
        ·
          refine ⟨48075692237679038820590641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64100922983572051760787521 48075692237679038820590641)
          ·
            refine ⟨36056769178259279115442981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48075692237679038820590641 36056769178259279115442981)
            ·
              refine ⟨6760644220923614834145559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36056769178259279115442981 6760644220923614834145559)
              ·
                refine ⟨10140966331385422251218339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760644220923614834145559 10140966331385422251218339)
                ·
                  refine ⟨15211449497078133376827509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10140966331385422251218339 15211449497078133376827509)
                  ·
                    refine ⟨1426073390351075004077579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15211449497078133376827509 1426073390351075004077579)
                    ·
                      rfl

theorem cell23_8331804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_8331804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331804 prefixEnd_8331804 := by exact prefixLift 8331804
  have htrace : WordTrace (prefixWord ++ tailWord_8331804) baseStart_8331804 baseEnd_8331804 := by
    simpa [prefixWord, tailWord_8331804, baseEnd_8331804] using wordTrace_append hprefix tailTrace_8331804
  have hstable : (prefixWord ++ tailWord_8331804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331804).length < 2 ^ (prefixWord ++ tailWord_8331804).sum := by decide
  have hdescent : baseEnd_8331804 < baseStart_8331804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331820 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_8331820 : Nat := 118140960795 + 8331820 * 2 ^ 59
def prefixEnd_8331820 : Nat := 4983230072969 + 3 ^ 40 * 8331820 * 2
def baseEnd_8331820 : Nat := 4278228386743696949632663

theorem tailTrace_8331820 : CollatzResearch.WordTrace tailWord_8331820 prefixEnd_8331820 4278228386743696949632663 := by
  unfold tailWord_8331820
  simp only [CollatzResearch.WordTrace]
  refine ⟨151943220337623288206676457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202590960450164384275568609 151943220337623288206676457)
  ·
    refine ⟨113957415253217466155007343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151943220337623288206676457 113957415253217466155007343)
    ·
      refine ⟨170936122879826199232511015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113957415253217466155007343 170936122879826199232511015)
      ·
        refine ⟨256404184319739298848766523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170936122879826199232511015 256404184319739298848766523)
        ·
          refine ⟨384606276479608948273149785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256404184319739298848766523 384606276479608948273149785)
          ·
            refine ⟨288454707359706711204862339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384606276479608948273149785 288454707359706711204862339)
            ·
              refine ⟨432682061039560066807293509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288454707359706711204862339 432682061039560066807293509)
              ·
                refine ⟨81127886444917512526367533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 432682061039560066807293509 81127886444917512526367533)
                ·
                  refine ⟨30422957416844067197387825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81127886444917512526367533 30422957416844067197387825)
                  ·
                    refine ⟨22817218062633050398040869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30422957416844067197387825 22817218062633050398040869)
                    ·
                      refine ⟨4278228386743696949632663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22817218062633050398040869 4278228386743696949632663)
                      ·
                        rfl

theorem cell23_8331820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_8331820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331820 prefixEnd_8331820 := by exact prefixLift 8331820
  have htrace : WordTrace (prefixWord ++ tailWord_8331820) baseStart_8331820 baseEnd_8331820 := by
    simpa [prefixWord, tailWord_8331820, baseEnd_8331820] using wordTrace_append hprefix tailTrace_8331820
  have hstable : (prefixWord ++ tailWord_8331820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331820).length < 2 ^ (prefixWord ++ tailWord_8331820).sum := by decide
  have hdescent : baseEnd_8331820 < baseStart_8331820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331824 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 3, 2, 2]
def baseStart_8331824 : Nat := 118140960795 + 8331824 * 2 ^ 59
def prefixEnd_8331824 : Nat := 4983230072969 + 3 ^ 40 * 8331824 * 2
def baseEnd_8331824 : Nat := 4278230440666314933982645

theorem tailTrace_8331824 : CollatzResearch.WordTrace tailWord_8331824 prefixEnd_8331824 4278230440666314933982645 := by
  unfold tailWord_8331824
  simp only [CollatzResearch.WordTrace]
  refine ⟨151943293283616042548249263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202591057711488056730999017 151943293283616042548249263)
  ·
    refine ⟨227914939925424063822373895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151943293283616042548249263 227914939925424063822373895)
    ·
      refine ⟨341872409888136095733560843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227914939925424063822373895 341872409888136095733560843)
      ·
        refine ⟨512808614832204143600341265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341872409888136095733560843 512808614832204143600341265)
        ·
          refine ⟨384606461124153107700255949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512808614832204143600341265 384606461124153107700255949)
          ·
            refine ⟨144227422921557415387595981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 384606461124153107700255949 144227422921557415387595981)
            ·
              refine ⟨54085283595584030770348493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144227422921557415387595981 54085283595584030770348493)
              ·
                refine ⟨20281981348344011538880685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54085283595584030770348493 20281981348344011538880685)
                ·
                  refine ⟨7605743005629004327080257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20281981348344011538880685 7605743005629004327080257)
                  ·
                    refine ⟨5704307254221753245310193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605743005629004327080257 5704307254221753245310193)
                    ·
                      refine ⟨4278230440666314933982645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704307254221753245310193 4278230440666314933982645)
                      ·
                        rfl

theorem cell23_8331824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 3, 2, 2].length) (baseStart_8331824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331824 prefixEnd_8331824 := by exact prefixLift 8331824
  have htrace : WordTrace (prefixWord ++ tailWord_8331824) baseStart_8331824 baseEnd_8331824 := by
    simpa [prefixWord, tailWord_8331824, baseEnd_8331824] using wordTrace_append hprefix tailTrace_8331824
  have hstable : (prefixWord ++ tailWord_8331824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331824).length < 2 ^ (prefixWord ++ tailWord_8331824).sum := by decide
  have hdescent : baseEnd_8331824 < baseStart_8331824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331837 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_8331837 : Nat := 118140960795 + 8331837 * 2 ^ 59
def prefixEnd_8331837 : Nat := 4983230072969 + 3 ^ 40 * 8331837 * 2
def baseEnd_8331837 : Nat := 4278237115914823383120085

theorem tailTrace_8331837 : CollatzResearch.WordTrace tailWord_8331837 prefixEnd_8331837 4278237115914823383120085 := by
  unfold tailWord_8331837
  simp only [CollatzResearch.WordTrace]
  refine ⟨303887060716184988316721765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202591373810789992211147843 303887060716184988316721765)
  ·
    refine ⟨56978823884284685309385331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303887060716184988316721765 56978823884284685309385331)
    ·
      refine ⟨85468235826427027964077997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56978823884284685309385331 85468235826427027964077997)
      ·
        refine ⟨32050588434910135486529249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85468235826427027964077997 32050588434910135486529249)
        ·
          refine ⟨24037941326182601614896937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32050588434910135486529249 24037941326182601614896937)
          ·
            refine ⟨18028455994636951211172703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24037941326182601614896937 18028455994636951211172703)
            ·
              refine ⟨27042683991955426816759055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18028455994636951211172703 27042683991955426816759055)
              ·
                refine ⟨40564025987933140225138583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27042683991955426816759055 40564025987933140225138583)
                ·
                  refine ⟨60846038981899710337707875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40564025987933140225138583 60846038981899710337707875)
                  ·
                    refine ⟨91269058472849565506561813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60846038981899710337707875 91269058472849565506561813)
                    ·
                      refine ⟨4278237115914823383120085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91269058472849565506561813 4278237115914823383120085)
                      ·
                        rfl

theorem cell23_8331837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_8331837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331837 prefixEnd_8331837 := by exact prefixLift 8331837
  have htrace : WordTrace (prefixWord ++ tailWord_8331837) baseStart_8331837 baseEnd_8331837 := by
    simpa [prefixWord, tailWord_8331837, baseEnd_8331837] using wordTrace_append hprefix tailTrace_8331837
  have hstable : (prefixWord ++ tailWord_8331837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331837).length < 2 ^ (prefixWord ++ tailWord_8331837).sum := by decide
  have hdescent : baseEnd_8331837 < baseStart_8331837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331841 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_8331841 : Nat := 118140960795 + 8331841 * 2 ^ 59
def prefixEnd_8331841 : Nat := 4983230072969 + 3 ^ 40 * 8331841 * 2
def baseEnd_8331841 : Nat := 4278239169837441367470067

theorem tailTrace_8331841 : CollatzResearch.WordTrace tailWord_8331841 prefixEnd_8331841 4278239169837441367470067 := by
  unfold tailWord_8331841
  simp only [CollatzResearch.WordTrace]
  refine ⟨303887206608170496999867377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202591471072113664666578251 303887206608170496999867377)
  ·
    refine ⟨227915404956127872749900533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303887206608170496999867377 227915404956127872749900533)
    ·
      refine ⟨21367069214636988070303175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227915404956127872749900533 21367069214636988070303175)
      ·
        refine ⟨32050603821955482105454763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21367069214636988070303175 32050603821955482105454763)
        ·
          refine ⟨48075905732933223158182145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32050603821955482105454763 48075905732933223158182145)
          ·
            refine ⟨36056929299699917368636609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48075905732933223158182145 36056929299699917368636609)
            ·
              refine ⟨27042696974774938026477457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36056929299699917368636609 27042696974774938026477457)
              ·
                refine ⟨20282022731081203519858093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27042696974774938026477457 20282022731081203519858093)
                ·
                  refine ⟨7605758524155451319946785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20282022731081203519858093 7605758524155451319946785)
                  ·
                    refine ⟨5704318893116588489960089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7605758524155451319946785 5704318893116588489960089)
                    ·
                      refine ⟨4278239169837441367470067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704318893116588489960089 4278239169837441367470067)
                      ·
                        rfl

theorem cell23_8331841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_8331841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331841 prefixEnd_8331841 := by exact prefixLift 8331841
  have htrace : WordTrace (prefixWord ++ tailWord_8331841) baseStart_8331841 baseEnd_8331841 := by
    simpa [prefixWord, tailWord_8331841, baseEnd_8331841] using wordTrace_append hprefix tailTrace_8331841
  have hstable : (prefixWord ++ tailWord_8331841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331841).length < 2 ^ (prefixWord ++ tailWord_8331841).sum := by decide
  have hdescent : baseEnd_8331841 < baseStart_8331841 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331847 : List Nat := [1, 1, 4, 1, 4, 1, 4, 7]
def baseStart_8331847 : Nat := 118140960795 + 8331847 * 2 ^ 59
def prefixEnd_8331847 : Nat := 4983230072969 + 3 ^ 40 * 8331847 * 2
def baseEnd_8331847 : Nat := 158453416693384012740557

theorem tailTrace_8331847 : CollatzResearch.WordTrace tailWord_8331847 prefixEnd_8331847 158453416693384012740557 := by
  unfold tailWord_8331847
  simp only [CollatzResearch.WordTrace]
  refine ⟨303887425446148760024585795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202591616964099173349723863 303887425446148760024585795)
  ·
    refine ⟨455831138169223140036878693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303887425446148760024585795 455831138169223140036878693)
    ·
      refine ⟨85468338406729338756914755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455831138169223140036878693 85468338406729338756914755)
      ·
        refine ⟨128202507610094008135372133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85468338406729338756914755 128202507610094008135372133)
        ·
          refine ⟨24037970176892626525382275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128202507610094008135372133 24037970176892626525382275)
          ·
            refine ⟨36056955265338939788073413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24037970176892626525382275 36056955265338939788073413)
            ·
              refine ⟨6760679112251051210263765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36056955265338939788073413 6760679112251051210263765)
              ·
                refine ⟨158453416693384012740557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6760679112251051210263765 158453416693384012740557)
                ·
                  rfl

theorem cell23_8331847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 7].length) (baseStart_8331847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331847 prefixEnd_8331847 := by exact prefixLift 8331847
  have htrace : WordTrace (prefixWord ++ tailWord_8331847) baseStart_8331847 baseEnd_8331847 := by
    simpa [prefixWord, tailWord_8331847, baseEnd_8331847] using wordTrace_append hprefix tailTrace_8331847
  have hstable : (prefixWord ++ tailWord_8331847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331847).length < 2 ^ (prefixWord ++ tailWord_8331847).sum := by decide
  have hdescent : baseEnd_8331847 < baseStart_8331847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331901 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_8331901 : Nat := 118140960795 + 8331901 * 2 ^ 59
def prefixEnd_8331901 : Nat := 4983230072969 + 3 ^ 40 * 8331901 * 2
def baseEnd_8331901 : Nat := 4278269978676711132719791

theorem tailTrace_8331901 : CollatzResearch.WordTrace tailWord_8331901 prefixEnd_8331901 4278269978676711132719791 := by
  unfold tailWord_8331901
  simp only [CollatzResearch.WordTrace]
  refine ⟨303889394987953127247051557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202592929991968751498034371 303889394987953127247051557)
  ·
    refine ⟨56979261560241211358822167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303889394987953127247051557 56979261560241211358822167)
    ·
      refine ⟨85468892340361817038233251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56979261560241211358822167 85468892340361817038233251)
      ·
        refine ⟨128203338510542725557349877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85468892340361817038233251 128203338510542725557349877)
        ·
          refine ⟨12019062985363380521001551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128203338510542725557349877 12019062985363380521001551)
          ·
            refine ⟨18028594478045070781502327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12019062985363380521001551 18028594478045070781502327)
            ·
              refine ⟨27042891717067606172253491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18028594478045070781502327 27042891717067606172253491)
              ·
                refine ⟨40564337575601409258380237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27042891717067606172253491 40564337575601409258380237)
                ·
                  refine ⟨15211626590850528471892589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40564337575601409258380237 15211626590850528471892589)
                  ·
                    refine ⟨5704359971568948176959721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15211626590850528471892589 5704359971568948176959721)
                    ·
                      refine ⟨4278269978676711132719791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704359971568948176959721 4278269978676711132719791)
                      ·
                        rfl

theorem cell23_8331901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_8331901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331901 prefixEnd_8331901 := by exact prefixLift 8331901
  have htrace : WordTrace (prefixWord ++ tailWord_8331901) baseStart_8331901 baseEnd_8331901 := by
    simpa [prefixWord, tailWord_8331901, baseEnd_8331901] using wordTrace_append hprefix tailTrace_8331901
  have hstable : (prefixWord ++ tailWord_8331901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331901).length < 2 ^ (prefixWord ++ tailWord_8331901).sum := by decide
  have hdescent : baseEnd_8331901 < baseStart_8331901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331918 : List Nat := [4, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_8331918 : Nat := 118140960795 + 8331918 * 2 ^ 59
def prefixEnd_8331918 : Nat := 4983230072969 + 3 ^ 40 * 8331918 * 2
def baseEnd_8331918 : Nat := 4278278707847837566207213

theorem tailTrace_8331918 : CollatzResearch.WordTrace tailWord_8331918 prefixEnd_8331918 4278278707847837566207213 := by
  unfold tailWord_8331918
  simp only [CollatzResearch.WordTrace]
  refine ⟨37986251878611442393802551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202593343352594359433613605 37986251878611442393802551)
  ·
    refine ⟨56979377817917163590703827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37986251878611442393802551 56979377817917163590703827)
    ·
      refine ⟨85469066726875745386055741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56979377817917163590703827 85469066726875745386055741)
      ·
        refine ⟨32050900022578404519770903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85469066726875745386055741 32050900022578404519770903)
        ·
          refine ⟨48076350033867606779656355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32050900022578404519770903 48076350033867606779656355)
          ·
            refine ⟨72114525050801410169484533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48076350033867606779656355 72114525050801410169484533)
            ·
              refine ⟨6760736723512632203389175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72114525050801410169484533 6760736723512632203389175)
              ·
                refine ⟨10141105085268948305083763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760736723512632203389175 10141105085268948305083763)
                ·
                  refine ⟨15211657627903422457625645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10141105085268948305083763 15211657627903422457625645)
                  ·
                    refine ⟨5704371610463783421609617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15211657627903422457625645 5704371610463783421609617)
                    ·
                      refine ⟨4278278707847837566207213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704371610463783421609617 4278278707847837566207213)
                      ·
                        rfl

theorem cell23_8331918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_8331918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331918 prefixEnd_8331918 := by exact prefixLift 8331918
  have htrace : WordTrace (prefixWord ++ tailWord_8331918) baseStart_8331918 baseEnd_8331918 := by
    simpa [prefixWord, tailWord_8331918, baseEnd_8331918] using wordTrace_append hprefix tailTrace_8331918
  have hstable : (prefixWord ++ tailWord_8331918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331918).length < 2 ^ (prefixWord ++ tailWord_8331918).sum := by decide
  have hdescent : baseEnd_8331918 < baseStart_8331918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331927 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_8331927 : Nat := 118140960795 + 8331927 * 2 ^ 59
def prefixEnd_8331927 : Nat := 4983230072969 + 3 ^ 40 * 8331927 * 2
def baseEnd_8331927 : Nat := 4278283329173728030994671

theorem tailTrace_8331927 : CollatzResearch.WordTrace tailWord_8331927 prefixEnd_8331927 4278283329173728030994671 := by
  unfold tailWord_8331927
  simp only [CollatzResearch.WordTrace]
  refine ⟨303890343285858933687498035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202593562190572622458332023 303890343285858933687498035)
  ·
    refine ⟨455835514928788400531247053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303890343285858933687498035 455835514928788400531247053)
    ·
      refine ⟨170938318098295650199217645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455835514928788400531247053 170938318098295650199217645)
      ·
        refine ⟨64101869286860868824706617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170938318098295650199217645 64101869286860868824706617)
        ·
          refine ⟨48076401965145651618529963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64101869286860868824706617 48076401965145651618529963)
          ·
            refine ⟨72114602947718477427794945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48076401965145651618529963 72114602947718477427794945)
            ·
              refine ⟨54085952210788858070846209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72114602947718477427794945 54085952210788858070846209)
              ·
                refine ⟨40564464158091643553134657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54085952210788858070846209 40564464158091643553134657)
                ·
                  refine ⟨30423348118568732664850993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40564464158091643553134657 30423348118568732664850993)
                  ·
                    refine ⟨22817511088926549498638245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30423348118568732664850993 22817511088926549498638245)
                    ·
                      refine ⟨4278283329173728030994671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22817511088926549498638245 4278283329173728030994671)
                      ·
                        rfl

theorem cell23_8331927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_8331927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331927 prefixEnd_8331927 := by exact prefixLift 8331927
  have htrace : WordTrace (prefixWord ++ tailWord_8331927) baseStart_8331927 baseEnd_8331927 := by
    simpa [prefixWord, tailWord_8331927, baseEnd_8331927] using wordTrace_append hprefix tailTrace_8331927
  have hstable : (prefixWord ++ tailWord_8331927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331927).length < 2 ^ (prefixWord ++ tailWord_8331927).sum := by decide
  have hdescent : baseEnd_8331927 < baseStart_8331927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331934 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_8331934 : Nat := 118140960795 + 8331934 * 2 ^ 59
def prefixEnd_8331934 : Nat := 4983230072969 + 3 ^ 40 * 8331934 * 2
def baseEnd_8331934 : Nat := 4278286923538309503607139

theorem tailTrace_8331934 : CollatzResearch.WordTrace tailWord_8331934 prefixEnd_8331934 4278286923538309503607139 := by
  unfold tailWord_8331934
  simp only [CollatzResearch.WordTrace]
  refine ⟨37986324824604196735375357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202593732397889049255335237 37986324824604196735375357)
  ·
    refine ⟨14244871809226573775765759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37986324824604196735375357 14244871809226573775765759)
    ·
      refine ⟨21367307713839860663648639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14244871809226573775765759 21367307713839860663648639)
      ·
        refine ⟨32050961570759790995472959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21367307713839860663648639 32050961570759790995472959)
        ·
          refine ⟨48076442356139686493209439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32050961570759790995472959 48076442356139686493209439)
          ·
            refine ⟨72114663534209529739814159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48076442356139686493209439 72114663534209529739814159)
            ·
              refine ⟨108171995301314294609721239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72114663534209529739814159 108171995301314294609721239)
              ·
                refine ⟨162257992951971441914581859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108171995301314294609721239 162257992951971441914581859)
                ·
                  refine ⟨243386989427957162871872789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 162257992951971441914581859 243386989427957162871872789)
                  ·
                    refine ⟨11408765129435492009619037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 243386989427957162871872789 11408765129435492009619037)
                    ·
                      refine ⟨4278286923538309503607139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408765129435492009619037 4278286923538309503607139)
                      ·
                        rfl

theorem cell23_8331934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_8331934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331934 prefixEnd_8331934 := by exact prefixLift 8331934
  have htrace : WordTrace (prefixWord ++ tailWord_8331934) baseStart_8331934 baseEnd_8331934 := by
    simpa [prefixWord, tailWord_8331934, baseEnd_8331934] using wordTrace_append hprefix tailTrace_8331934
  have hstable : (prefixWord ++ tailWord_8331934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331934).length < 2 ^ (prefixWord ++ tailWord_8331934).sum := by decide
  have hdescent : baseEnd_8331934 < baseStart_8331934 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331967 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 1, 7]
def baseStart_8331967 : Nat := 118140960795 + 8331967 * 2 ^ 59
def prefixEnd_8331967 : Nat := 4983230072969 + 3 ^ 40 * 8331967 * 2
def baseEnd_8331967 : Nat := 1426101289466635958164829

theorem tailTrace_8331967 : CollatzResearch.WordTrace tailWord_8331967 prefixEnd_8331967 1426101289466635958164829 := by
  unfold tailWord_8331967
  simp only [CollatzResearch.WordTrace]
  refine ⟨303891802205714020518954155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202594534803809347012636103 303891802205714020518954155)
  ·
    refine ⟨455837703308571030778431233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303891802205714020518954155 455837703308571030778431233)
    ·
      refine ⟨341878277481428273083823425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455837703308571030778431233 341878277481428273083823425)
      ·
        refine ⟨256408708111071204812867569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341878277481428273083823425 256408708111071204812867569)
        ·
          refine ⟨192306531083303403609650677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256408708111071204812867569 192306531083303403609650677)
          ·
            refine ⟨18028737289059694088404751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192306531083303403609650677 18028737289059694088404751)
            ·
              refine ⟨27043105933589541132607127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18028737289059694088404751 27043105933589541132607127)
              ·
                refine ⟨40564658900384311698910691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27043105933589541132607127 40564658900384311698910691)
                ·
                  refine ⟨60846988350576467548366037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40564658900384311698910691 60846988350576467548366037)
                  ·
                    refine ⟨1426101289466635958164829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60846988350576467548366037 1426101289466635958164829)
                    ·
                      rfl

theorem cell23_8331967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_8331967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331967 prefixEnd_8331967 := by exact prefixLift 8331967
  have htrace : WordTrace (prefixWord ++ tailWord_8331967) baseStart_8331967 baseEnd_8331967 := by
    simpa [prefixWord, tailWord_8331967, baseEnd_8331967] using wordTrace_append hprefix tailTrace_8331967
  have hstable : (prefixWord ++ tailWord_8331967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331967).length < 2 ^ (prefixWord ++ tailWord_8331967).sum := by decide
  have hdescent : baseEnd_8331967 < baseStart_8331967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8331969 : List Nat := [1, 2, 6, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_8331969 : Nat := 118140960795 + 8331969 * 2 ^ 59
def prefixEnd_8331969 : Nat := 4983230072969 + 3 ^ 40 * 8331969 * 2
def baseEnd_8331969 : Nat := 4278304895361216866669479

theorem tailTrace_8331969 : CollatzResearch.WordTrace tailWord_8331969 prefixEnd_8331969 4278304895361216866669479 := by
  unfold tailWord_8331969
  simp only [CollatzResearch.WordTrace]
  refine ⟨303891875151706774860526961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202594583434471183240351307 303891875151706774860526961)
  ·
    refine ⟨227918906363780081145395221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303891875151706774860526961 227918906363780081145395221)
    ·
      refine ⟨10683698735802191303690401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227918906363780081145395221 10683698735802191303690401)
      ·
        refine ⟨8012774051851643477767801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10683698735802191303690401 8012774051851643477767801)
        ·
          refine ⟨6009580538888732608325851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8012774051851643477767801 6009580538888732608325851)
          ·
            refine ⟨9014370808333098912488777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009580538888732608325851 9014370808333098912488777)
            ·
              refine ⟨6760778106249824184366583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9014370808333098912488777 6760778106249824184366583)
              ·
                refine ⟨10141167159374736276549875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760778106249824184366583 10141167159374736276549875)
                ·
                  refine ⟨15211750739062104414824813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10141167159374736276549875 15211750739062104414824813)
                  ·
                    refine ⟨5704406527148289155559305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15211750739062104414824813 5704406527148289155559305)
                    ·
                      refine ⟨4278304895361216866669479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704406527148289155559305 4278304895361216866669479)
                      ·
                        rfl

theorem cell23_8331969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_8331969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8331969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8331969 prefixEnd_8331969 := by exact prefixLift 8331969
  have htrace : WordTrace (prefixWord ++ tailWord_8331969) baseStart_8331969 baseEnd_8331969 := by
    simpa [prefixWord, tailWord_8331969, baseEnd_8331969] using wordTrace_append hprefix tailTrace_8331969
  have hstable : (prefixWord ++ tailWord_8331969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8331969).length < 2 ^ (prefixWord ++ tailWord_8331969).sum := by decide
  have hdescent : baseEnd_8331969 < baseStart_8331969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8331969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332017 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_8332017 : Nat := 118140960795 + 8332017 * 2 ^ 59
def prefixEnd_8332017 : Nat := 4983230072969 + 3 ^ 40 * 8332017 * 2
def baseEnd_8332017 : Nat := 4278329542432632678869257

theorem tailTrace_8332017 : CollatzResearch.WordTrace tailWord_8332017 prefixEnd_8332017 4278329542432632678869257 := by
  unfold tailWord_8332017
  simp only [CollatzResearch.WordTrace]
  refine ⟨303893625855532879058274305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202595750570355252705516203 303893625855532879058274305)
  ·
    refine ⟨227920219391649659293705729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303893625855532879058274305 227920219391649659293705729)
    ·
      refine ⟨170940164543737244470279297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227920219391649659293705729 170940164543737244470279297)
      ·
        refine ⟨128205123407802933352709473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170940164543737244470279297 128205123407802933352709473)
        ·
          refine ⟨96153842555852200014532105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128205123407802933352709473 96153842555852200014532105)
          ·
            refine ⟨72115381916889150010899079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96153842555852200014532105 72115381916889150010899079)
            ·
              refine ⟨108173072875333725016348619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72115381916889150010899079 108173072875333725016348619)
              ·
                refine ⟨162259609313000587524522929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108173072875333725016348619 162259609313000587524522929)
                ·
                  refine ⟨121694706984750440643392197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162259609313000587524522929 121694706984750440643392197)
                  ·
                    refine ⟨22817757559640707620636037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121694706984750440643392197 22817757559640707620636037)
                    ·
                      refine ⟨4278329542432632678869257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22817757559640707620636037 4278329542432632678869257)
                      ·
                        rfl

theorem cell23_8332017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_8332017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332017 prefixEnd_8332017 := by exact prefixLift 8332017
  have htrace : WordTrace (prefixWord ++ tailWord_8332017) baseStart_8332017 baseEnd_8332017 := by
    simpa [prefixWord, tailWord_8332017, baseEnd_8332017] using wordTrace_append hprefix tailTrace_8332017
  have hstable : (prefixWord ++ tailWord_8332017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332017).length < 2 ^ (prefixWord ++ tailWord_8332017).sum := by decide
  have hdescent : baseEnd_8332017 < baseStart_8332017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332024 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_8332024 : Nat := 118140960795 + 8332024 * 2 ^ 59
def prefixEnd_8332024 : Nat := 4983230072969 + 3 ^ 40 * 8332024 * 2
def baseEnd_8332024 : Nat := 4278333136797214151481725

theorem tailTrace_8332024 : CollatzResearch.WordTrace tailWord_8332024 prefixEnd_8332024 4278333136797214151481725 := by
  unfold tailWord_8332024
  simp only [CollatzResearch.WordTrace]
  refine ⟨151946940583253759626889563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202595920777671679502519417 151946940583253759626889563)
  ·
    refine ⟨227920410874880639440334345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151946940583253759626889563 227920410874880639440334345)
    ·
      refine ⟨170940308156160479580250759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227920410874880639440334345 170940308156160479580250759)
      ·
        refine ⟨256410462234240719370376139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170940308156160479580250759 256410462234240719370376139)
        ·
          refine ⟨384615693351361079055564209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256410462234240719370376139 384615693351361079055564209)
          ·
            refine ⟨288461770013520809291673157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384615693351361079055564209 288461770013520809291673157)
            ·
              refine ⟨54086581877535151742188717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288461770013520809291673157 54086581877535151742188717)
              ·
                refine ⟨20282468204075681903320769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54086581877535151742188717 20282468204075681903320769)
                ·
                  refine ⟨15211851153056761427490577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20282468204075681903320769 15211851153056761427490577)
                  ·
                    refine ⟨11408888364792571070617933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15211851153056761427490577 11408888364792571070617933)
                    ·
                      refine ⟨4278333136797214151481725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408888364792571070617933 4278333136797214151481725)
                      ·
                        rfl

theorem cell23_8332024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_8332024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332024 prefixEnd_8332024 := by exact prefixLift 8332024
  have htrace : WordTrace (prefixWord ++ tailWord_8332024) baseStart_8332024 baseEnd_8332024 := by
    simpa [prefixWord, tailWord_8332024, baseEnd_8332024] using wordTrace_append hprefix tailTrace_8332024
  have hstable : (prefixWord ++ tailWord_8332024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332024).length < 2 ^ (prefixWord ++ tailWord_8332024).sum := by decide
  have hdescent : baseEnd_8332024 < baseStart_8332024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332088 : List Nat := [2, 1, 2, 1, 3, 2, 2, 5, 1, 1, 3]
def baseStart_8332088 : Nat := 118140960795 + 8332088 * 2 ^ 59
def prefixEnd_8332088 : Nat := 4983230072969 + 3 ^ 40 * 8332088 * 2
def baseEnd_8332088 : Nat := 4278365999559101901081431

theorem tailTrace_8332088 : CollatzResearch.WordTrace tailWord_8332088 prefixEnd_8332088 4278365999559101901081431 := by
  unfold tailWord_8332088
  simp only [CollatzResearch.WordTrace]
  refine ⟨151948107719137829092054459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202597476958850438789405945 151948107719137829092054459)
  ·
    refine ⟨227922161578706743638081689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151948107719137829092054459 227922161578706743638081689)
    ·
      refine ⟨170941621184030057728561267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227922161578706743638081689 170941621184030057728561267)
      ·
        refine ⟨256412431776045086592841901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170941621184030057728561267 256412431776045086592841901)
        ·
          refine ⟨96154661916016907472315713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256412431776045086592841901 96154661916016907472315713)
          ·
            refine ⟨72115996437012680604236785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96154661916016907472315713 72115996437012680604236785)
            ·
              refine ⟨54086997327759510453177589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72115996437012680604236785 54086997327759510453177589)
              ·
                refine ⟨5070655999477454104985399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54086997327759510453177589 5070655999477454104985399)
                ·
                  refine ⟨7605983999216181157478099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070655999477454104985399 7605983999216181157478099)
                  ·
                    refine ⟨11408975998824271736217149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7605983999216181157478099 11408975998824271736217149)
                    ·
                      refine ⟨4278365999559101901081431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408975998824271736217149 4278365999559101901081431)
                      ·
                        rfl

theorem cell23_8332088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 5, 1, 1, 3].length) (baseStart_8332088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332088 prefixEnd_8332088 := by exact prefixLift 8332088
  have htrace : WordTrace (prefixWord ++ tailWord_8332088) baseStart_8332088 baseEnd_8332088 := by
    simpa [prefixWord, tailWord_8332088, baseEnd_8332088] using wordTrace_append hprefix tailTrace_8332088
  have hstable : (prefixWord ++ tailWord_8332088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332088).length < 2 ^ (prefixWord ++ tailWord_8332088).sum := by decide
  have hdescent : baseEnd_8332088 < baseStart_8332088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332105 : List Nat := [1, 2, 1, 1, 2, 5, 4, 2, 1, 1, 3]
def baseStart_8332105 : Nat := 118140960795 + 8332105 * 2 ^ 59
def prefixEnd_8332105 : Nat := 4983230072969 + 3 ^ 40 * 8332105 * 2
def baseEnd_8332105 : Nat := 4278374728730228334568853

theorem tailTrace_8332105 : CollatzResearch.WordTrace tailWord_8332105 prefixEnd_8332105 4278374728730228334568853 := by
  unfold tailWord_8332105
  simp only [CollatzResearch.WordTrace]
  refine ⟨303896835479214070087477769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202597890319476046724985179 303896835479214070087477769)
  ·
    refine ⟨227922626609410552565608327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303896835479214070087477769 227922626609410552565608327)
    ·
      refine ⟨341883939914115828848412491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227922626609410552565608327 341883939914115828848412491)
      ·
        refine ⟨512825909871173743272618737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341883939914115828848412491 512825909871173743272618737)
        ·
          refine ⟨384619432403380307454464053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512825909871173743272618737 384619432403380307454464053)
          ·
            refine ⟨36058071787816903823856005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 384619432403380307454464053 36058071787816903823856005)
            ·
              refine ⟨6760888460215669466973001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36058071787816903823856005 6760888460215669466973001)
              ·
                refine ⟨5070666345161752100229751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6760888460215669466973001 5070666345161752100229751)
                ·
                  refine ⟨7605999517742628150344627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070666345161752100229751 7605999517742628150344627)
                  ·
                    refine ⟨11408999276613942225516941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7605999517742628150344627 11408999276613942225516941)
                    ·
                      refine ⟨4278374728730228334568853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11408999276613942225516941 4278374728730228334568853)
                      ·
                        rfl

theorem cell23_8332105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 2, 1, 1, 3].length) (baseStart_8332105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332105 prefixEnd_8332105 := by exact prefixLift 8332105
  have htrace : WordTrace (prefixWord ++ tailWord_8332105) baseStart_8332105 baseEnd_8332105 := by
    simpa [prefixWord, tailWord_8332105, baseEnd_8332105] using wordTrace_append hprefix tailTrace_8332105
  have hstable : (prefixWord ++ tailWord_8332105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332105).length < 2 ^ (prefixWord ++ tailWord_8332105).sum := by decide
  have hdescent : baseEnd_8332105 < baseStart_8332105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332111 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 9, 2, 2]
def baseStart_8332111 : Nat := 118140960795 + 8332111 * 2 ^ 59
def prefixEnd_8332111 : Nat := 4983230072969 + 3 ^ 40 * 8332111 * 2
def baseEnd_8332111 : Nat := 4278377809614155311093825

theorem tailTrace_8332111 : CollatzResearch.WordTrace tailWord_8332111 prefixEnd_8332111 4278377809614155311093825 := by
  unfold tailWord_8332111
  simp only [CollatzResearch.WordTrace]
  refine ⟨303897054317192333112196187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202598036211461555408130791 303897054317192333112196187)
  ·
    refine ⟨455845581475788499668294281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303897054317192333112196187 455845581475788499668294281)
    ·
      refine ⟨341884186106841374751220711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455845581475788499668294281 341884186106841374751220711)
      ·
        refine ⟨512826279160262062126831067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341884186106841374751220711 512826279160262062126831067)
        ·
          refine ⟨769239418740393093190246601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512826279160262062126831067 769239418740393093190246601)
          ·
            refine ⟨576929564055294819892684951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769239418740393093190246601 576929564055294819892684951)
            ·
              refine ⟨865394346082942229839027427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576929564055294819892684951 865394346082942229839027427)
              ·
                refine ⟨1298091519124413344758541141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865394346082942229839027427 1298091519124413344758541141)
                ·
                  refine ⟨7606004994869609441944577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1298091519124413344758541141 7606004994869609441944577)
                  ·
                    refine ⟨5704503746152207081458433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606004994869609441944577 5704503746152207081458433)
                    ·
                      refine ⟨4278377809614155311093825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704503746152207081458433 4278377809614155311093825)
                      ·
                        rfl

theorem cell23_8332111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 2, 2].length) (baseStart_8332111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332111 prefixEnd_8332111 := by exact prefixLift 8332111
  have htrace : WordTrace (prefixWord ++ tailWord_8332111) baseStart_8332111 baseEnd_8332111 := by
    simpa [prefixWord, tailWord_8332111, baseEnd_8332111] using wordTrace_append hprefix tailTrace_8332111
  have hstable : (prefixWord ++ tailWord_8332111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332111).length < 2 ^ (prefixWord ++ tailWord_8332111).sum := by decide
  have hdescent : baseEnd_8332111 < baseStart_8332111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332114 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_8332114 : Nat := 118140960795 + 8332114 * 2 ^ 59
def prefixEnd_8332114 : Nat := 4983230072969 + 3 ^ 40 * 8332114 * 2
def baseEnd_8332114 : Nat := 4278379350056118799356311

theorem tailTrace_8332114 : CollatzResearch.WordTrace tailWord_8332114 prefixEnd_8332114 4278379350056118799356311 := by
  unfold tailWord_8332114
  simp only [CollatzResearch.WordTrace]
  refine ⟨75974290934045366156138849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202598109157454309749703597 75974290934045366156138849)
  ·
    refine ⟨56980718200534024617104137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75974290934045366156138849 56980718200534024617104137)
    ·
      refine ⟨42735538650400518462828103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56980718200534024617104137 42735538650400518462828103)
      ·
        refine ⟨64103307975600777694242155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42735538650400518462828103 64103307975600777694242155)
        ·
          refine ⟨96154961963401166541363233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64103307975600777694242155 96154961963401166541363233)
          ·
            refine ⟨72116221472550874906022425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96154961963401166541363233 72116221472550874906022425)
            ·
              refine ⟨54087166104413156179516819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72116221472550874906022425 54087166104413156179516819)
              ·
                refine ⟨81130749156619734269275229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54087166104413156179516819 81130749156619734269275229)
                ·
                  refine ⟨30424030933732400350978211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81130749156619734269275229 30424030933732400350978211)
                  ·
                    refine ⟨45636046400598600526467317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30424030933732400350978211 45636046400598600526467317)
                    ·
                      refine ⟨4278379350056118799356311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45636046400598600526467317 4278379350056118799356311)
                      ·
                        rfl

theorem cell23_8332114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_8332114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332114 prefixEnd_8332114 := by exact prefixLift 8332114
  have htrace : WordTrace (prefixWord ++ tailWord_8332114) baseStart_8332114 baseEnd_8332114 := by
    simpa [prefixWord, tailWord_8332114, baseEnd_8332114] using wordTrace_append hprefix tailTrace_8332114
  have hstable : (prefixWord ++ tailWord_8332114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332114).length < 2 ^ (prefixWord ++ tailWord_8332114).sum := by decide
  have hdescent : baseEnd_8332114 < baseStart_8332114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332121 : List Nat := [1, 2, 1, 2, 2, 4, 2, 3, 2, 4]
def baseStart_8332121 : Nat := 118140960795 + 8332121 * 2 ^ 59
def prefixEnd_8332121 : Nat := 4983230072969 + 3 ^ 40 * 8332121 * 2
def baseEnd_8332121 : Nat := 1426127648140233423989593

theorem tailTrace_8332121 : CollatzResearch.WordTrace tailWord_8332121 prefixEnd_8332121 1426127648140233423989593 := by
  unfold tailWord_8332121
  simp only [CollatzResearch.WordTrace]
  refine ⟨303897419047156104820060217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202598279364770736546706811 303897419047156104820060217)
  ·
    refine ⟨227923064285367078615045163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303897419047156104820060217 227923064285367078615045163)
    ·
      refine ⟨341884596428050617922567745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227923064285367078615045163 341884596428050617922567745)
      ·
        refine ⟨256413447321037963441925809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341884596428050617922567745 256413447321037963441925809)
        ·
          refine ⟨192310085490778472581444357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256413447321037963441925809 192310085490778472581444357)
          ·
            refine ⟨36058141029520963609020817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192310085490778472581444357 36058141029520963609020817)
            ·
              refine ⟨27043605772140722706765613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36058141029520963609020817 27043605772140722706765613)
              ·
                refine ⟨10141352164552771015037105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27043605772140722706765613 10141352164552771015037105)
                ·
                  refine ⟨7606014123414578261277829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10141352164552771015037105 7606014123414578261277829)
                  ·
                    refine ⟨1426127648140233423989593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606014123414578261277829 1426127648140233423989593)
                    ·
                      rfl

theorem cell23_8332121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_8332121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332121 prefixEnd_8332121 := by exact prefixLift 8332121
  have htrace : WordTrace (prefixWord ++ tailWord_8332121) baseStart_8332121 baseEnd_8332121 := by
    simpa [prefixWord, tailWord_8332121, baseEnd_8332121] using wordTrace_append hprefix tailTrace_8332121
  have hstable : (prefixWord ++ tailWord_8332121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332121).length < 2 ^ (prefixWord ++ tailWord_8332121).sum := by decide
  have hdescent : baseEnd_8332121 < baseStart_8332121 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332128 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 3, 2, 2]
def baseStart_8332128 : Nat := 118140960795 + 8332128 * 2 ^ 59
def prefixEnd_8332128 : Nat := 4983230072969 + 3 ^ 40 * 8332128 * 2
def baseEnd_8332128 : Nat := 4278386538785281744581247

theorem tailTrace_8332128 : CollatzResearch.WordTrace tailWord_8332128 prefixEnd_8332128 4278386538785281744581247 := by
  unfold tailWord_8332128
  simp only [CollatzResearch.WordTrace]
  refine ⟨151948837179065372507782519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202598449572087163343710025 151948837179065372507782519)
  ·
    refine ⟨227923255768598058761673779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151948837179065372507782519 227923255768598058761673779)
    ·
      refine ⟨341884883652897088142510669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227923255768598058761673779 341884883652897088142510669)
      ·
        refine ⟨128206831369836408053441501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341884883652897088142510669 128206831369836408053441501)
        ·
          refine ⟨48077561763688653020040563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128206831369836408053441501 48077561763688653020040563)
          ·
            refine ⟨72116342645532979530060845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48077561763688653020040563 72116342645532979530060845)
            ·
              refine ⟨27043628492074867323772817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72116342645532979530060845 27043628492074867323772817)
              ·
                refine ⟨20282721369056150492829613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27043628492074867323772817 20282721369056150492829613)
                ·
                  refine ⟨7606020513396056434811105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20282721369056150492829613 7606020513396056434811105)
                  ·
                    refine ⟨5704515385047042326108329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606020513396056434811105 5704515385047042326108329)
                    ·
                      refine ⟨4278386538785281744581247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704515385047042326108329 4278386538785281744581247)
                      ·
                        rfl

theorem cell23_8332128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 3, 2, 2].length) (baseStart_8332128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332128 prefixEnd_8332128 := by exact prefixLift 8332128
  have htrace : WordTrace (prefixWord ++ tailWord_8332128) baseStart_8332128 baseEnd_8332128 := by
    simpa [prefixWord, tailWord_8332128, baseEnd_8332128] using wordTrace_append hprefix tailTrace_8332128
  have hstable : (prefixWord ++ tailWord_8332128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332128).length < 2 ^ (prefixWord ++ tailWord_8332128).sum := by decide
  have hdescent : baseEnd_8332128 < baseStart_8332128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332131 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 3]
def baseStart_8332131 : Nat := 118140960795 + 8332131 * 2 ^ 59
def prefixEnd_8332131 : Nat := 4983230072969 + 3 ^ 40 * 8332131 * 2
def baseEnd_8332131 : Nat := 4278388079227245232843733

theorem tailTrace_8332131 : CollatzResearch.WordTrace tailWord_8332131 prefixEnd_8332131 4278388079227245232843733 := by
  unfold tailWord_8332131
  simp only [CollatzResearch.WordTrace]
  refine ⟨303897783777119876527924247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202598522518079917685282831 303897783777119876527924247)
  ·
    refine ⟨455846675665679814791886371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303897783777119876527924247 455846675665679814791886371)
    ·
      refine ⟨683770013498519722187829557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455846675665679814791886371 683770013498519722187829557)
      ·
        refine ⟨64103438765486223955109021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 683770013498519722187829557 64103438765486223955109021)
        ·
          refine ⟨24038789537057333983165883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64103438765486223955109021 24038789537057333983165883)
          ·
            refine ⟨36058184305586000974748825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24038789537057333983165883 36058184305586000974748825)
            ·
              refine ⟨27043638229189500731061619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36058184305586000974748825 27043638229189500731061619)
              ·
                refine ⟨40565457343784251096592429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27043638229189500731061619 40565457343784251096592429)
                ·
                  refine ⟨15212046503919094161222161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40565457343784251096592429 15212046503919094161222161)
                  ·
                    refine ⟨11409034877939320620916621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15212046503919094161222161 11409034877939320620916621)
                    ·
                      refine ⟨4278388079227245232843733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11409034877939320620916621 4278388079227245232843733)
                      ·
                        rfl

theorem cell23_8332131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_8332131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332131 prefixEnd_8332131 := by exact prefixLift 8332131
  have htrace : WordTrace (prefixWord ++ tailWord_8332131) baseStart_8332131 baseEnd_8332131 := by
    simpa [prefixWord, tailWord_8332131, baseEnd_8332131] using wordTrace_append hprefix tailTrace_8332131
  have hstable : (prefixWord ++ tailWord_8332131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332131).length < 2 ^ (prefixWord ++ tailWord_8332131).sum := by decide
  have hdescent : baseEnd_8332131 < baseStart_8332131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332142 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_8332142 : Nat := 118140960795 + 8332142 * 2 ^ 59
def prefixEnd_8332142 : Nat := 4983230072969 + 3 ^ 40 * 8332142 * 2
def baseEnd_8332142 : Nat := 1426131242504814896602061

theorem tailTrace_8332142 : CollatzResearch.WordTrace tailWord_8332142 prefixEnd_8332142 1426131242504814896602061 := by
  unfold tailWord_8332142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37987273122510003175821835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202598789986720016937716453 37987273122510003175821835)
  ·
    refine ⟨56980909683765004763732753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37987273122510003175821835 56980909683765004763732753)
    ·
      refine ⟨42735682262823753572799565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56980909683765004763732753 42735682262823753572799565)
      ·
        refine ⟨16025880848558907589799837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42735682262823753572799565 16025880848558907589799837)
        ·
          refine ⟨6009705318209590346174939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16025880848558907589799837 6009705318209590346174939)
          ·
            refine ⟨9014557977314385519262409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009705318209590346174939 9014557977314385519262409)
            ·
              refine ⟨6760918482985789139446807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9014557977314385519262409 6760918482985789139446807)
              ·
                refine ⟨10141377724478683709170211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6760918482985789139446807 10141377724478683709170211)
                ·
                  refine ⟨15212066586718025563755317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10141377724478683709170211 15212066586718025563755317)
                  ·
                    refine ⟨1426131242504814896602061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15212066586718025563755317 1426131242504814896602061)
                    ·
                      rfl

theorem cell23_8332142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_8332142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332142 prefixEnd_8332142 := by exact prefixLift 8332142
  have htrace : WordTrace (prefixWord ++ tailWord_8332142) baseStart_8332142 baseEnd_8332142 := by
    simpa [prefixWord, tailWord_8332142, baseEnd_8332142] using wordTrace_append hprefix tailTrace_8332142
  have hstable : (prefixWord ++ tailWord_8332142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332142).length < 2 ^ (prefixWord ++ tailWord_8332142).sum := by decide
  have hdescent : baseEnd_8332142 < baseStart_8332142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332145 : List Nat := [1, 2, 2, 2, 1, 4, 1, 5, 1, 2, 2]
def baseStart_8332145 : Nat := 118140960795 + 8332145 * 2 ^ 59
def prefixEnd_8332145 : Nat := 4983230072969 + 3 ^ 40 * 8332145 * 2
def baseEnd_8332145 : Nat := 4278395267956408178068669

theorem tailTrace_8332145 : CollatzResearch.WordTrace tailWord_8332145 prefixEnd_8332145 4278395267956408178068669 := by
  unfold tailWord_8332145
  simp only [CollatzResearch.WordTrace]
  refine ⟨303898294399069156918933889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202598862932712771279289259 303898294399069156918933889)
  ·
    refine ⟨227923720799301867689200417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303898294399069156918933889 227923720799301867689200417)
    ·
      refine ⟨170942790599476400766900313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227923720799301867689200417 170942790599476400766900313)
      ·
        refine ⟨128207092949607300575175235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170942790599476400766900313 128207092949607300575175235)
        ·
          refine ⟨192310639424410950862762853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128207092949607300575175235 192310639424410950862762853)
          ·
            refine ⟨36058244892077053286768035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192310639424410950862762853 36058244892077053286768035)
            ·
              refine ⟨54087367338115579930152053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36058244892077053286768035 54087367338115579930152053)
              ·
                refine ⟨5070690687948335618451755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54087367338115579930152053 5070690687948335618451755)
                ·
                  refine ⟨7606036031922503427677633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070690687948335618451755 7606036031922503427677633)
                  ·
                    refine ⟨5704527023941877570758225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606036031922503427677633 5704527023941877570758225)
                    ·
                      refine ⟨4278395267956408178068669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704527023941877570758225 4278395267956408178068669)
                      ·
                        rfl

theorem cell23_8332145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_8332145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332145 prefixEnd_8332145 := by exact prefixLift 8332145
  have htrace : WordTrace (prefixWord ++ tailWord_8332145) baseStart_8332145 baseEnd_8332145 := by
    simpa [prefixWord, tailWord_8332145, baseEnd_8332145] using wordTrace_append hprefix tailTrace_8332145
  have hstable : (prefixWord ++ tailWord_8332145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332145).length < 2 ^ (prefixWord ++ tailWord_8332145).sum := by decide
  have hdescent : baseEnd_8332145 < baseStart_8332145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332171 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 5, 3, 2]
def baseStart_8332171 : Nat := 118140960795 + 8332171 * 2 ^ 59
def prefixEnd_8332171 : Nat := 4983230072969 + 3 ^ 40 * 8332171 * 2
def baseEnd_8332171 : Nat := 4278408618453425076343549

theorem tailTrace_8332171 : CollatzResearch.WordTrace tailWord_8332171 prefixEnd_8332171 4278408618453425076343549 := by
  unfold tailWord_8332171
  simp only [CollatzResearch.WordTrace]
  refine ⟨303899242696974963359380367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202599495131316642239586911 303899242696974963359380367)
  ·
    refine ⟨455848864045462445039070551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303899242696974963359380367 455848864045462445039070551)
    ·
      refine ⟨683773296068193667558605827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455848864045462445039070551 683773296068193667558605827)
      ·
        refine ⟨1025659944102290501337908741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683773296068193667558605827 1025659944102290501337908741)
        ·
          refine ⟨192311239519179469000857889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1025659944102290501337908741 192311239519179469000857889)
          ·
            refine ⟨144233429639384601750643417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192311239519179469000857889 144233429639384601750643417)
            ·
              refine ⟨108175072229538451312982563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144233429639384601750643417 108175072229538451312982563)
              ·
                refine ⟨162262608344307676969473845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108175072229538451312982563 162262608344307676969473845)
                ·
                  refine ⟨15212119532278844715888173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162262608344307676969473845 15212119532278844715888173)
                  ·
                    refine ⟨5704544824604566768458065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15212119532278844715888173 5704544824604566768458065)
                    ·
                      refine ⟨4278408618453425076343549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704544824604566768458065 4278408618453425076343549)
                      ·
                        rfl

theorem cell23_8332171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 3, 2].length) (baseStart_8332171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332171 prefixEnd_8332171 := by exact prefixLift 8332171
  have htrace : WordTrace (prefixWord ++ tailWord_8332171) baseStart_8332171 baseEnd_8332171 := by
    simpa [prefixWord, tailWord_8332171, baseEnd_8332171] using wordTrace_append hprefix tailTrace_8332171
  have hstable : (prefixWord ++ tailWord_8332171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332171).length < 2 ^ (prefixWord ++ tailWord_8332171).sum := by decide
  have hdescent : baseEnd_8332171 < baseStart_8332171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332182 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_8332182 : Nat := 118140960795 + 8332182 * 2 ^ 59
def prefixEnd_8332182 : Nat := 4983230072969 + 3 ^ 40 * 8332182 * 2
def baseEnd_8332182 : Nat := 4278414266740624533305999

theorem tailTrace_8332182 : CollatzResearch.WordTrace tailWord_8332182 prefixEnd_8332182 4278414266740624533305999 := by
  unfold tailWord_8332182
  simp only [CollatzResearch.WordTrace]
  refine ⟨18993727743745944514876925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202599762599956741492020533 18993727743745944514876925)
  ·
    refine ⟨7122647903904729193078847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18993727743745944514876925 7122647903904729193078847)
    ·
      refine ⟨10683971855857093789618271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7122647903904729193078847 10683971855857093789618271)
      ·
        refine ⟨16025957783785640684427407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10683971855857093789618271 16025957783785640684427407)
        ·
          refine ⟨24038936675678461026641111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16025957783785640684427407 24038936675678461026641111)
          ·
            refine ⟨36058405013517691539961667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24038936675678461026641111 36058405013517691539961667)
            ·
              refine ⟨54087607520276537309942501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36058405013517691539961667 54087607520276537309942501)
              ·
                refine ⟨10141426410051850745614219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54087607520276537309942501 10141426410051850745614219)
                ·
                  refine ⟨15212139615077776118421329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10141426410051850745614219 15212139615077776118421329)
                  ·
                    refine ⟨11409104711308332088815997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15212139615077776118421329 11409104711308332088815997)
                    ·
                      refine ⟨4278414266740624533305999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11409104711308332088815997 4278414266740624533305999)
                      ·
                        rfl

theorem cell23_8332182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_8332182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332182 prefixEnd_8332182 := by exact prefixLift 8332182
  have htrace : WordTrace (prefixWord ++ tailWord_8332182) baseStart_8332182 baseEnd_8332182 := by
    simpa [prefixWord, tailWord_8332182, baseEnd_8332182] using wordTrace_append hprefix tailTrace_8332182
  have hstable : (prefixWord ++ tailWord_8332182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332182).length < 2 ^ (prefixWord ++ tailWord_8332182).sum := by decide
  have hdescent : baseEnd_8332182 < baseStart_8332182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332201 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 3, 4, 2]
def baseStart_8332201 : Nat := 118140960795 + 8332201 * 2 ^ 59
def prefixEnd_8332201 : Nat := 4983230072969 + 3 ^ 40 * 8332201 * 2
def baseEnd_8332201 : Nat := 4278424022873059958968411

theorem tailTrace_8332201 : CollatzResearch.WordTrace tailWord_8332201 prefixEnd_8332201 4278424022873059958968411 := by
  unfold tailWord_8332201
  simp only [CollatzResearch.WordTrace]
  refine ⟨303900336886866278482972457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202600224591244185655314971 303900336886866278482972457)
  ·
    refine ⟨227925252665149708862229343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303900336886866278482972457 227925252665149708862229343)
    ·
      refine ⟨341887878997724563293344015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227925252665149708862229343 341887878997724563293344015)
      ·
        refine ⟨512831818496586844940016023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341887878997724563293344015 512831818496586844940016023)
        ·
          refine ⟨769247727744880267410024035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512831818496586844940016023 769247727744880267410024035)
          ·
            refine ⟨1153871591617320401115036053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769247727744880267410024035 1153871591617320401115036053)
            ·
              refine ⟨54087730857061893802267315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1153871591617320401115036053 54087730857061893802267315)
              ·
                refine ⟨81131596285592840703400973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54087730857061893802267315 81131596285592840703400973)
                ·
                  refine ⟨30424348607097315263775365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81131596285592840703400973 30424348607097315263775365)
                  ·
                    refine ⟨5704565363830746611957881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30424348607097315263775365 5704565363830746611957881)
                    ·
                      refine ⟨4278424022873059958968411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704565363830746611957881 4278424022873059958968411)
                      ·
                        rfl

theorem cell23_8332201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 4, 2].length) (baseStart_8332201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332201 prefixEnd_8332201 := by exact prefixLift 8332201
  have htrace : WordTrace (prefixWord ++ tailWord_8332201) baseStart_8332201 baseEnd_8332201 := by
    simpa [prefixWord, tailWord_8332201, baseEnd_8332201] using wordTrace_append hprefix tailTrace_8332201
  have hstable : (prefixWord ++ tailWord_8332201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332201).length < 2 ^ (prefixWord ++ tailWord_8332201).sum := by decide
  have hdescent : baseEnd_8332201 < baseStart_8332201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332204 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_8332204 : Nat := 118140960795 + 8332204 * 2 ^ 59
def prefixEnd_8332204 : Nat := 4983230072969 + 3 ^ 40 * 8332204 * 2
def baseEnd_8332204 : Nat := 4278425563315023447230897

theorem tailTrace_8332204 : CollatzResearch.WordTrace tailWord_8332204 prefixEnd_8332204 4278425563315023447230897 := by
  unfold tailWord_8332204
  simp only [CollatzResearch.WordTrace]
  refine ⟨151950223152927704997665833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202600297537236939996887777 151950223152927704997665833)
  ·
    refine ⟨113962667364695778748249375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151950223152927704997665833 113962667364695778748249375)
    ·
      refine ⟨170944001047043668122374063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113962667364695778748249375 170944001047043668122374063)
      ·
        refine ⟨256416001570565502183561095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170944001047043668122374063 256416001570565502183561095)
        ·
          refine ⟨384624002355848253275341643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256416001570565502183561095 384624002355848253275341643)
          ·
            refine ⟨576936003533772379913012465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384624002355848253275341643 576936003533772379913012465)
            ·
              refine ⟨432702002650329284934759349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 576936003533772379913012465 432702002650329284934759349)
              ·
                refine ⟨40565812748468370462633689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432702002650329284934759349 40565812748468370462633689)
                ·
                  refine ⟨30424359561351277846975267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40565812748468370462633689 30424359561351277846975267)
                  ·
                    refine ⟨45636539342026916770462901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30424359561351277846975267 45636539342026916770462901)
                    ·
                      refine ⟨4278425563315023447230897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45636539342026916770462901 4278425563315023447230897)
                      ·
                        rfl

theorem cell23_8332204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_8332204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332204 prefixEnd_8332204 := by exact prefixLift 8332204
  have htrace : WordTrace (prefixWord ++ tailWord_8332204) baseStart_8332204 baseEnd_8332204 := by
    simpa [prefixWord, tailWord_8332204, baseEnd_8332204] using wordTrace_append hprefix tailTrace_8332204
  have hstable : (prefixWord ++ tailWord_8332204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332204).length < 2 ^ (prefixWord ++ tailWord_8332204).sum := by decide
  have hdescent : baseEnd_8332204 < baseStart_8332204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332218 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2]
def baseStart_8332218 : Nat := 118140960795 + 8332218 * 2 ^ 59
def prefixEnd_8332218 : Nat := 4983230072969 + 3 ^ 40 * 8332218 * 2
def baseEnd_8332218 : Nat := 4278432752044186392455833

theorem tailTrace_8332218 : CollatzResearch.WordTrace tailWord_8332218 prefixEnd_8332218 4278432752044186392455833 := by
  unfold tailWord_8332218
  simp only [CollatzResearch.WordTrace]
  refine ⟨75975239231951172596585327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202600637951869793590894205 75975239231951172596585327)
  ·
    refine ⟨113962858847926758894877991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75975239231951172596585327 113962858847926758894877991)
    ·
      refine ⟨170944288271890138342316987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113962858847926758894877991 170944288271890138342316987)
      ·
        refine ⟨256416432407835207513475481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170944288271890138342316987 256416432407835207513475481)
        ·
          refine ⟨192312324305876405635106611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256416432407835207513475481 192312324305876405635106611)
          ·
            refine ⟨288468486458814608452659917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192312324305876405635106611 288468486458814608452659917)
            ·
              refine ⟨108175682422055478169747469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 288468486458814608452659917 108175682422055478169747469)
              ·
                refine ⟨40565880908270804313655301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108175682422055478169747469 40565880908270804313655301)
                ·
                  refine ⟨7606102670300775808810369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40565880908270804313655301 7606102670300775808810369)
                  ·
                    refine ⟨5704577002725581856607777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606102670300775808810369 5704577002725581856607777)
                    ·
                      refine ⟨4278432752044186392455833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704577002725581856607777 4278432752044186392455833)
                      ·
                        rfl

theorem cell23_8332218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2].length) (baseStart_8332218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332218 prefixEnd_8332218 := by exact prefixLift 8332218
  have htrace : WordTrace (prefixWord ++ tailWord_8332218) baseStart_8332218 baseEnd_8332218 := by
    simpa [prefixWord, tailWord_8332218, baseEnd_8332218] using wordTrace_append hprefix tailTrace_8332218
  have hstable : (prefixWord ++ tailWord_8332218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332218).length < 2 ^ (prefixWord ++ tailWord_8332218).sum := by decide
  have hdescent : baseEnd_8332218 < baseStart_8332218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332235 : List Nat := [1, 1, 1, 1, 3, 6, 1, 3, 2, 2, 2]
def baseStart_8332235 : Nat := 118140960795 + 8332235 * 2 ^ 59
def prefixEnd_8332235 : Nat := 4983230072969 + 3 ^ 40 * 8332235 * 2
def baseEnd_8332235 : Nat := 4278441481215312825943255

theorem tailTrace_8332235 : CollatzResearch.WordTrace tailWord_8332235 prefixEnd_8332235 4278441481215312825943255 := by
  unfold tailWord_8332235
  simp only [CollatzResearch.WordTrace]
  refine ⟨303901576968743102289710159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202601051312495401526473439 303901576968743102289710159)
  ·
    refine ⟨455852365453114653434565239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303901576968743102289710159 455852365453114653434565239)
    ·
      refine ⟨683778548179671980151847859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455852365453114653434565239 683778548179671980151847859)
      ·
        refine ⟨1025667822269507970227771789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683778548179671980151847859 1025667822269507970227771789)
        ·
          refine ⟨384625433351065488835414421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1025667822269507970227771789 384625433351065488835414421)
          ·
            refine ⟨18029317188331194789160051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 384625433351065488835414421 18029317188331194789160051)
            ·
              refine ⟨27043975782496792183740077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18029317188331194789160051 27043975782496792183740077)
              ·
                refine ⟨10141490918436297068902529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27043975782496792183740077 10141490918436297068902529)
                ·
                  refine ⟨7606118188827222801676897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10141490918436297068902529 7606118188827222801676897)
                  ·
                    refine ⟨5704588641620417101257673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606118188827222801676897 5704588641620417101257673)
                    ·
                      refine ⟨4278441481215312825943255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704588641620417101257673 4278441481215312825943255)
                      ·
                        rfl

theorem cell23_8332235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 2, 2].length) (baseStart_8332235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332235 prefixEnd_8332235 := by exact prefixLift 8332235
  have htrace : WordTrace (prefixWord ++ tailWord_8332235) baseStart_8332235 baseEnd_8332235 := by
    simpa [prefixWord, tailWord_8332235, baseEnd_8332235] using wordTrace_append hprefix tailTrace_8332235
  have hstable : (prefixWord ++ tailWord_8332235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332235).length < 2 ^ (prefixWord ++ tailWord_8332235).sum := by decide
  have hdescent : baseEnd_8332235 < baseStart_8332235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332271 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 2, 5]
def baseStart_8332271 : Nat := 118140960795 + 8332271 * 2 ^ 59
def prefixEnd_8332271 : Nat := 4983230072969 + 3 ^ 40 * 8332271 * 2
def baseEnd_8332271 : Nat := 1426153322172958228364363

theorem tailTrace_8332271 : CollatzResearch.WordTrace tailWord_8332271 prefixEnd_8332271 1426153322172958228364363 := by
  unfold tailWord_8332271
  simp only [CollatzResearch.WordTrace]
  refine ⟨303902889996612680438020667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202601926664408453625347111 303902889996612680438020667)
  ·
    refine ⟨455854334994919020657031001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303902889996612680438020667 455854334994919020657031001)
    ·
      refine ⟨341890751246189265492773251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455854334994919020657031001 341890751246189265492773251)
      ·
        refine ⟨512836126869283898239159877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341890751246189265492773251 512836126869283898239159877)
        ·
          refine ⟨96156773787990730919842477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 512836126869283898239159877 96156773787990730919842477)
          ·
            refine ⟨36058790170496524094940929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96156773787990730919842477 36058790170496524094940929)
            ·
              refine ⟨27044092627872393071205697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36058790170496524094940929 27044092627872393071205697)
              ·
                refine ⟨20283069470904294803404273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27044092627872393071205697 20283069470904294803404273)
                ·
                  refine ⟨15212302103178221102553205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20283069470904294803404273 15212302103178221102553205)
                  ·
                    refine ⟨1426153322172958228364363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15212302103178221102553205 1426153322172958228364363)
                    ·
                      rfl

theorem cell23_8332271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_8332271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332271 prefixEnd_8332271 := by exact prefixLift 8332271
  have htrace : WordTrace (prefixWord ++ tailWord_8332271) baseStart_8332271 baseEnd_8332271 := by
    simpa [prefixWord, tailWord_8332271, baseEnd_8332271] using wordTrace_append hprefix tailTrace_8332271
  have hstable : (prefixWord ++ tailWord_8332271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332271).length < 2 ^ (prefixWord ++ tailWord_8332271).sum := by decide
  have hdescent : baseEnd_8332271 < baseStart_8332271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332304 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_8332304 : Nat := 118140960795 + 8332304 * 2 ^ 59
def prefixEnd_8332304 : Nat := 4983230072969 + 3 ^ 40 * 8332304 * 2
def baseEnd_8332304 : Nat := 4278476911380473055980437

theorem tailTrace_8332304 : CollatzResearch.WordTrace tailWord_8332304 prefixEnd_8332304 4278476911380473055980437 := by
  unfold tailWord_8332304
  simp only [CollatzResearch.WordTrace]
  refine ⟨151952046802746563536985983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202602729070328751382647977 151952046802746563536985983)
  ·
    refine ⟨227928070204119845305478975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151952046802746563536985983 227928070204119845305478975)
    ·
      refine ⟨341892105306179767958218463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227928070204119845305478975 341892105306179767958218463)
      ·
        refine ⟨512838157959269651937327695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341892105306179767958218463 512838157959269651937327695)
        ·
          refine ⟨769257236938904477905991543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512838157959269651937327695 769257236938904477905991543)
          ·
            refine ⟨1153885855408356716858987315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769257236938904477905991543 1153885855408356716858987315)
            ·
              refine ⟨1730828783112535075288480973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1153885855408356716858987315 1730828783112535075288480973)
              ·
                refine ⟨649060793667200653233180365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1730828783112535075288480973 649060793667200653233180365)
                ·
                  refine ⟨243397797625200244962442637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649060793667200653233180365 243397797625200244962442637)
                  ·
                    refine ⟨91274174109450091860915989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 243397797625200244962442637 91274174109450091860915989)
                    ·
                      refine ⟨4278476911380473055980437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91274174109450091860915989 4278476911380473055980437)
                      ·
                        rfl

theorem cell23_8332304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_8332304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332304 prefixEnd_8332304 := by exact prefixLift 8332304
  have htrace : WordTrace (prefixWord ++ tailWord_8332304) baseStart_8332304 baseEnd_8332304 := by
    simpa [prefixWord, tailWord_8332304, baseEnd_8332304] using wordTrace_append hprefix tailTrace_8332304
  have hstable : (prefixWord ++ tailWord_8332304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332304).length < 2 ^ (prefixWord ++ tailWord_8332304).sum := by decide
  have hdescent : baseEnd_8332304 < baseStart_8332304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332321 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_8332321 : Nat := 118140960795 + 8332321 * 2 ^ 59
def prefixEnd_8332321 : Nat := 4983230072969 + 3 ^ 40 * 8332321 * 2
def baseEnd_8332321 : Nat := 4278485640551599489467859

theorem tailTrace_8332321 : CollatzResearch.WordTrace tailWord_8332321 prefixEnd_8332321 4278485640551599489467859 := by
  unfold tailWord_8332321
  simp only [CollatzResearch.WordTrace]
  refine ⟨303904713646431538977340817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202603142430954359318227211 303904713646431538977340817)
  ·
    refine ⟨227928535234823654233005613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303904713646431538977340817 227928535234823654233005613)
    ·
      refine ⟨85473200713058870337377105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227928535234823654233005613 85473200713058870337377105)
      ·
        refine ⟨64104900534794152753032829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85473200713058870337377105 64104900534794152753032829)
        ·
          refine ⟨24039337700547807282387311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64104900534794152753032829 24039337700547807282387311)
          ·
            refine ⟨36059006550821710923580967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24039337700547807282387311 36059006550821710923580967)
            ·
              refine ⟨54088509826232566385371451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36059006550821710923580967 54088509826232566385371451)
              ·
                refine ⟨81132764739348849578057177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54088509826232566385371451 81132764739348849578057177)
                ·
                  refine ⟨60849573554511637183542883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81132764739348849578057177 60849573554511637183542883)
                  ·
                    refine ⟨91274360331767455775314325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60849573554511637183542883 91274360331767455775314325)
                    ·
                      refine ⟨4278485640551599489467859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91274360331767455775314325 4278485640551599489467859)
                      ·
                        rfl

theorem cell23_8332321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_8332321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332321 prefixEnd_8332321 := by exact prefixLift 8332321
  have htrace : WordTrace (prefixWord ++ tailWord_8332321) baseStart_8332321 baseEnd_8332321 := by
    simpa [prefixWord, tailWord_8332321, baseEnd_8332321] using wordTrace_append hprefix tailTrace_8332321
  have hstable : (prefixWord ++ tailWord_8332321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332321).length < 2 ^ (prefixWord ++ tailWord_8332321).sum := by decide
  have hdescent : baseEnd_8332321 < baseStart_8332321 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332368 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 6, 3, 2]
def baseStart_8332368 : Nat := 118140960795 + 8332368 * 2 ^ 59
def prefixEnd_8332368 : Nat := 4983230072969 + 3 ^ 40 * 8332368 * 2
def baseEnd_8332368 : Nat := 4278509774142360805580143

theorem tailTrace_8332368 : CollatzResearch.WordTrace tailWord_8332368 prefixEnd_8332368 4278509774142360805580143 := by
  unfold tailWord_8332368
  simp only [CollatzResearch.WordTrace]
  refine ⟨151953213938630633002150879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202604285251507510669534505 151953213938630633002150879)
  ·
    refine ⟨227929820907945949503226319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151953213938630633002150879 227929820907945949503226319)
    ·
      refine ⟨341894731361918924254839479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227929820907945949503226319 341894731361918924254839479)
      ·
        refine ⟨512842097042878386382259219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341894731361918924254839479 512842097042878386382259219)
        ·
          refine ⟨769263145564317579573388829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512842097042878386382259219 769263145564317579573388829)
          ·
            refine ⟨288473679586619092340020811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 769263145564317579573388829 288473679586619092340020811)
            ·
              refine ⟨432710519379928638510031217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288473679586619092340020811 432710519379928638510031217)
              ·
                refine ⟨324532889534946478882523413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432710519379928638510031217 324532889534946478882523413)
                ·
                  refine ⟨15212479196950616197618285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 324532889534946478882523413 15212479196950616197618285)
                  ·
                    refine ⟨5704679698856481074106857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15212479196950616197618285 5704679698856481074106857)
                    ·
                      refine ⟨4278509774142360805580143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704679698856481074106857 4278509774142360805580143)
                      ·
                        rfl

theorem cell23_8332368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 6, 3, 2].length) (baseStart_8332368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332368 prefixEnd_8332368 := by exact prefixLift 8332368
  have htrace : WordTrace (prefixWord ++ tailWord_8332368) baseStart_8332368 baseEnd_8332368 := by
    simpa [prefixWord, tailWord_8332368, baseEnd_8332368] using wordTrace_append hprefix tailTrace_8332368
  have hstable : (prefixWord ++ tailWord_8332368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332368).length < 2 ^ (prefixWord ++ tailWord_8332368).sum := by decide
  have hdescent : baseEnd_8332368 < baseStart_8332368 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332401 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_8332401 : Nat := 118140960795 + 8332401 * 2 ^ 59
def prefixEnd_8332401 : Nat := 4983230072969 + 3 ^ 40 * 8332401 * 2
def baseEnd_8332401 : Nat := 4278526719003959176467491

theorem tailTrace_8332401 : CollatzResearch.WordTrace tailWord_8332401 prefixEnd_8332401 4278526719003959176467491 := by
  unfold tailWord_8332401
  simp only [CollatzResearch.WordTrace]
  refine ⟨303907631486141712640253057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202605087657427808426835371 303907631486141712640253057)
  ·
    refine ⟨227930723614606284480189793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303907631486141712640253057 227930723614606284480189793)
    ·
      refine ⟨170948042710954713360142345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227930723614606284480189793 170948042710954713360142345)
      ·
        refine ⟨128211032033216035020106759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170948042710954713360142345 128211032033216035020106759)
        ·
          refine ⟨192316548049824052530160139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128211032033216035020106759 192316548049824052530160139)
          ·
            refine ⟨288474822074736078795240209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192316548049824052530160139 288474822074736078795240209)
            ·
              refine ⟨216356116556052059096430157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288474822074736078795240209 216356116556052059096430157)
              ·
                refine ⟨81133543708519522161161309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216356116556052059096430157 81133543708519522161161309)
                ·
                  refine ⟨30425078890694820810435491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81133543708519522161161309 30425078890694820810435491)
                  ·
                    refine ⟨45637618336042231215653237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30425078890694820810435491 45637618336042231215653237)
                    ·
                      refine ⟨4278526719003959176467491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45637618336042231215653237 4278526719003959176467491)
                      ·
                        rfl

theorem cell23_8332401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_8332401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332401 prefixEnd_8332401 := by exact prefixLift 8332401
  have htrace : WordTrace (prefixWord ++ tailWord_8332401) baseStart_8332401 baseEnd_8332401 := by
    simpa [prefixWord, tailWord_8332401, baseEnd_8332401] using wordTrace_append hprefix tailTrace_8332401
  have hstable : (prefixWord ++ tailWord_8332401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332401).length < 2 ^ (prefixWord ++ tailWord_8332401).sum := by decide
  have hdescent : baseEnd_8332401 < baseStart_8332401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332411 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4]
def baseStart_8332411 : Nat := 118140960795 + 8332411 * 2 ^ 59
def prefixEnd_8332411 : Nat := 4983230072969 + 3 ^ 40 * 8332411 * 2
def baseEnd_8332411 : Nat := 4278531853810504137342445

theorem tailTrace_8332411 : CollatzResearch.WordTrace tailWord_8332411 prefixEnd_8332411 4278531853810504137342445 := by
  unfold tailWord_8332411
  simp only [CollatzResearch.WordTrace]
  refine ⟨303907996216105484348117087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202605330810736989565411391 303907996216105484348117087)
  ·
    refine ⟨455861994324158226522175631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303907996216105484348117087 455861994324158226522175631)
    ·
      refine ⟨683792991486237339783263447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455861994324158226522175631 683792991486237339783263447)
      ·
        refine ⟨1025689487229356009674895171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683792991486237339783263447 1025689487229356009674895171)
        ·
          refine ⟨1538534230844034014512342757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025689487229356009674895171 1538534230844034014512342757)
          ·
            refine ⟨288475168283256377721064267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1538534230844034014512342757 288475168283256377721064267)
            ·
              refine ⟨432712752424884566581596401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288475168283256377721064267 432712752424884566581596401)
              ·
                refine ⟨324534564318663424936197301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432712752424884566581596401 324534564318663424936197301)
                ·
                  refine ⟨30425115404874696087768497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324534564318663424936197301 30425115404874696087768497)
                  ·
                    refine ⟨22818836553656022065826373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30425115404874696087768497 22818836553656022065826373)
                    ·
                      refine ⟨4278531853810504137342445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22818836553656022065826373 4278531853810504137342445)
                      ·
                        rfl

theorem cell23_8332411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_8332411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332411 prefixEnd_8332411 := by exact prefixLift 8332411
  have htrace : WordTrace (prefixWord ++ tailWord_8332411) baseStart_8332411 baseEnd_8332411 := by
    simpa [prefixWord, tailWord_8332411, baseEnd_8332411] using wordTrace_append hprefix tailTrace_8332411
  have hstable : (prefixWord ++ tailWord_8332411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332411).length < 2 ^ (prefixWord ++ tailWord_8332411).sum := by decide
  have hdescent : baseEnd_8332411 < baseStart_8332411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332442 : List Nat := [3, 1, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_8332442 : Nat := 118140960795 + 8332442 * 2 ^ 59
def prefixEnd_8332442 : Nat := 4983230072969 + 3 ^ 40 * 8332442 * 2
def baseEnd_8332442 : Nat := 1426182590570264505351601

theorem tailTrace_8332442 : CollatzResearch.WordTrace tailWord_8332442 prefixEnd_8332442 1426182590570264505351601 := by
  unfold tailWord_8332442
  simp only [CollatzResearch.WordTrace]
  refine ⟨75977281719748294160623895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202606084585995451094997053 75977281719748294160623895)
  ·
    refine ⟨113965922579622441240935843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75977281719748294160623895 113965922579622441240935843)
    ·
      refine ⟨170948883869433661861403765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113965922579622441240935843 170948883869433661861403765)
      ·
        refine ⟨16026457862759405799506603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170948883869433661861403765 16026457862759405799506603)
        ·
          refine ⟨24039686794139108699259905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16026457862759405799506603 24039686794139108699259905)
          ·
            refine ⟨18029765095604331524444929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24039686794139108699259905 18029765095604331524444929)
            ·
              refine ⟨13522323821703248643333697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18029765095604331524444929 13522323821703248643333697)
              ·
                refine ⟨10141742866277436482500273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13522323821703248643333697 10141742866277436482500273)
                ·
                  refine ⟨7606307149708077361875205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10141742866277436482500273 7606307149708077361875205)
                  ·
                    refine ⟨1426182590570264505351601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606307149708077361875205 1426182590570264505351601)
                    ·
                      rfl

theorem cell23_8332442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_8332442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332442 prefixEnd_8332442 := by exact prefixLift 8332442
  have htrace : WordTrace (prefixWord ++ tailWord_8332442) baseStart_8332442 baseEnd_8332442 := by
    simpa [prefixWord, tailWord_8332442, baseEnd_8332442] using wordTrace_append hprefix tailTrace_8332442
  have hstable : (prefixWord ++ tailWord_8332442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332442).length < 2 ^ (prefixWord ++ tailWord_8332442).sum := by decide
  have hdescent : baseEnd_8332442 < baseStart_8332442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332448 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3]
def baseStart_8332448 : Nat := 118140960795 + 8332448 * 2 ^ 59
def prefixEnd_8332448 : Nat := 4983230072969 + 3 ^ 40 * 8332448 * 2
def baseEnd_8332448 : Nat := 4278550852594720492579775

theorem tailTrace_8332448 : CollatzResearch.WordTrace tailWord_8332448 prefixEnd_8332448 4278550852594720492579775 := by
  unfold tailWord_8332448
  simp only [CollatzResearch.WordTrace]
  refine ⟨151954672858485719833606999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202606230477980959778142665 151954672858485719833606999)
  ·
    refine ⟨227932009287728579750410499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151954672858485719833606999 227932009287728579750410499)
    ·
      refine ⟨341898013931592869625615749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227932009287728579750410499 341898013931592869625615749)
      ·
        refine ⟨64105877612173663054802953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341898013931592869625615749 64105877612173663054802953)
        ·
          refine ⟨48079408209130247291102215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64105877612173663054802953 48079408209130247291102215)
          ·
            refine ⟨72119112313695370936653323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48079408209130247291102215 72119112313695370936653323)
            ·
              refine ⟨108178668470543056404979985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72119112313695370936653323 108178668470543056404979985)
              ·
                refine ⟨81134001352907292303734989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108178668470543056404979985 81134001352907292303734989)
                ·
                  refine ⟨30425250507340234613900621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81134001352907292303734989 30425250507340234613900621)
                  ·
                    refine ⟨11409468940252587980212733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30425250507340234613900621 11409468940252587980212733)
                    ·
                      refine ⟨4278550852594720492579775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11409468940252587980212733 4278550852594720492579775)
                      ·
                        rfl

theorem cell23_8332448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_8332448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332448 prefixEnd_8332448 := by exact prefixLift 8332448
  have htrace : WordTrace (prefixWord ++ tailWord_8332448) baseStart_8332448 baseEnd_8332448 := by
    simpa [prefixWord, tailWord_8332448, baseEnd_8332448] using wordTrace_append hprefix tailTrace_8332448
  have hstable : (prefixWord ++ tailWord_8332448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332448).length < 2 ^ (prefixWord ++ tailWord_8332448).sum := by decide
  have hdescent : baseEnd_8332448 < baseStart_8332448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332449 : List Nat := [1, 2, 3, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_8332449 : Nat := 118140960795 + 8332449 * 2 ^ 59
def prefixEnd_8332449 : Nat := 4983230072969 + 3 ^ 40 * 8332449 * 2
def baseEnd_8332449 : Nat := 4278551366075374988667271

theorem tailTrace_8332449 : CollatzResearch.WordTrace tailWord_8332449 prefixEnd_8332449 4278551366075374988667271 := by
  unfold tailWord_8332449
  simp only [CollatzResearch.WordTrace]
  refine ⟨303909382189967816838000401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202606254793311877892000267 303909382189967816838000401)
  ·
    refine ⟨227932036642475862628500301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303909382189967816838000401 227932036642475862628500301)
    ·
      refine ⟨85474513740928448485687613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227932036642475862628500301 85474513740928448485687613)
      ·
        refine ⟨32052942652848168182132855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85474513740928448485687613 32052942652848168182132855)
        ·
          refine ⟨48079413979272252273199283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32052942652848168182132855 48079413979272252273199283)
          ·
            refine ⟨72119120968908378409798925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48079413979272252273199283 72119120968908378409798925)
            ·
              refine ⟨27044670363340641903674597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72119120968908378409798925 27044670363340641903674597)
              ·
                refine ⟨5070875693126370356938987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27044670363340641903674597 5070875693126370356938987)
                ·
                  refine ⟨7606313539689555535408481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5070875693126370356938987 7606313539689555535408481)
                  ·
                    refine ⟨5704735154767166651556361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606313539689555535408481 5704735154767166651556361)
                    ·
                      refine ⟨4278551366075374988667271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704735154767166651556361 4278551366075374988667271)
                      ·
                        rfl

theorem cell23_8332449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_8332449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332449 prefixEnd_8332449 := by exact prefixLift 8332449
  have htrace : WordTrace (prefixWord ++ tailWord_8332449) baseStart_8332449 baseEnd_8332449 := by
    simpa [prefixWord, tailWord_8332449, baseEnd_8332449] using wordTrace_append hprefix tailTrace_8332449
  have hstable : (prefixWord ++ tailWord_8332449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332449).length < 2 ^ (prefixWord ++ tailWord_8332449).sum := by decide
  have hdescent : baseEnd_8332449 < baseStart_8332449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332455 : List Nat := [1, 1, 6, 2, 1, 3, 1, 8]
def baseStart_8332455 : Nat := 118140960795 + 8332455 * 2 ^ 59
def prefixEnd_8332455 : Nat := 4983230072969 + 3 ^ 40 * 8332455 * 2
def baseEnd_8332455 : Nat := 158464979517011183896009

theorem tailTrace_8332455 : CollatzResearch.WordTrace tailWord_8332455 prefixEnd_8332455 158464979517011183896009 := by
  unfold tailWord_8332455
  simp only [CollatzResearch.WordTrace]
  refine ⟨303909601027946079862718819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202606400685297386575145879 303909601027946079862718819)
  ·
    refine ⟨455864401541919119794078229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303909601027946079862718819 455864401541919119794078229)
    ·
      refine ⟨21368643822277458740347417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 455864401541919119794078229 21368643822277458740347417)
      ·
        refine ⟨16026482866708094055260563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21368643822277458740347417 16026482866708094055260563)
        ·
          refine ⟨24039724300062141082890845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16026482866708094055260563 24039724300062141082890845)
          ·
            refine ⟨9014896612523302906084067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24039724300062141082890845 9014896612523302906084067)
            ·
              refine ⟨13522344918784954359126101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014896612523302906084067 13522344918784954359126101)
              ·
                refine ⟨158464979517011183896009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13522344918784954359126101 158464979517011183896009)
                ·
                  rfl

theorem cell23_8332455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 8].length) (baseStart_8332455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332455 prefixEnd_8332455 := by exact prefixLift 8332455
  have htrace : WordTrace (prefixWord ++ tailWord_8332455) baseStart_8332455 baseEnd_8332455 := by
    simpa [prefixWord, tailWord_8332455, baseEnd_8332455] using wordTrace_append hprefix tailTrace_8332455
  have hstable : (prefixWord ++ tailWord_8332455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332455).length < 2 ^ (prefixWord ++ tailWord_8332455).sum := by decide
  have hdescent : baseEnd_8332455 < baseStart_8332455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332465 : List Nat := [1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_8332465 : Nat := 118140960795 + 8332465 * 2 ^ 59
def prefixEnd_8332465 : Nat := 4983230072969 + 3 ^ 40 * 8332465 * 2
def baseEnd_8332465 : Nat := 4278559581765846926067197

theorem tailTrace_8332465 : CollatzResearch.WordTrace tailWord_8332465 prefixEnd_8332465 4278559581765846926067197 := by
  unfold tailWord_8332465
  simp only [CollatzResearch.WordTrace]
  refine ⟨303909965757909851570582849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202606643838606567713721899 303909965757909851570582849)
  ·
    refine ⟨227932474318432388677937137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303909965757909851570582849 227932474318432388677937137)
    ·
      refine ⟨170949355738824291508452853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227932474318432388677937137 170949355738824291508452853)
      ·
        refine ⟨16026502100514777328917455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170949355738824291508452853 16026502100514777328917455)
        ·
          refine ⟨24039753150772165993376183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16026502100514777328917455 24039753150772165993376183)
          ·
            refine ⟨36059629726158248990064275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24039753150772165993376183 36059629726158248990064275)
            ·
              refine ⟨54089444589237373485096413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36059629726158248990064275 54089444589237373485096413)
              ·
                refine ⟨20283541720964015056911155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54089444589237373485096413 20283541720964015056911155)
                ·
                  refine ⟨30425312581446022585366733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20283541720964015056911155 30425312581446022585366733)
                  ·
                    refine ⟨11409492218042258469512525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30425312581446022585366733 11409492218042258469512525)
                    ·
                      refine ⟨4278559581765846926067197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11409492218042258469512525 4278559581765846926067197)
                      ·
                        rfl

theorem cell23_8332465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_8332465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332465 prefixEnd_8332465 := by exact prefixLift 8332465
  have htrace : WordTrace (prefixWord ++ tailWord_8332465) baseStart_8332465 baseEnd_8332465 := by
    simpa [prefixWord, tailWord_8332465, baseEnd_8332465] using wordTrace_append hprefix tailTrace_8332465
  have hstable : (prefixWord ++ tailWord_8332465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332465).length < 2 ^ (prefixWord ++ tailWord_8332465).sum := by decide
  have hdescent : baseEnd_8332465 < baseStart_8332465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332493 : List Nat := [1, 6, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_8332493 : Nat := 118140960795 + 8332493 * 2 ^ 59
def prefixEnd_8332493 : Nat := 4983230072969 + 3 ^ 40 * 8332493 * 2
def baseEnd_8332493 : Nat := 1426191319741390938839023

theorem tailTrace_8332493 : CollatzResearch.WordTrace tailWord_8332493 prefixEnd_8332493 1426191319741390938839023 := by
  unfold tailWord_8332493
  simp only [CollatzResearch.WordTrace]
  refine ⟨303910987001808412352602133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202607324667872274901734755 303910987001808412352602133)
  ·
    refine ⟨14245827515709769329028225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 303910987001808412352602133 14245827515709769329028225)
    ·
      refine ⟨10684370636782326996771169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14245827515709769329028225 10684370636782326996771169)
      ·
        refine ⟨8013277977586745247578377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10684370636782326996771169 8013277977586745247578377)
        ·
          refine ⟨6009958483190058935683783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8013277977586745247578377 6009958483190058935683783)
          ·
            refine ⟨9014937724785088403525675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6009958483190058935683783 9014937724785088403525675)
            ·
              refine ⟨13522406587177632605288513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9014937724785088403525675 13522406587177632605288513)
              ·
                refine ⟨10141804940383224453966385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13522406587177632605288513 10141804940383224453966385)
                ·
                  refine ⟨7606353705287418340474789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10141804940383224453966385 7606353705287418340474789)
                  ·
                    refine ⟨1426191319741390938839023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606353705287418340474789 1426191319741390938839023)
                    ·
                      rfl

theorem cell23_8332493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_8332493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332493 prefixEnd_8332493 := by exact prefixLift 8332493
  have htrace : WordTrace (prefixWord ++ tailWord_8332493) baseStart_8332493 baseEnd_8332493 := by
    simpa [prefixWord, tailWord_8332493, baseEnd_8332493] using wordTrace_append hprefix tailTrace_8332493
  have hstable : (prefixWord ++ tailWord_8332493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332493).length < 2 ^ (prefixWord ++ tailWord_8332493).sum := by decide
  have hdescent : baseEnd_8332493 < baseStart_8332493 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332498 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_8332498 : Nat := 118140960795 + 8332498 * 2 ^ 59
def prefixEnd_8332498 : Nat := 4983230072969 + 3 ^ 40 * 8332498 * 2
def baseEnd_8332498 : Nat := 1426192175542481765651515

theorem tailTrace_8332498 : CollatzResearch.WordTrace tailWord_8332498 prefixEnd_8332498 1426192175542481765651515 := by
  unfold tailWord_8332498
  simp only [CollatzResearch.WordTrace]
  refine ⟨75977792341697574551633537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202607446244526865471022765 75977792341697574551633537)
  ·
    refine ⟨56983344256273180913725153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75977792341697574551633537 56983344256273180913725153)
    ·
      refine ⟨42737508192204885685293865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56983344256273180913725153 42737508192204885685293865)
      ·
        refine ⟨32053131144153664263970399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42737508192204885685293865 32053131144153664263970399)
        ·
          refine ⟨48079696716230496395955599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32053131144153664263970399 48079696716230496395955599)
          ·
            refine ⟨72119545074345744593933399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48079696716230496395955599 72119545074345744593933399)
            ·
              refine ⟨108179317611518616890900099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72119545074345744593933399 108179317611518616890900099)
              ·
                refine ⟨162268976417277925336350149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108179317611518616890900099 162268976417277925336350149)
                ·
                  refine ⟨30425433078239611000565653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162268976417277925336350149 30425433078239611000565653)
                  ·
                    refine ⟨1426192175542481765651515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30425433078239611000565653 1426192175542481765651515)
                    ·
                      rfl

theorem cell23_8332498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_8332498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332498 prefixEnd_8332498 := by exact prefixLift 8332498
  have htrace : WordTrace (prefixWord ++ tailWord_8332498) baseStart_8332498 baseEnd_8332498 := by
    simpa [prefixWord, tailWord_8332498, baseEnd_8332498] using wordTrace_append hprefix tailTrace_8332498
  have hstable : (prefixWord ++ tailWord_8332498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332498).length < 2 ^ (prefixWord ++ tailWord_8332498).sum := by decide
  have hdescent : baseEnd_8332498 < baseStart_8332498 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332522 : List Nat := [3, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_8332522 : Nat := 118140960795 + 8332522 * 2 ^ 59
def prefixEnd_8332522 : Nat := 4983230072969 + 3 ^ 40 * 8332522 * 2
def baseEnd_8332522 : Nat := 4278588850163153203054435

theorem tailTrace_8332522 : CollatzResearch.WordTrace tailWord_8332522 prefixEnd_8332522 4278588850163153203054435 := by
  unfold tailWord_8332522
  simp only [CollatzResearch.WordTrace]
  refine ⟨75978011179675837576351955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202608029812468900203605213 75978011179675837576351955)
  ·
    refine ⟨113967016769513756364527933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75978011179675837576351955 113967016769513756364527933)
    ·
      refine ⟨42737631288567658636697975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113967016769513756364527933 42737631288567658636697975)
      ·
        refine ⟨64106446932851487955046963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42737631288567658636697975 64106446932851487955046963)
        ·
          refine ⟨96159670399277231932570445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64106446932851487955046963 96159670399277231932570445)
          ·
            refine ⟨36059876399728961974713917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96159670399277231932570445 36059876399728961974713917)
            ·
              refine ⟨13522453649898360740517719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36059876399728961974713917 13522453649898360740517719)
              ·
                refine ⟨20283680474847541110776579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13522453649898360740517719 20283680474847541110776579)
                ·
                  refine ⟨30425520712271311666164869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20283680474847541110776579 30425520712271311666164869)
                  ·
                    refine ⟨5704785133550870937405913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30425520712271311666164869 5704785133550870937405913)
                    ·
                      refine ⟨4278588850163153203054435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704785133550870937405913 4278588850163153203054435)
                      ·
                        rfl

theorem cell23_8332522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_8332522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332522 prefixEnd_8332522 := by exact prefixLift 8332522
  have htrace : WordTrace (prefixWord ++ tailWord_8332522) baseStart_8332522 baseEnd_8332522 := by
    simpa [prefixWord, tailWord_8332522, baseEnd_8332522] using wordTrace_append hprefix tailTrace_8332522
  have hstable : (prefixWord ++ tailWord_8332522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332522).length < 2 ^ (prefixWord ++ tailWord_8332522).sum := by decide
  have hdescent : baseEnd_8332522 < baseStart_8332522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332565 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_8332565 : Nat := 118140960795 + 8332565 * 2 ^ 59
def prefixEnd_8332565 : Nat := 4983230072969 + 3 ^ 40 * 8332565 * 2
def baseEnd_8332565 : Nat := 4278610929831296534816737

theorem tailTrace_8332565 : CollatzResearch.WordTrace tailWord_8332565 prefixEnd_8332565 4278610929831296534816737 := by
  unfold tailWord_8332565
  simp only [CollatzResearch.WordTrace]
  refine ⟨303913613057547568649223149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202609075371698379099482099 303913613057547568649223149)
  ·
    refine ⟨113967604896580338243458681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303913613057547568649223149 113967604896580338243458681)
    ·
      refine ⟨85475703672435253682594011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113967604896580338243458681 85475703672435253682594011)
      ·
        refine ⟨128213555508652880523891017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85475703672435253682594011 128213555508652880523891017)
        ·
          refine ⟨96160166631489660392918263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128213555508652880523891017 96160166631489660392918263)
          ·
            refine ⟨144240249947234490589377395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96160166631489660392918263 144240249947234490589377395)
            ·
              refine ⟨216360374920851735884066093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 144240249947234490589377395 216360374920851735884066093)
              ·
                refine ⟨81135140595319400956524785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216360374920851735884066093 81135140595319400956524785)
                ·
                  refine ⟨60851355446489550717393589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81135140595319400956524785 60851355446489550717393589)
                  ·
                    refine ⟨5704814573108395379755649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60851355446489550717393589 5704814573108395379755649)
                    ·
                      refine ⟨4278610929831296534816737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704814573108395379755649 4278610929831296534816737)
                      ·
                        rfl

theorem cell23_8332565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_8332565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332565 prefixEnd_8332565 := by exact prefixLift 8332565
  have htrace : WordTrace (prefixWord ++ tailWord_8332565) baseStart_8332565 baseEnd_8332565 := by
    simpa [prefixWord, tailWord_8332565, baseEnd_8332565] using wordTrace_append hprefix tailTrace_8332565
  have hstable : (prefixWord ++ tailWord_8332565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332565).length < 2 ^ (prefixWord ++ tailWord_8332565).sum := by decide
  have hdescent : baseEnd_8332565 < baseStart_8332565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332568 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_8332568 : Nat := 118140960795 + 8332568 * 2 ^ 59
def prefixEnd_8332568 : Nat := 4983230072969 + 3 ^ 40 * 8332568 * 2
def baseEnd_8332568 : Nat := 4278612470273260023079223

theorem tailTrace_8332568 : CollatzResearch.WordTrace tailWord_8332568 prefixEnd_8332568 4278612470273260023079223 := by
  unfold tailWord_8332568
  simp only [CollatzResearch.WordTrace]
  refine ⟨151956861238268350080791179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202609148317691133441054905 151956861238268350080791179)
  ·
    refine ⟨227935291857402525121186769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151956861238268350080791179 227935291857402525121186769)
    ·
      refine ⟨170951468893051893840890077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227935291857402525121186769 170951468893051893840890077)
      ·
        refine ⟨64106800834894460190333779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170951468893051893840890077 64106800834894460190333779)
        ·
          refine ⟨96160201252341690285500669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64106800834894460190333779 96160201252341690285500669)
          ·
            refine ⟨36060075469628133857062751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96160201252341690285500669 36060075469628133857062751)
            ·
              refine ⟨54090113204442200785594127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36060075469628133857062751 54090113204442200785594127)
              ·
                refine ⟨81135169806663301178391191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54090113204442200785594127 81135169806663301178391191)
                ·
                  refine ⟨121702754709994951767586787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81135169806663301178391191 121702754709994951767586787)
                  ·
                    refine ⟨182554132064992427651380181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121702754709994951767586787 182554132064992427651380181)
                    ·
                      refine ⟨4278612470273260023079223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182554132064992427651380181 4278612470273260023079223)
                      ·
                        rfl

theorem cell23_8332568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_8332568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332568 prefixEnd_8332568 := by exact prefixLift 8332568
  have htrace : WordTrace (prefixWord ++ tailWord_8332568) baseStart_8332568 baseEnd_8332568 := by
    simpa [prefixWord, tailWord_8332568, baseEnd_8332568] using wordTrace_append hprefix tailTrace_8332568
  have hstable : (prefixWord ++ tailWord_8332568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332568).length < 2 ^ (prefixWord ++ tailWord_8332568).sum := by decide
  have hdescent : baseEnd_8332568 < baseStart_8332568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332573 : List Nat := [1, 4, 2, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_8332573 : Nat := 118140960795 + 8332573 * 2 ^ 59
def prefixEnd_8332573 : Nat := 4983230072969 + 3 ^ 40 * 8332573 * 2
def baseEnd_8332573 : Nat := 4278615037676532503516701

theorem tailTrace_8332573 : CollatzResearch.WordTrace tailWord_8332573 prefixEnd_8332573 4278615037676532503516701 := by
  unfold tailWord_8332573
  simp only [CollatzResearch.WordTrace]
  refine ⟨303913904841518586015514373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202609269894345724010342915 303913904841518586015514373)
  ·
    refine ⟨56983857157784734877908945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303913904841518586015514373 56983857157784734877908945)
    ·
      refine ⟨42737892868338551158431709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56983857157784734877908945 42737892868338551158431709)
      ·
        refine ⟨16026709825626956684411891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42737892868338551158431709 16026709825626956684411891)
        ·
          refine ⟨24040064738440435026617837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16026709825626956684411891 24040064738440435026617837)
          ·
            refine ⟨9015024276915163134981689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24040064738440435026617837 9015024276915163134981689)
            ·
              refine ⟨6761268207686372351236267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9015024276915163134981689 6761268207686372351236267)
              ·
                refine ⟨10141902311529558526854401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761268207686372351236267 10141902311529558526854401)
                ·
                  refine ⟨7606426733647168895140801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10141902311529558526854401 7606426733647168895140801)
                  ·
                    refine ⟨5704820050235376671355601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606426733647168895140801 5704820050235376671355601)
                    ·
                      refine ⟨4278615037676532503516701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704820050235376671355601 4278615037676532503516701)
                      ·
                        rfl

theorem cell23_8332573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_8332573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332573 prefixEnd_8332573 := by exact prefixLift 8332573
  have htrace : WordTrace (prefixWord ++ tailWord_8332573) baseStart_8332573 baseEnd_8332573 := by
    simpa [prefixWord, tailWord_8332573, baseEnd_8332573] using wordTrace_append hprefix tailTrace_8332573
  have hstable : (prefixWord ++ tailWord_8332573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332573).length < 2 ^ (prefixWord ++ tailWord_8332573).sum := by decide
  have hdescent : baseEnd_8332573 < baseStart_8332573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332595 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 4]
def baseStart_8332595 : Nat := 118140960795 + 8332595 * 2 ^ 59
def prefixEnd_8332595 : Nat := 4983230072969 + 3 ^ 40 * 8332595 * 2
def baseEnd_8332595 : Nat := 4278626334250931417441599

theorem tailTrace_8332595 : CollatzResearch.WordTrace tailWord_8332595 prefixEnd_8332595 4278626334250931417441599 := by
  unfold tailWord_8332595
  simp only [CollatzResearch.WordTrace]
  refine ⟨303914707247438883772815239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202609804831625922515210159 303914707247438883772815239)
  ·
    refine ⟨455872060871158325659222859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303914707247438883772815239 455872060871158325659222859)
    ·
      refine ⟨683808091306737488488834289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455872060871158325659222859 683808091306737488488834289)
      ·
        refine ⟨512856068480053116366625717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683808091306737488488834289 512856068480053116366625717)
        ·
          refine ⟨48080256420004979659371161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 512856068480053116366625717 48080256420004979659371161)
          ·
            refine ⟨36060192315003734744528371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48080256420004979659371161 36060192315003734744528371)
            ·
              refine ⟨54090288472505602116792557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36060192315003734744528371 54090288472505602116792557)
              ·
                refine ⟨20283858177189600793797209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54090288472505602116792557 20283858177189600793797209)
                ·
                  refine ⟨15212893632892200595347907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20283858177189600793797209 15212893632892200595347907)
                  ·
                    refine ⟨22819340449338300893021861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15212893632892200595347907 22819340449338300893021861)
                    ·
                      refine ⟨4278626334250931417441599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22819340449338300893021861 4278626334250931417441599)
                      ·
                        rfl

theorem cell23_8332595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_8332595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332595 prefixEnd_8332595 := by exact prefixLift 8332595
  have htrace : WordTrace (prefixWord ++ tailWord_8332595) baseStart_8332595 baseEnd_8332595 := by
    simpa [prefixWord, tailWord_8332595, baseEnd_8332595] using wordTrace_append hprefix tailTrace_8332595
  have hstable : (prefixWord ++ tailWord_8332595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332595).length < 2 ^ (prefixWord ++ tailWord_8332595).sum := by decide
  have hdescent : baseEnd_8332595 < baseStart_8332595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332608 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_8332608 : Nat := 118140960795 + 8332608 * 2 ^ 59
def prefixEnd_8332608 : Nat := 4983230072969 + 3 ^ 40 * 8332608 * 2
def baseEnd_8332608 : Nat := 4278633009499439866579039

theorem tailTrace_8332608 : CollatzResearch.WordTrace tailWord_8332608 prefixEnd_8332608 4278633009499439866579039 := by
  unfold tailWord_8332608
  simp only [CollatzResearch.WordTrace]
  refine ⟨151957590698195893496519239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202610120930927857995358985 151957590698195893496519239)
  ·
    refine ⟨227936386047293840244778859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151957590698195893496519239 227936386047293840244778859)
    ·
      refine ⟨341904579070940760367168289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227936386047293840244778859 341904579070940760367168289)
      ·
        refine ⟨256428434303205570275376217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341904579070940760367168289 256428434303205570275376217)
        ·
          refine ⟨192321325727404177706532163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256428434303205570275376217 192321325727404177706532163)
          ·
            refine ⟨288481988591106266559798245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192321325727404177706532163 288481988591106266559798245)
            ·
              refine ⟨54090372860832424979962171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288481988591106266559798245 54090372860832424979962171)
              ·
                refine ⟨81135559291248637469943257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54090372860832424979962171 81135559291248637469943257)
                ·
                  refine ⟨60851669468436478102457443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81135559291248637469943257 60851669468436478102457443)
                  ·
                    refine ⟨91277504202654717153686165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60851669468436478102457443 91277504202654717153686165)
                    ·
                      refine ⟨4278633009499439866579039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91277504202654717153686165 4278633009499439866579039)
                      ·
                        rfl

theorem cell23_8332608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_8332608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332608 prefixEnd_8332608 := by exact prefixLift 8332608
  have htrace : WordTrace (prefixWord ++ tailWord_8332608) baseStart_8332608 baseEnd_8332608 := by
    simpa [prefixWord, tailWord_8332608, baseEnd_8332608] using wordTrace_append hprefix tailTrace_8332608
  have hstable : (prefixWord ++ tailWord_8332608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332608).length < 2 ^ (prefixWord ++ tailWord_8332608).sum := by decide
  have hdescent : baseEnd_8332608 < baseStart_8332608 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332618 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 8]
def baseStart_8332618 : Nat := 118140960795 + 8332618 * 2 ^ 59
def prefixEnd_8332618 : Nat := 4983230072969 + 3 ^ 40 * 8332618 * 2
def baseEnd_8332618 : Nat := 475404238256220536383777

theorem tailTrace_8332618 : CollatzResearch.WordTrace tailWord_8332618 prefixEnd_8332618 475404238256220536383777 := by
  unfold tailWord_8332618
  simp only [CollatzResearch.WordTrace]
  refine ⟨75978886531588889675225627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202610364084237039133935005 75978886531588889675225627)
  ·
    refine ⟨113968329797383334512838441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75978886531588889675225627 113968329797383334512838441)
    ·
      refine ⟨85476247348037500884628831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113968329797383334512838441 85476247348037500884628831)
      ·
        refine ⟨128214371022056251326943247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85476247348037500884628831 128214371022056251326943247)
        ·
          refine ⟨192321556533084376990414871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128214371022056251326943247 192321556533084376990414871)
          ·
            refine ⟨288482334799626565485622307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192321556533084376990414871 288482334799626565485622307)
            ·
              refine ⟨432723502199439848228433461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288482334799626565485622307 432723502199439848228433461)
              ·
                refine ⟨40567828331197485771415637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432723502199439848228433461 40567828331197485771415637)
                ·
                  refine ⟨475404238256220536383777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40567828331197485771415637 475404238256220536383777)
                  ·
                    rfl

theorem cell23_8332618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_8332618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332618 prefixEnd_8332618 := by exact prefixLift 8332618
  have htrace : WordTrace (prefixWord ++ tailWord_8332618) baseStart_8332618 baseEnd_8332618 := by
    simpa [prefixWord, tailWord_8332618, baseEnd_8332618] using wordTrace_append hprefix tailTrace_8332618
  have hstable : (prefixWord ++ tailWord_8332618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332618).length < 2 ^ (prefixWord ++ tailWord_8332618).sum := by decide
  have hdescent : baseEnd_8332618 < baseStart_8332618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332672 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 2, 3, 2]
def baseStart_8332672 : Nat := 118140960795 + 8332672 * 2 ^ 59
def prefixEnd_8332672 : Nat := 4983230072969 + 3 ^ 40 * 8332672 * 2
def baseEnd_8332672 : Nat := 4278665872261327616178745

theorem tailTrace_8332672 : CollatzResearch.WordTrace tailWord_8332672 prefixEnd_8332672 4278665872261327616178745 := by
  unfold tailWord_8332672
  simp only [CollatzResearch.WordTrace]
  refine ⟨151958757834079962961684135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202611677112106617282245513 151958757834079962961684135)
  ·
    refine ⟨227938136751119944442526203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151958757834079962961684135 227938136751119944442526203)
    ·
      refine ⟨341907205126679916663789305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227938136751119944442526203 341907205126679916663789305)
      ·
        refine ⟨256430403845009937497841979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341907205126679916663789305 256430403845009937497841979)
        ·
          refine ⟨384645605767514906246762969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256430403845009937497841979 384645605767514906246762969)
          ·
            refine ⟨288484204325636179685072227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384645605767514906246762969 288484204325636179685072227)
            ·
              refine ⟨432726306488454269527608341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288484204325636179685072227 432726306488454269527608341)
              ·
                refine ⟨20284045616646293884106641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432726306488454269527608341 20284045616646293884106641)
                ·
                  refine ⟨15213034212484720413079981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20284045616646293884106641 15213034212484720413079981)
                  ·
                    refine ⟨5704887829681770154904993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15213034212484720413079981 5704887829681770154904993)
                    ·
                      refine ⟨4278665872261327616178745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704887829681770154904993 4278665872261327616178745)
                      ·
                        rfl

theorem cell23_8332672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_8332672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332672 prefixEnd_8332672 := by exact prefixLift 8332672
  have htrace : WordTrace (prefixWord ++ tailWord_8332672) baseStart_8332672 baseEnd_8332672 := by
    simpa [prefixWord, tailWord_8332672, baseEnd_8332672] using wordTrace_append hprefix tailTrace_8332672
  have hstable : (prefixWord ++ tailWord_8332672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332672).length < 2 ^ (prefixWord ++ tailWord_8332672).sum := by decide
  have hdescent : baseEnd_8332672 < baseStart_8332672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332679 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_8332679 : Nat := 118140960795 + 8332679 * 2 ^ 59
def prefixEnd_8332679 : Nat := 4983230072969 + 3 ^ 40 * 8332679 * 2
def baseEnd_8332679 : Nat := 4278669466625909088791213

theorem tailTrace_8332679 : CollatzResearch.WordTrace tailWord_8332679 prefixEnd_8332679 4278669466625909088791213 := by
  unfold tailWord_8332679
  simp only [CollatzResearch.WordTrace]
  refine ⟨303917770979134566118873091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202611847319423044079248727 303917770979134566118873091)
  ·
    refine ⟨455876656468701849178309637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303917770979134566118873091 455876656468701849178309637)
    ·
      refine ⟨85476873087881596720933057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455876656468701849178309637 85476873087881596720933057)
      ·
        refine ⟨64107654815911197540699793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85476873087881596720933057 64107654815911197540699793)
        ·
          refine ⟨48080741111933398155524845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64107654815911197540699793 48080741111933398155524845)
          ·
            refine ⟨18030277916975024308321817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48080741111933398155524845 18030277916975024308321817)
            ·
              refine ⟨13522708437731268231241363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18030277916975024308321817 13522708437731268231241363)
              ·
                refine ⟨20284062656596902346862045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13522708437731268231241363 20284062656596902346862045)
                ·
                  refine ⟨7606523496223838380073267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20284062656596902346862045 7606523496223838380073267)
                  ·
                    refine ⟨11409785244335757570109901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7606523496223838380073267 11409785244335757570109901)
                    ·
                      refine ⟨4278669466625909088791213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11409785244335757570109901 4278669466625909088791213)
                      ·
                        rfl

theorem cell23_8332679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_8332679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332679 prefixEnd_8332679 := by exact prefixLift 8332679
  have htrace : WordTrace (prefixWord ++ tailWord_8332679) baseStart_8332679 baseEnd_8332679 := by
    simpa [prefixWord, tailWord_8332679, baseEnd_8332679] using wordTrace_append hprefix tailTrace_8332679
  have hstable : (prefixWord ++ tailWord_8332679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332679).length < 2 ^ (prefixWord ++ tailWord_8332679).sum := by decide
  have hdescent : baseEnd_8332679 < baseStart_8332679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332725 : List Nat := [1, 3, 3, 2, 2, 1, 11]
def baseStart_8332725 : Nat := 118140960795 + 8332725 * 2 ^ 59
def prefixEnd_8332725 : Nat := 4983230072969 + 3 ^ 40 * 8332725 * 2
def baseEnd_8332725 : Nat := 52823371441185381590321

theorem tailTrace_8332725 : CollatzResearch.WordTrace tailWord_8332725 prefixEnd_8332725 52823371441185381590321 := by
  unfold tailWord_8332725
  simp only [CollatzResearch.WordTrace]
  refine ⟨303919448736967915975047629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202612965824645277316698419 303919448736967915975047629)
  ·
    refine ⟨113969793276362968490642861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303919448736967915975047629 113969793276362968490642861)
    ·
      refine ⟨42738672478636113183991073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113969793276362968490642861 42738672478636113183991073)
      ·
        refine ⟨32054004358977084887993305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42738672478636113183991073 32054004358977084887993305)
        ·
          refine ⟨24040503269232813665994979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32054004358977084887993305 24040503269232813665994979)
          ·
            refine ⟨36060754903849220498992469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24040503269232813665994979 36060754903849220498992469)
            ·
              refine ⟨52823371441185381590321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 36060754903849220498992469 52823371441185381590321)
              ·
                rfl

theorem cell23_8332725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 11].length) (baseStart_8332725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332725 prefixEnd_8332725 := by exact prefixLift 8332725
  have htrace : WordTrace (prefixWord ++ tailWord_8332725) baseStart_8332725 baseEnd_8332725 := by
    simpa [prefixWord, tailWord_8332725, baseEnd_8332725] using wordTrace_append hprefix tailTrace_8332725
  have hstable : (prefixWord ++ tailWord_8332725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332725).length < 2 ^ (prefixWord ++ tailWord_8332725).sum := by decide
  have hdescent : baseEnd_8332725 < baseStart_8332725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332736 : List Nat := [2, 1, 1, 2, 3, 1, 2, 6, 1, 2, 2]
def baseStart_8332736 : Nat := 118140960795 + 8332736 * 2 ^ 59
def prefixEnd_8332736 : Nat := 4983230072969 + 3 ^ 40 * 8332736 * 2
def baseEnd_8332736 : Nat := 4278698735023215365778451

theorem tailTrace_8332736 : CollatzResearch.WordTrace tailWord_8332736 prefixEnd_8332736 4278698735023215365778451 := by
  unfold tailWord_8332736
  simp only [CollatzResearch.WordTrace]
  refine ⟨151959924969964032426849031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202613233293285376569132041 151959924969964032426849031)
  ·
    refine ⟨227939887454946048640273547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151959924969964032426849031 227939887454946048640273547)
    ·
      refine ⟨341909831182419072960410321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227939887454946048640273547 341909831182419072960410321)
      ·
        refine ⟨256432373386814304720307741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341909831182419072960410321 256432373386814304720307741)
        ·
          refine ⟨96162140020055364270115403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 256432373386814304720307741 96162140020055364270115403)
          ·
            refine ⟨144243210030083046405173105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96162140020055364270115403 144243210030083046405173105)
            ·
              refine ⟨108182407522562284803879829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144243210030083046405173105 108182407522562284803879829)
              ·
                refine ⟨5071050352620107100181867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108182407522562284803879829 5071050352620107100181867)
                ·
                  refine ⟨7606575528930160650272801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071050352620107100181867 7606575528930160650272801)
                  ·
                    refine ⟨5704931646697620487704601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606575528930160650272801 5704931646697620487704601)
                    ·
                      refine ⟨4278698735023215365778451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704931646697620487704601 4278698735023215365778451)
                      ·
                        rfl

theorem cell23_8332736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 6, 1, 2, 2].length) (baseStart_8332736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332736 prefixEnd_8332736 := by exact prefixLift 8332736
  have htrace : WordTrace (prefixWord ++ tailWord_8332736) baseStart_8332736 baseEnd_8332736 := by
    simpa [prefixWord, tailWord_8332736, baseEnd_8332736] using wordTrace_append hprefix tailTrace_8332736
  have hstable : (prefixWord ++ tailWord_8332736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332736).length < 2 ^ (prefixWord ++ tailWord_8332736).sum := by decide
  have hdescent : baseEnd_8332736 < baseStart_8332736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332746 : List Nat := [3, 1, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_8332746 : Nat := 118140960795 + 8332746 * 2 ^ 59
def prefixEnd_8332746 : Nat := 4983230072969 + 3 ^ 40 * 8332746 * 2
def baseEnd_8332746 : Nat := 1426234623276586775551135

theorem tailTrace_8332746 : CollatzResearch.WordTrace tailWord_8332746 prefixEnd_8332746 1426234623276586775551135 := by
  unfold tailWord_8332746
  simp only [CollatzResearch.WordTrace]
  refine ⟨75980053667472959140390523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202613476446594557707708061 75980053667472959140390523)
  ·
    refine ⟨113970080501209438710585785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75980053667472959140390523 113970080501209438710585785)
    ·
      refine ⟨85477560375907079032939339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113970080501209438710585785 85477560375907079032939339)
      ·
        refine ⟨128216340563860618549409009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85477560375907079032939339 128216340563860618549409009)
        ·
          refine ⟨96162255422895463912056757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128216340563860618549409009 96162255422895463912056757)
          ·
            refine ⟨9015211445896449741755321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96162255422895463912056757 9015211445896449741755321)
            ·
              refine ⟨6761408584422337306316491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9015211445896449741755321 6761408584422337306316491)
              ·
                refine ⟨10142112876633505959474737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761408584422337306316491 10142112876633505959474737)
                ·
                  refine ⟨7606584657475129469606053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142112876633505959474737 7606584657475129469606053)
                  ·
                    refine ⟨1426234623276586775551135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606584657475129469606053 1426234623276586775551135)
                    ·
                      rfl

theorem cell23_8332746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_8332746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332746 prefixEnd_8332746 := by exact prefixLift 8332746
  have htrace : WordTrace (prefixWord ++ tailWord_8332746) baseStart_8332746 baseEnd_8332746 := by
    simpa [prefixWord, tailWord_8332746, baseEnd_8332746] using wordTrace_append hprefix tailTrace_8332746
  have hstable : (prefixWord ++ tailWord_8332746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332746).length < 2 ^ (prefixWord ++ tailWord_8332746).sum := by decide
  have hdescent : baseEnd_8332746 < baseStart_8332746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332786 : List Nat := [3, 2, 1, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_8332786 : Nat := 118140960795 + 8332786 * 2 ^ 59
def prefixEnd_8332786 : Nat := 4983230072969 + 3 ^ 40 * 8332786 * 2
def baseEnd_8332786 : Nat := 4278724409055940170153221

theorem tailTrace_8332786 : CollatzResearch.WordTrace tailWord_8332786 prefixEnd_8332786 4278724409055940170153221 := by
  unfold tailWord_8332786
  simp only [CollatzResearch.WordTrace]
  refine ⟨75980418397436730848254553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202614449059831282262012141 75980418397436730848254553)
  ·
    refine ⟨56985313798077548136190915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75980418397436730848254553 56985313798077548136190915)
    ·
      refine ⟨85477970697116322204286373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56985313798077548136190915 85477970697116322204286373)
      ·
        refine ⟨16027119505709310413303695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85477970697116322204286373 16027119505709310413303695)
        ·
          refine ⟨24040679258563965619955543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16027119505709310413303695 24040679258563965619955543)
          ·
            refine ⟨36061018887845948429933315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24040679258563965619955543 36061018887845948429933315)
            ·
              refine ⟨54091528331768922644899973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36061018887845948429933315 54091528331768922644899973)
              ·
                refine ⟨10142161562206672995918745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54091528331768922644899973 10142161562206672995918745)
                ·
                  refine ⟨7606621171655004746939059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142161562206672995918745 7606621171655004746939059)
                  ·
                    refine ⟨11409931757482507120408589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7606621171655004746939059 11409931757482507120408589)
                    ·
                      refine ⟨4278724409055940170153221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11409931757482507120408589 4278724409055940170153221)
                      ·
                        rfl

theorem cell23_8332786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_8332786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332786 prefixEnd_8332786 := by exact prefixLift 8332786
  have htrace : WordTrace (prefixWord ++ tailWord_8332786) baseStart_8332786 baseEnd_8332786 := by
    simpa [prefixWord, tailWord_8332786, baseEnd_8332786] using wordTrace_append hprefix tailTrace_8332786
  have hstable : (prefixWord ++ tailWord_8332786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332786).length < 2 ^ (prefixWord ++ tailWord_8332786).sum := by decide
  have hdescent : baseEnd_8332786 < baseStart_8332786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332809 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 1, 4, 2]
def baseStart_8332809 : Nat := 118140960795 + 8332809 * 2 ^ 59
def prefixEnd_8332809 : Nat := 4983230072969 + 3 ^ 40 * 8332809 * 2
def baseEnd_8332809 : Nat := 4278736219110993580165615

theorem tailTrace_8332809 : CollatzResearch.WordTrace tailWord_8332809 prefixEnd_8332809 4278736219110993580165615 := by
  unfold tailWord_8332809
  simp only [CollatzResearch.WordTrace]
  refine ⟨303922512468663598321105481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202615008312442398880736987 303922512468663598321105481)
  ·
    refine ⟨227941884351497698740829111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303922512468663598321105481 227941884351497698740829111)
    ·
      refine ⟨341912826527246548111243667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227941884351497698740829111 341912826527246548111243667)
      ·
        refine ⟨512869239790869822166865501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341912826527246548111243667 512869239790869822166865501)
        ·
          refine ⟨192325964921576183312574563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512869239790869822166865501 192325964921576183312574563)
          ·
            refine ⟨288488947382364274968861845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192325964921576183312574563 288488947382364274968861845)
            ·
              refine ⟨13522919408548325389165399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288488947382364274968861845 13522919408548325389165399)
              ·
                refine ⟨20284379112822488083748099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13522919408548325389165399 20284379112822488083748099)
                ·
                  refine ⟨30426568669233732125622149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20284379112822488083748099 30426568669233732125622149)
                  ·
                    refine ⟨5704981625481324773554153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30426568669233732125622149 5704981625481324773554153)
                    ·
                      refine ⟨4278736219110993580165615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5704981625481324773554153 4278736219110993580165615)
                      ·
                        rfl

theorem cell23_8332809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 4, 2].length) (baseStart_8332809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332809 prefixEnd_8332809 := by exact prefixLift 8332809
  have htrace : WordTrace (prefixWord ++ tailWord_8332809) baseStart_8332809 baseEnd_8332809 := by
    simpa [prefixWord, tailWord_8332809, baseEnd_8332809] using wordTrace_append hprefix tailTrace_8332809
  have hstable : (prefixWord ++ tailWord_8332809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332809).length < 2 ^ (prefixWord ++ tailWord_8332809).sum := by decide
  have hdescent : baseEnd_8332809 < baseStart_8332809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332860 : List Nat := [2, 2, 2, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_8332860 : Nat := 118140960795 + 8332860 * 2 ^ 59
def prefixEnd_8332860 : Nat := 4983230072969 + 3 ^ 40 * 8332860 * 2
def baseEnd_8332860 : Nat := 4278762406624372880627881

theorem tailTrace_8332860 : CollatzResearch.WordTrace tailWord_8332860 prefixEnd_8332860 4278762406624372880627881 := by
  unfold tailWord_8332860
  simp only [CollatzResearch.WordTrace]
  refine ⟨151962186295739417015606017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202616248394319222687474689 151962186295739417015606017)
  ·
    refine ⟨113971639721804562761704513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151962186295739417015606017 113971639721804562761704513)
    ·
      refine ⟨85478729791353422071278385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113971639721804562761704513 85478729791353422071278385)
      ·
        refine ⟨64109047343515066553458789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85478729791353422071278385 64109047343515066553458789)
        ·
          refine ⟨12020446376909074978773523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64109047343515066553458789 12020446376909074978773523)
          ·
            refine ⟨18030669565363612468160285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020446376909074978773523 18030669565363612468160285)
            ·
              refine ⟨6761501087011354675560107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18030669565363612468160285 6761501087011354675560107)
              ·
                refine ⟨10142251630517032013340161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761501087011354675560107 10142251630517032013340161)
                ·
                  refine ⟨7606688722887774010005121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142251630517032013340161 7606688722887774010005121)
                  ·
                    refine ⟨5705016542165830507503841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606688722887774010005121 5705016542165830507503841)
                    ·
                      refine ⟨4278762406624372880627881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705016542165830507503841 4278762406624372880627881)
                      ·
                        rfl

theorem cell23_8332860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_8332860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332860 prefixEnd_8332860 := by exact prefixLift 8332860
  have htrace : WordTrace (prefixWord ++ tailWord_8332860) baseStart_8332860 baseEnd_8332860 := by
    simpa [prefixWord, tailWord_8332860, baseEnd_8332860] using wordTrace_append hprefix tailTrace_8332860
  have hstable : (prefixWord ++ tailWord_8332860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332860).length < 2 ^ (prefixWord ++ tailWord_8332860).sum := by decide
  have hdescent : baseEnd_8332860 < baseStart_8332860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332875 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 10]
def baseStart_8332875 : Nat := 118140960795 + 8332875 * 2 ^ 59
def prefixEnd_8332875 : Nat := 4983230072969 + 3 ^ 40 * 8332875 * 2
def baseEnd_8332875 : Nat := 1426256702944730107313437

theorem tailTrace_8332875 : CollatzResearch.WordTrace tailWord_8332875 prefixEnd_8332875 1426256702944730107313437 := by
  unfold tailWord_8332875
  simp only [CollatzResearch.WordTrace]
  refine ⟨303924919686424491593008079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202616613124282994395338719 303924919686424491593008079)
  ·
    refine ⟨455887379529636737389512119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303924919686424491593008079 455887379529636737389512119)
    ·
      refine ⟨683831069294455106084268179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455887379529636737389512119 683831069294455106084268179)
      ·
        refine ⟨1025746603941682659126402269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683831069294455106084268179 1025746603941682659126402269)
        ·
          refine ⟨384654976478130997172400851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1025746603941682659126402269 384654976478130997172400851)
          ·
            refine ⟨576982464717196495758601277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384654976478130997172400851 576982464717196495758601277)
            ·
              refine ⟨216368424268948685909475479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576982464717196495758601277 216368424268948685909475479)
              ·
                refine ⟨324552636403423028864213219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216368424268948685909475479 324552636403423028864213219)
                ·
                  refine ⟨486828954605134543296319829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 324552636403423028864213219 486828954605134543296319829)
                  ·
                    refine ⟨1426256702944730107313437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 486828954605134543296319829 1426256702944730107313437)
                    ·
                      rfl

theorem cell23_8332875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_8332875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332875 prefixEnd_8332875 := by exact prefixLift 8332875
  have htrace : WordTrace (prefixWord ++ tailWord_8332875) baseStart_8332875 baseEnd_8332875 := by
    simpa [prefixWord, tailWord_8332875, baseEnd_8332875] using wordTrace_append hprefix tailTrace_8332875
  have hstable : (prefixWord ++ tailWord_8332875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332875).length < 2 ^ (prefixWord ++ tailWord_8332875).sum := by decide
  have hdescent : baseEnd_8332875 < baseStart_8332875 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332899 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 4]
def baseStart_8332899 : Nat := 118140960795 + 8332899 * 2 ^ 59
def prefixEnd_8332899 : Nat := 4983230072969 + 3 ^ 40 * 8332899 * 2
def baseEnd_8332899 : Nat := 4278782432369898228040201

theorem tailTrace_8332899 : CollatzResearch.WordTrace tailWord_8332899 prefixEnd_8332899 4278782432369898228040201 := by
  unfold tailWord_8332899
  simp only [CollatzResearch.WordTrace]
  refine ⟨303925795038337543691881751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202617196692225029127921167 303925795038337543691881751)
  ·
    refine ⟨455888692557506315537822627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303925795038337543691881751 455888692557506315537822627)
    ·
      refine ⟨683833038836259473306733941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455888692557506315537822627 683833038836259473306733941)
      ·
        refine ⟨64109347390899325622506307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 683833038836259473306733941 64109347390899325622506307)
        ·
          refine ⟨96164021086348988433759461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64109347390899325622506307 96164021086348988433759461)
          ·
            refine ⟨18030753953690435331329899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96164021086348988433759461 18030753953690435331329899)
            ·
              refine ⟨27046130930535652996994849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18030753953690435331329899 27046130930535652996994849)
              ·
                refine ⟨20284598197901739747746137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27046130930535652996994849 20284598197901739747746137)
                ·
                  refine ⟨15213448648426304810809603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20284598197901739747746137 15213448648426304810809603)
                  ·
                    refine ⟨22820172972639457216214405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15213448648426304810809603 22820172972639457216214405)
                    ·
                      refine ⟨4278782432369898228040201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22820172972639457216214405 4278782432369898228040201)
                      ·
                        rfl

theorem cell23_8332899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_8332899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332899 prefixEnd_8332899 := by exact prefixLift 8332899
  have htrace : WordTrace (prefixWord ++ tailWord_8332899) baseStart_8332899 baseEnd_8332899 := by
    simpa [prefixWord, tailWord_8332899, baseEnd_8332899] using wordTrace_append hprefix tailTrace_8332899
  have hstable : (prefixWord ++ tailWord_8332899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332899).length < 2 ^ (prefixWord ++ tailWord_8332899).sum := by decide
  have hdescent : baseEnd_8332899 < baseStart_8332899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332956 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 6]
def baseStart_8332956 : Nat := 118140960795 + 8332956 * 2 ^ 59
def prefixEnd_8332956 : Nat := 4983230072969 + 3 ^ 40 * 8332956 * 2
def baseEnd_8332956 : Nat := 475423522307467167225271

theorem tailTrace_8332956 : CollatzResearch.WordTrace tailWord_8332956 prefixEnd_8332956 475423522307467167225271 := by
  unfold tailWord_8332956
  simp only [CollatzResearch.WordTrace]
  refine ⟨151963936999565521213353361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202618582666087361617804481 151963936999565521213353361)
  ·
    refine ⟨113972952749674140910015021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151963936999565521213353361 113972952749674140910015021)
    ·
      refine ⟨42739857281127802841255633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113972952749674140910015021 42739857281127802841255633)
      ·
        refine ⟨32054892960845852130941725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42739857281127802841255633 32054892960845852130941725)
        ·
          refine ⟨12020584860317194549103147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32054892960845852130941725 12020584860317194549103147)
          ·
            refine ⟨18030877290475791823654721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020584860317194549103147 18030877290475791823654721)
            ·
              refine ⟨13523157967856843867741041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18030877290475791823654721 13523157967856843867741041)
              ·
                refine ⟨10142368475892632900805781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523157967856843867741041 10142368475892632900805781)
                ·
                  refine ⟨475423522307467167225271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10142368475892632900805781 475423522307467167225271)
                  ·
                    rfl

theorem cell23_8332956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_8332956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332956 prefixEnd_8332956 := by exact prefixLift 8332956
  have htrace : WordTrace (prefixWord ++ tailWord_8332956) baseStart_8332956 baseEnd_8332956 := by
    simpa [prefixWord, tailWord_8332956, baseEnd_8332956] using wordTrace_append hprefix tailTrace_8332956
  have hstable : (prefixWord ++ tailWord_8332956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332956).length < 2 ^ (prefixWord ++ tailWord_8332956).sum := by decide
  have hdescent : baseEnd_8332956 < baseStart_8332956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332960 : List Nat := [2, 1, 1, 4, 3, 3, 2, 2, 1, 4]
def baseStart_8332960 : Nat := 118140960795 + 8332960 * 2 ^ 59
def prefixEnd_8332960 : Nat := 4983230072969 + 3 ^ 40 * 8332960 * 2
def baseEnd_8332960 : Nat := 1426271251563274163125807

theorem tailTrace_8332960 : CollatzResearch.WordTrace tailWord_8332960 prefixEnd_8332960 1426271251563274163125807 := by
  unfold tailWord_8332960
  simp only [CollatzResearch.WordTrace]
  refine ⟨151964009945558275554926167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202618679927411034073234889 151964009945558275554926167)
  ·
    refine ⟨227946014918337413332389251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151964009945558275554926167 227946014918337413332389251)
    ·
      refine ⟨341919022377506119998583877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227946014918337413332389251 341919022377506119998583877)
      ·
        refine ⟨64109816695782397499734477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341919022377506119998583877 64109816695782397499734477)
        ·
          refine ⟨24041181260918399062400429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64109816695782397499734477 24041181260918399062400429)
          ·
            refine ⟨9015442972844399648400161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24041181260918399062400429 9015442972844399648400161)
            ·
              refine ⟨6761582229633299736300121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9015442972844399648400161 6761582229633299736300121)
              ·
                refine ⟨5071186672224974802225091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6761582229633299736300121 5071186672224974802225091)
                ·
                  refine ⟨7606780008337462203337637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071186672224974802225091 7606780008337462203337637)
                  ·
                    refine ⟨1426271251563274163125807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606780008337462203337637 1426271251563274163125807)
                    ·
                      rfl

theorem cell23_8332960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 4].length) (baseStart_8332960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332960 prefixEnd_8332960 := by exact prefixLift 8332960
  have htrace : WordTrace (prefixWord ++ tailWord_8332960) baseStart_8332960 baseEnd_8332960 := by
    simpa [prefixWord, tailWord_8332960, baseEnd_8332960] using wordTrace_append hprefix tailTrace_8332960
  have hstable : (prefixWord ++ tailWord_8332960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332960).length < 2 ^ (prefixWord ++ tailWord_8332960).sum := by decide
  have hdescent : baseEnd_8332960 < baseStart_8332960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332989 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_8332989 : Nat := 118140960795 + 8332989 * 2 ^ 59
def prefixEnd_8332989 : Nat := 4983230072969 + 3 ^ 40 * 8332989 * 2
def baseEnd_8332989 : Nat := 4278828645628802875914787

theorem tailTrace_8332989 : CollatzResearch.WordTrace tailWord_8332989 prefixEnd_8332989 4278828645628802875914787 := by
  unfold tailWord_8332989
  simp only [CollatzResearch.WordTrace]
  refine ⟨303929077608011489062658021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202619385072007659375105347 303929077608011489062658021)
  ·
    refine ⟨56986702051502154199248379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303929077608011489062658021 56986702051502154199248379)
    ·
      refine ⟨85480053077253231298872569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56986702051502154199248379 85480053077253231298872569)
      ·
        refine ⟨64110039807939923474154427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85480053077253231298872569 64110039807939923474154427)
        ·
          refine ⟨96165059711909885211231641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64110039807939923474154427 96165059711909885211231641)
          ·
            refine ⟨72123794783932413908423731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96165059711909885211231641 72123794783932413908423731)
            ·
              refine ⟨108185692175898620862635597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72123794783932413908423731 108185692175898620862635597)
              ·
                refine ⟨40569634565961982823488349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108185692175898620862635597 40569634565961982823488349)
                ·
                  refine ⟨15213612962235743558808131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40569634565961982823488349 15213612962235743558808131)
                  ·
                    refine ⟨22820419443353615338212197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15213612962235743558808131 22820419443353615338212197)
                    ·
                      refine ⟨4278828645628802875914787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22820419443353615338212197 4278828645628802875914787)
                      ·
                        rfl

theorem cell23_8332989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_8332989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332989 prefixEnd_8332989 := by exact prefixLift 8332989
  have htrace : WordTrace (prefixWord ++ tailWord_8332989) baseStart_8332989 baseEnd_8332989 := by
    simpa [prefixWord, tailWord_8332989, baseEnd_8332989] using wordTrace_append hprefix tailTrace_8332989
  have hstable : (prefixWord ++ tailWord_8332989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332989).length < 2 ^ (prefixWord ++ tailWord_8332989).sum := by decide
  have hdescent : baseEnd_8332989 < baseStart_8332989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332994 : List Nat := [3, 5, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_8332994 : Nat := 118140960795 + 8332994 * 2 ^ 59
def prefixEnd_8332994 : Nat := 4983230072969 + 3 ^ 40 * 8332994 * 2
def baseEnd_8332994 : Nat := 1426277071010691785450755

theorem tailTrace_8332994 : CollatzResearch.WordTrace tailWord_8332994 prefixEnd_8332994 1426277071010691785450755 := by
  unfold tailWord_8332994
  simp only [CollatzResearch.WordTrace]
  refine ⟨75982314993248343729147509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202619506648662249944393357 75982314993248343729147509)
  ·
    refine ⟨7123342030617032224607579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75982314993248343729147509 7123342030617032224607579)
    ·
      refine ⟨10685013045925548336911369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7123342030617032224607579 10685013045925548336911369)
      ·
        refine ⟨8013759784444161252683527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10685013045925548336911369 8013759784444161252683527)
        ·
          refine ⟨12020639676666241879025291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8013759784444161252683527 12020639676666241879025291)
          ·
            refine ⟨18030959514999362818537937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12020639676666241879025291 18030959514999362818537937)
            ·
              refine ⟨13523219636249522113903453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18030959514999362818537937 13523219636249522113903453)
              ·
                refine ⟨5071207363593570792713795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13523219636249522113903453 5071207363593570792713795)
                ·
                  refine ⟨7606811045390356189070693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071207363593570792713795 7606811045390356189070693)
                  ·
                    refine ⟨1426277071010691785450755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606811045390356189070693 1426277071010691785450755)
                    ·
                      rfl

theorem cell23_8332994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_8332994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332994 prefixEnd_8332994 := by exact prefixLift 8332994
  have htrace : WordTrace (prefixWord ++ tailWord_8332994) baseStart_8332994 baseEnd_8332994 := by
    simpa [prefixWord, tailWord_8332994, baseEnd_8332994] using wordTrace_append hprefix tailTrace_8332994
  have hstable : (prefixWord ++ tailWord_8332994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332994).length < 2 ^ (prefixWord ++ tailWord_8332994).sum := by decide
  have hdescent : baseEnd_8332994 < baseStart_8332994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8332999 : List Nat := [1, 1, 4, 1, 1, 1, 4, 2, 4, 4]
def baseStart_8332999 : Nat := 118140960795 + 8332999 * 2 ^ 59
def prefixEnd_8332999 : Nat := 4983230072969 + 3 ^ 40 * 8332999 * 2
def baseEnd_8332999 : Nat := 1426277926811782612263247

theorem tailTrace_8332999 : CollatzResearch.WordTrace tailWord_8332999 prefixEnd_8332999 1426277926811782612263247 := by
  unfold tailWord_8332999
  simp only [CollatzResearch.WordTrace]
  refine ⟨303929442337975260770522051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202619628225316840513681367 303929442337975260770522051)
  ·
    refine ⟨455894163506962891155783077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303929442337975260770522051 455894163506962891155783077)
    ·
      refine ⟨85480155657555542091709327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455894163506962891155783077 85480155657555542091709327)
      ·
        refine ⟨128220233486333313137563991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85480155657555542091709327 128220233486333313137563991)
        ·
          refine ⟨192330350229499969706345987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128220233486333313137563991 192330350229499969706345987)
          ·
            refine ⟨288495525344249954559518981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192330350229499969706345987 288495525344249954559518981)
            ·
              refine ⟨54092911002046866479909809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 288495525344249954559518981 54092911002046866479909809)
              ·
                refine ⟨40569683251535149859932357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54092911002046866479909809 40569683251535149859932357)
                ·
                  refine ⟨7606815609662840598737317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40569683251535149859932357 7606815609662840598737317)
                  ·
                    refine ⟨1426277926811782612263247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7606815609662840598737317 1426277926811782612263247)
                    ·
                      rfl

theorem cell23_8332999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_8332999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8332999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8332999 prefixEnd_8332999 := by exact prefixLift 8332999
  have htrace : WordTrace (prefixWord ++ tailWord_8332999) baseStart_8332999 baseEnd_8332999 := by
    simpa [prefixWord, tailWord_8332999, baseEnd_8332999] using wordTrace_append hprefix tailTrace_8332999
  have hstable : (prefixWord ++ tailWord_8332999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8332999).length < 2 ^ (prefixWord ++ tailWord_8332999).sum := by decide
  have hdescent : baseEnd_8332999 < baseStart_8332999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8332999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333006 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_8333006 : Nat := 118140960795 + 8333006 * 2 ^ 59
def prefixEnd_8333006 : Nat := 4983230072969 + 3 ^ 40 * 8333006 * 2
def baseEnd_8333006 : Nat := 4278837374799929309402209

theorem tailTrace_8333006 : CollatzResearch.WordTrace tailWord_8333006 prefixEnd_8333006 4278837374799929309402209 := by
  unfold tailWord_8333006
  simp only [CollatzResearch.WordTrace]
  refine ⟨37991212206118737620753359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202619798432633267310684581 37991212206118737620753359)
  ·
    refine ⟨56986818309178106431130039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37991212206118737620753359 56986818309178106431130039)
    ·
      refine ⟨85480227463767159646695059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56986818309178106431130039 85480227463767159646695059)
      ·
        refine ⟨128220341195650739470042589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85480227463767159646695059 128220341195650739470042589)
        ·
          refine ⟨48082627948369027301265971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128220341195650739470042589 48082627948369027301265971)
          ·
            refine ⟨72123941922553540951898957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48082627948369027301265971 72123941922553540951898957)
            ·
              refine ⟨27046478220957577856962109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72123941922553540951898957 27046478220957577856962109)
              ·
                refine ⟨10142429332859091696360791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27046478220957577856962109 10142429332859091696360791)
                ·
                  refine ⟨15213643999288637544541187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10142429332859091696360791 15213643999288637544541187)
                  ·
                    refine ⟨22820465998932956316811781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15213643999288637544541187 22820465998932956316811781)
                    ·
                      refine ⟨4278837374799929309402209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22820465998932956316811781 4278837374799929309402209)
                      ·
                        rfl

theorem cell23_8333006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_8333006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333006 prefixEnd_8333006 := by exact prefixLift 8333006
  have htrace : WordTrace (prefixWord ++ tailWord_8333006) baseStart_8333006 baseEnd_8333006 := by
    simpa [prefixWord, tailWord_8333006, baseEnd_8333006] using wordTrace_append hprefix tailTrace_8333006
  have hstable : (prefixWord ++ tailWord_8333006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333006).length < 2 ^ (prefixWord ++ tailWord_8333006).sum := by decide
  have hdescent : baseEnd_8333006 < baseStart_8333006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333023 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 3, 2, 2]
def baseStart_8333023 : Nat := 118140960795 + 8333023 * 2 ^ 59
def prefixEnd_8333023 : Nat := 4983230072969 + 3 ^ 40 * 8333023 * 2
def baseEnd_8333023 : Nat := 4278846103971055742889631

theorem tailTrace_8333023 : CollatzResearch.WordTrace tailWord_8333023 prefixEnd_8333023 4278846103971055742889631 := by
  unfold tailWord_8333023
  simp only [CollatzResearch.WordTrace]
  refine ⟨303930317689888312869395723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202620211793258875246263815 303930317689888312869395723)
  ·
    refine ⟨455895476534832469304093585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303930317689888312869395723 455895476534832469304093585)
    ·
      refine ⟨341921607401124351978070189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455895476534832469304093585 341921607401124351978070189)
      ·
        refine ⟨128220602775421631991776321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341921607401124351978070189 128220602775421631991776321)
        ·
          refine ⟨96165452081566223993832241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128220602775421631991776321 96165452081566223993832241)
          ·
            refine ⟨72124089061174667995374181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96165452081566223993832241 72124089061174667995374181)
            ·
              refine ⟨13523266698970250249132659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72124089061174667995374181 13523266698970250249132659)
              ·
                refine ⟨20284900048455375373698989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13523266698970250249132659 20284900048455375373698989)
                ·
                  refine ⟨7606837518170765765137121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20284900048455375373698989 7606837518170765765137121)
                  ·
                    refine ⟨5705128138628074323852841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606837518170765765137121 5705128138628074323852841)
                    ·
                      refine ⟨4278846103971055742889631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705128138628074323852841 4278846103971055742889631)
                      ·
                        rfl

theorem cell23_8333023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_8333023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333023 prefixEnd_8333023 := by exact prefixLift 8333023
  have htrace : WordTrace (prefixWord ++ tailWord_8333023) baseStart_8333023 baseEnd_8333023 := by
    simpa [prefixWord, tailWord_8333023, baseEnd_8333023] using wordTrace_append hprefix tailTrace_8333023
  have hstable : (prefixWord ++ tailWord_8333023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333023).length < 2 ^ (prefixWord ++ tailWord_8333023).sum := by decide
  have hdescent : baseEnd_8333023 < baseStart_8333023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333046 : List Nat := [5, 1, 1, 1, 1, 3, 4, 7]
def baseStart_8333046 : Nat := 118140960795 + 8333046 * 2 ^ 59
def prefixEnd_8333046 : Nat := 4983230072969 + 3 ^ 40 * 8333046 * 2
def baseEnd_8333046 : Nat := 158476219038004042700075

theorem tailTrace_8333046 : CollatzResearch.WordTrace tailWord_8333046 prefixEnd_8333046 158476219038004042700075 := by
  unfold tailWord_8333046
  simp only [CollatzResearch.WordTrace]
  refine ⟨18995697285550311737342687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202620771045869991864988661 18995697285550311737342687)
  ·
    refine ⟨28493545928325467606014031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18995697285550311737342687 28493545928325467606014031)
    ·
      refine ⟨42740318892488201409021047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28493545928325467606014031 42740318892488201409021047)
      ·
        refine ⟨64110478338732302113531571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42740318892488201409021047 64110478338732302113531571)
        ·
          refine ⟨96165717508098453170297357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64110478338732302113531571 96165717508098453170297357)
          ·
            refine ⟨36062144065536919938861509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96165717508098453170297357 36062144065536919938861509)
            ·
              refine ⟨6761652012288172488536533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36062144065536919938861509 6761652012288172488536533)
              ·
                refine ⟨158476219038004042700075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6761652012288172488536533 158476219038004042700075)
                ·
                  rfl

theorem cell23_8333046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_8333046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333046 prefixEnd_8333046 := by exact prefixLift 8333046
  have htrace : WordTrace (prefixWord ++ tailWord_8333046) baseStart_8333046 baseEnd_8333046 := by
    simpa [prefixWord, tailWord_8333046, baseEnd_8333046] using wordTrace_append hprefix tailTrace_8333046
  have hstable : (prefixWord ++ tailWord_8333046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333046).length < 2 ^ (prefixWord ++ tailWord_8333046).sum := by decide
  have hdescent : baseEnd_8333046 < baseStart_8333046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333100 : List Nat := [2, 2, 1, 1, 1, 7, 1, 2, 1, 3, 2]
def baseStart_8333100 : Nat := 118140960795 + 8333100 * 2 ^ 59
def prefixEnd_8333100 : Nat := 4983230072969 + 3 ^ 40 * 8333100 * 2
def baseEnd_8333100 : Nat := 4278885641981451941626777

theorem tailTrace_8333100 : CollatzResearch.WordTrace tailWord_8333100 prefixEnd_8333100 4278885641981451941626777 := by
  unfold tailWord_8333100
  simp only [CollatzResearch.WordTrace]
  refine ⟨151966563055304677509974377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202622084073739570013299169 151966563055304677509974377)
  ·
    refine ⟨113974922291478508132480783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151966563055304677509974377 113974922291478508132480783)
    ·
      refine ⟨170962383437217762198721175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113974922291478508132480783 170962383437217762198721175)
      ·
        refine ⟨256443575155826643298081763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170962383437217762198721175 256443575155826643298081763)
        ·
          refine ⟨384665362733739964947122645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256443575155826643298081763 384665362733739964947122645)
          ·
            refine ⟨9015594439072030428448187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 384665362733739964947122645 9015594439072030428448187)
            ·
              refine ⟨13523391658608045642672281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9015594439072030428448187 13523391658608045642672281)
              ·
                refine ⟨10142543743956034232004211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523391658608045642672281 10142543743956034232004211)
                ·
                  refine ⟨15213815615934051348006317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10142543743956034232004211 15213815615934051348006317)
                  ·
                    refine ⟨5705180855975269255502369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15213815615934051348006317 5705180855975269255502369)
                    ·
                      refine ⟨4278885641981451941626777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705180855975269255502369 4278885641981451941626777)
                      ·
                        rfl

theorem cell23_8333100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 3, 2].length) (baseStart_8333100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333100 prefixEnd_8333100 := by exact prefixLift 8333100
  have htrace : WordTrace (prefixWord ++ tailWord_8333100) baseStart_8333100 baseEnd_8333100 := by
    simpa [prefixWord, tailWord_8333100, baseEnd_8333100] using wordTrace_append hprefix tailTrace_8333100
  have hstable : (prefixWord ++ tailWord_8333100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333100).length < 2 ^ (prefixWord ++ tailWord_8333100).sum := by decide
  have hdescent : baseEnd_8333100 < baseStart_8333100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333117 : List Nat := [1, 4, 1, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_8333117 : Nat := 118140960795 + 8333117 * 2 ^ 59
def prefixEnd_8333117 : Nat := 4983230072969 + 3 ^ 40 * 8333117 * 2
def baseEnd_8333117 : Nat := 4278894371152578375114199

theorem tailTrace_8333117 : CollatzResearch.WordTrace tailWord_8333117 prefixEnd_8333117 4278894371152578375114199 := by
  unfold tailWord_8333117
  simp only [CollatzResearch.WordTrace]
  refine ⟨303933746151547766923317605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202622497434365177948878403 303933746151547766923317605)
  ·
    refine ⟨56987577403415206298122051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303933746151547766923317605 56987577403415206298122051)
    ·
      refine ⟨85481366105122809447183077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56987577403415206298122051 85481366105122809447183077)
      ·
        refine ⟨16027756144710526771346827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85481366105122809447183077 16027756144710526771346827)
        ·
          refine ⟨24041634217065790157020241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16027756144710526771346827 24041634217065790157020241)
          ·
            refine ⟨18031225662799342617765181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24041634217065790157020241 18031225662799342617765181)
            ·
              refine ⟨6761709623549753481661943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18031225662799342617765181 6761709623549753481661943)
              ·
                refine ⟨10142564435324630222492915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761709623549753481661943 10142564435324630222492915)
                ·
                  refine ⟨15213846652986945333739373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10142564435324630222492915 15213846652986945333739373)
                  ·
                    refine ⟨5705192494870104500152265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15213846652986945333739373 5705192494870104500152265)
                    ·
                      refine ⟨4278894371152578375114199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705192494870104500152265 4278894371152578375114199)
                      ·
                        rfl

theorem cell23_8333117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_8333117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333117 prefixEnd_8333117 := by exact prefixLift 8333117
  have htrace : WordTrace (prefixWord ++ tailWord_8333117) baseStart_8333117 baseEnd_8333117 := by
    simpa [prefixWord, tailWord_8333117, baseEnd_8333117] using wordTrace_append hprefix tailTrace_8333117
  have hstable : (prefixWord ++ tailWord_8333117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333117).length < 2 ^ (prefixWord ++ tailWord_8333117).sum := by decide
  have hdescent : baseEnd_8333117 < baseStart_8333117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333130 : List Nat := [3, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_8333130 : Nat := 118140960795 + 8333130 * 2 ^ 59
def prefixEnd_8333130 : Nat := 4983230072969 + 3 ^ 40 * 8333130 * 2
def baseEnd_8333130 : Nat := 4278901046401086824251639

theorem tailTrace_8333130 : CollatzResearch.WordTrace tailWord_8333130 prefixEnd_8333130 4278901046401086824251639 := by
  unfold tailWord_8333130
  simp only [CollatzResearch.WordTrace]
  refine ⟨75983555075125167535885211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202622813533667113429027229 75983555075125167535885211)
  ·
    refine ⟨113975332612687751303827817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75983555075125167535885211 113975332612687751303827817)
    ·
      refine ⟨85481499459515813477870863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113975332612687751303827817 85481499459515813477870863)
      ·
        refine ⟨128222249189273720216806295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85481499459515813477870863 128222249189273720216806295)
        ·
          refine ⟨192333373783910580325209443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128222249189273720216806295 192333373783910580325209443)
          ·
            refine ⟨288500060675865870487814165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192333373783910580325209443 288500060675865870487814165)
            ·
              refine ⟨13523440344181212679116289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288500060675865870487814165 13523440344181212679116289)
              ·
                refine ⟨10142580258135909509337217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13523440344181212679116289 10142580258135909509337217)
                ·
                  refine ⟨7606935193601932132002913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142580258135909509337217 7606935193601932132002913)
                  ·
                    refine ⟨5705201395201449099002185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7606935193601932132002913 5705201395201449099002185)
                    ·
                      refine ⟨4278901046401086824251639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705201395201449099002185 4278901046401086824251639)
                      ·
                        rfl

theorem cell23_8333130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_8333130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333130 prefixEnd_8333130 := by exact prefixLift 8333130
  have htrace : WordTrace (prefixWord ++ tailWord_8333130) baseStart_8333130 baseEnd_8333130 := by
    simpa [prefixWord, tailWord_8333130, baseEnd_8333130] using wordTrace_append hprefix tailTrace_8333130
  have hstable : (prefixWord ++ tailWord_8333130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333130).length < 2 ^ (prefixWord ++ tailWord_8333130).sum := by decide
  have hdescent : baseEnd_8333130 < baseStart_8333130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333133 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_8333133 : Nat := 118140960795 + 8333133 * 2 ^ 59
def prefixEnd_8333133 : Nat := 4983230072969 + 3 ^ 40 * 8333133 * 2
def baseEnd_8333133 : Nat := 4278902586843050312514125

theorem tailTrace_8333133 : CollatzResearch.WordTrace tailWord_8333133 prefixEnd_8333133 4278902586843050312514125 := by
  unfold tailWord_8333133
  simp only [CollatzResearch.WordTrace]
  refine ⟨303934329719489801655900053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202622886479659867770600035 303934329719489801655900053)
  ·
    refine ⟨14246921705601084452620315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 303934329719489801655900053 14246921705601084452620315)
    ·
      refine ⟨21370382558401626678930473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14246921705601084452620315 21370382558401626678930473)
      ·
        refine ⟨16027786918801220009197855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21370382558401626678930473 16027786918801220009197855)
        ·
          refine ⟨24041680378201830013796783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16027786918801220009197855 24041680378201830013796783)
          ·
            refine ⟨36062520567302745020695175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24041680378201830013796783 36062520567302745020695175)
            ·
              refine ⟨54093780850954117531042763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36062520567302745020695175 54093780850954117531042763)
              ·
                refine ⟨81140671276431176296564145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54093780850954117531042763 81140671276431176296564145)
                ·
                  refine ⟨60855503457323382222423109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81140671276431176296564145 60855503457323382222423109)
                  ·
                    refine ⟨11410406898248134166704333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60855503457323382222423109 11410406898248134166704333)
                    ·
                      refine ⟨4278902586843050312514125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11410406898248134166704333 4278902586843050312514125)
                      ·
                        rfl

theorem cell23_8333133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_8333133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333133 prefixEnd_8333133 := by exact prefixLift 8333133
  have htrace : WordTrace (prefixWord ++ tailWord_8333133) baseStart_8333133 baseEnd_8333133 := by
    simpa [prefixWord, tailWord_8333133, baseEnd_8333133] using wordTrace_append hprefix tailTrace_8333133
  have hstable : (prefixWord ++ tailWord_8333133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333133).length < 2 ^ (prefixWord ++ tailWord_8333133).sum := by decide
  have hdescent : baseEnd_8333133 < baseStart_8333133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333146 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3]
def baseStart_8333146 : Nat := 118140960795 + 8333146 * 2 ^ 59
def prefixEnd_8333146 : Nat := 4983230072969 + 3 ^ 40 * 8333146 * 2
def baseEnd_8333146 : Nat := 4278909262091558761651565

theorem tailTrace_8333146 : CollatzResearch.WordTrace tailWord_8333146 prefixEnd_8333146 4278909262091558761651565 := by
  unfold tailWord_8333146
  simp only [CollatzResearch.WordTrace]
  refine ⟨75983700967110676219030823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202623202578961803250748861 75983700967110676219030823)
  ·
    refine ⟨113975551450666014328546235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75983700967110676219030823 113975551450666014328546235)
    ·
      refine ⟨170963327175999021492819353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113975551450666014328546235 170963327175999021492819353)
      ·
        refine ⟨128222495381999266119614515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170963327175999021492819353 128222495381999266119614515)
        ·
          refine ⟨192333743072998899179421773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128222495381999266119614515 192333743072998899179421773)
          ·
            refine ⟨72125153652374587192283165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192333743072998899179421773 72125153652374587192283165)
            ·
              refine ⟨27046932619640470197106187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72125153652374587192283165 27046932619640470197106187)
              ·
                refine ⟨40570398929460705295659281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27046932619640470197106187 40570398929460705295659281)
                ·
                  refine ⟨30427799197095528971744461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40570398929460705295659281 30427799197095528971744461)
                  ·
                    refine ⟨11410424698910823364404173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30427799197095528971744461 11410424698910823364404173)
                    ·
                      refine ⟨4278909262091558761651565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11410424698910823364404173 4278909262091558761651565)
                      ·
                        rfl

theorem cell23_8333146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_8333146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333146 prefixEnd_8333146 := by exact prefixLift 8333146
  have htrace : WordTrace (prefixWord ++ tailWord_8333146) baseStart_8333146 baseEnd_8333146 := by
    simpa [prefixWord, tailWord_8333146, baseEnd_8333146] using wordTrace_append hprefix tailTrace_8333146
  have hstable : (prefixWord ++ tailWord_8333146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333146).length < 2 ^ (prefixWord ++ tailWord_8333146).sum := by decide
  have hdescent : baseEnd_8333146 < baseStart_8333146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333213 : List Nat := [1, 4, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_8333213 : Nat := 118140960795 + 8333213 * 2 ^ 59
def prefixEnd_8333213 : Nat := 4983230072969 + 3 ^ 40 * 8333213 * 2
def baseEnd_8333213 : Nat := 1426314555098469999837919

theorem tailTrace_8333213 : CollatzResearch.WordTrace tailWord_8333213 prefixEnd_8333213 1426314555098469999837919 := by
  unfold tailWord_8333213
  simp only [CollatzResearch.WordTrace]
  refine ⟨303937247559199975318812293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202624831706133316879208195 303937247559199975318812293)
  ·
    refine ⟨56988233917349995372277305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303937247559199975318812293 56988233917349995372277305)
    ·
      refine ⟨42741175438012496529207979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56988233917349995372277305 42741175438012496529207979)
      ·
        refine ⟨64111763157018744793811969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42741175438012496529207979 64111763157018744793811969)
        ·
          refine ⟨48083822367764058595358977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64111763157018744793811969 48083822367764058595358977)
          ·
            refine ⟨36062866775823043946519233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48083822367764058595358977 36062866775823043946519233)
            ·
              refine ⟨27047150081867282959889425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36062866775823043946519233 27047150081867282959889425)
              ·
                refine ⟨20285362561400462219917069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27047150081867282959889425 20285362561400462219917069)
                ·
                  refine ⟨7607010960525173332468901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20285362561400462219917069 7607010960525173332468901)
                  ·
                    refine ⟨1426314555098469999837919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7607010960525173332468901 1426314555098469999837919)
                    ·
                      rfl

theorem cell23_8333213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_8333213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333213 prefixEnd_8333213 := by exact prefixLift 8333213
  have htrace : WordTrace (prefixWord ++ tailWord_8333213) baseStart_8333213 baseEnd_8333213 := by
    simpa [prefixWord, tailWord_8333213, baseEnd_8333213] using wordTrace_append hprefix tailTrace_8333213
  have hstable : (prefixWord ++ tailWord_8333213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333213).length < 2 ^ (prefixWord ++ tailWord_8333213).sum := by decide
  have hdescent : baseEnd_8333213 < baseStart_8333213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333223 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_8333223 : Nat := 118140960795 + 8333223 * 2 ^ 59
def prefixEnd_8333223 : Nat := 4983230072969 + 3 ^ 40 * 8333223 * 2
def baseEnd_8333223 : Nat := 4278948800101954960388711

theorem tailTrace_8333223 : CollatzResearch.WordTrace tailWord_8333223 prefixEnd_8333223 4278948800101954960388711 := by
  unfold tailWord_8333223
  simp only [CollatzResearch.WordTrace]
  refine ⟨303937612289163747026676323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202625074859442498017784215 303937612289163747026676323)
  ·
    refine ⟨455906418433745620540014485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303937612289163747026676323 455906418433745620540014485)
    ·
      refine ⟨21370613364081825962813179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 455906418433745620540014485 21370613364081825962813179)
      ·
        refine ⟨32055920046122738944219769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21370613364081825962813179 32055920046122738944219769)
        ·
          refine ⟨24041940034592054208164827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32055920046122738944219769 24041940034592054208164827)
          ·
            refine ⟨36062910051888081312247241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24041940034592054208164827 36062910051888081312247241)
            ·
              refine ⟨27047182538916060984185431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36062910051888081312247241 27047182538916060984185431)
              ·
                refine ⟨40570773808374091476278147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27047182538916060984185431 40570773808374091476278147)
                ·
                  refine ⟨60856160712561137214417221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40570773808374091476278147 60856160712561137214417221)
                  ·
                    refine ⟨11410530133605213227703229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60856160712561137214417221 11410530133605213227703229)
                    ·
                      refine ⟨4278948800101954960388711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11410530133605213227703229 4278948800101954960388711)
                      ·
                        rfl

theorem cell23_8333223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_8333223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333223 prefixEnd_8333223 := by exact prefixLift 8333223
  have htrace : WordTrace (prefixWord ++ tailWord_8333223) baseStart_8333223 baseEnd_8333223 := by
    simpa [prefixWord, tailWord_8333223, baseEnd_8333223] using wordTrace_append hprefix tailTrace_8333223
  have hstable : (prefixWord ++ tailWord_8333223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333223).length < 2 ^ (prefixWord ++ tailWord_8333223).sum := by decide
  have hdescent : baseEnd_8333223 < baseStart_8333223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333253 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 3]
def baseStart_8333253 : Nat := 118140960795 + 8333253 * 2 ^ 59
def prefixEnd_8333253 : Nat := 4983230072969 + 3 ^ 40 * 8333253 * 2
def baseEnd_8333253 : Nat := 4278964204521589843013573

theorem tailTrace_8333253 : CollatzResearch.WordTrace tailWord_8333253 prefixEnd_8333253 4278964204521589843013573 := by
  unfold tailWord_8333253
  simp only [CollatzResearch.WordTrace]
  refine ⟨303938706479055062150268413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202625804319370041433512275 303938706479055062150268413)
  ·
    refine ⟨113977014929645648306350655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303938706479055062150268413 113977014929645648306350655)
    ·
      refine ⟨170965522394468472459525983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113977014929645648306350655 170965522394468472459525983)
      ·
        refine ⟨256448283591702708689288975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170965522394468472459525983 256448283591702708689288975)
        ·
          refine ⟨384672425387554063033933463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256448283591702708689288975 384672425387554063033933463)
          ·
            refine ⟨577008638081331094550900195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384672425387554063033933463 577008638081331094550900195)
            ·
              refine ⟨865512957121996641826350293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577008638081331094550900195 865512957121996641826350293)
              ·
                refine ⟨20285459932546796292805085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 865512957121996641826350293 20285459932546796292805085)
                ·
                  refine ⟨7607047474705048609801907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20285459932546796292805085 7607047474705048609801907)
                  ·
                    refine ⟨11410571212057572914702861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7607047474705048609801907 11410571212057572914702861)
                    ·
                      refine ⟨4278964204521589843013573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11410571212057572914702861 4278964204521589843013573)
                      ·
                        rfl

theorem cell23_8333253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 1, 3].length) (baseStart_8333253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333253 prefixEnd_8333253 := by exact prefixLift 8333253
  have htrace : WordTrace (prefixWord ++ tailWord_8333253) baseStart_8333253 baseEnd_8333253 := by
    simpa [prefixWord, tailWord_8333253, baseEnd_8333253] using wordTrace_append hprefix tailTrace_8333253
  have hstable : (prefixWord ++ tailWord_8333253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333253).length < 2 ^ (prefixWord ++ tailWord_8333253).sum := by decide
  have hdescent : baseEnd_8333253 < baseStart_8333253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333260 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 6]
def baseStart_8333260 : Nat := 118140960795 + 8333260 * 2 ^ 59
def prefixEnd_8333260 : Nat := 4983230072969 + 3 ^ 40 * 8333260 * 2
def baseEnd_8333260 : Nat := 475440866542907923958449

theorem tailTrace_8333260 : CollatzResearch.WordTrace tailWord_8333260 prefixEnd_8333260 475440866542907923958449 := by
  unfold tailWord_8333260
  simp only [CollatzResearch.WordTrace]
  refine ⟨151969480895014851172886617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202625974526686468230515489 151969480895014851172886617)
  ·
    refine ⟨113977110671261138379664963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151969480895014851172886617 113977110671261138379664963)
    ·
      refine ⟨170965666006891707569497445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113977110671261138379664963 170965666006891707569497445)
      ·
        refine ⟨32056062376292195169280771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170965666006891707569497445 32056062376292195169280771)
        ·
          refine ⟨48084093564438292753921157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32056062376292195169280771 48084093564438292753921157)
          ·
            refine ⟨9015767543332179891360217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48084093564438292753921157 9015767543332179891360217)
            ·
              refine ⟨6761825657499134918520163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9015767543332179891360217 6761825657499134918520163)
              ·
                refine ⟨10142738486248702377780245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761825657499134918520163 10142738486248702377780245)
                ·
                  refine ⟨475440866542907923958449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10142738486248702377780245 475440866542907923958449)
                  ·
                    rfl

theorem cell23_8333260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_8333260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333260 prefixEnd_8333260 := by exact prefixLift 8333260
  have htrace : WordTrace (prefixWord ++ tailWord_8333260) baseStart_8333260 baseEnd_8333260 := by
    simpa [prefixWord, tailWord_8333260, baseEnd_8333260] using wordTrace_append hprefix tailTrace_8333260
  have hstable : (prefixWord ++ tailWord_8333260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333260).length < 2 ^ (prefixWord ++ tailWord_8333260).sum := by decide
  have hdescent : baseEnd_8333260 < baseStart_8333260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333263 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 4, 3, 2]
def baseStart_8333263 : Nat := 118140960795 + 8333263 * 2 ^ 59
def prefixEnd_8333263 : Nat := 4983230072969 + 3 ^ 40 * 8333263 * 2
def baseEnd_8333263 : Nat := 4278969339328134803888527

theorem tailTrace_8333263 : CollatzResearch.WordTrace tailWord_8333263 prefixEnd_8333263 4278969339328134803888527 := by
  unfold tailWord_8333263
  simp only [CollatzResearch.WordTrace]
  refine ⟨303939071209018833858132443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202626047472679222572088295 303939071209018833858132443)
  ·
    refine ⟨455908606813528250787198665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303939071209018833858132443 455908606813528250787198665)
    ·
      refine ⟨341931455110146188090398999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455908606813528250787198665 341931455110146188090398999)
      ·
        refine ⟨512897182665219282135598499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341931455110146188090398999 512897182665219282135598499)
        ·
          refine ⟨769345773997828923203397749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512897182665219282135598499 769345773997828923203397749)
          ·
            refine ⟨72126166312296461550318539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 769345773997828923203397749 72126166312296461550318539)
            ·
              refine ⟨108189249468444692325477809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72126166312296461550318539 108189249468444692325477809)
              ·
                refine ⟨81141937101333519244108357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108189249468444692325477809 81141937101333519244108357)
                ·
                  refine ⟨15214113206500034858270317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81141937101333519244108357 15214113206500034858270317)
                  ·
                    refine ⟨5705292452437513071851369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15214113206500034858270317 5705292452437513071851369)
                    ·
                      refine ⟨4278969339328134803888527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705292452437513071851369 4278969339328134803888527)
                      ·
                        rfl

theorem cell23_8333263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 3, 2].length) (baseStart_8333263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333263 prefixEnd_8333263 := by exact prefixLift 8333263
  have htrace : WordTrace (prefixWord ++ tailWord_8333263) baseStart_8333263 baseEnd_8333263 := by
    simpa [prefixWord, tailWord_8333263, baseEnd_8333263] using wordTrace_append hprefix tailTrace_8333263
  have hstable : (prefixWord ++ tailWord_8333263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333263).length < 2 ^ (prefixWord ++ tailWord_8333263).sum := by decide
  have hdescent : baseEnd_8333263 < baseStart_8333263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333273 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 3, 5]
def baseStart_8333273 : Nat := 118140960795 + 8333273 * 2 ^ 59
def prefixEnd_8333273 : Nat := 4983230072969 + 3 ^ 40 * 8333273 * 2
def baseEnd_8333273 : Nat := 1426324824711559921587827

theorem tailTrace_8333273 : CollatzResearch.WordTrace tailWord_8333273 prefixEnd_8333273 1426324824711559921587827 := by
  unfold tailWord_8333273
  simp only [CollatzResearch.WordTrace]
  refine ⟨303939435938982605565996473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202626290625988403710664315 303939435938982605565996473)
  ·
    refine ⟨227954576954236954174497355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303939435938982605565996473 227954576954236954174497355)
    ·
      refine ⟨341931865431355431261746033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227954576954236954174497355 341931865431355431261746033)
      ·
        refine ⟨256448899073516573446309525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341931865431355431261746033 256448899073516573446309525)
        ·
          refine ⟨12021042144071089380295759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 256448899073516573446309525 12021042144071089380295759)
          ·
            refine ⟨18031563216106634070443639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12021042144071089380295759 18031563216106634070443639)
            ·
              refine ⟨27047344824159951105665459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18031563216106634070443639 27047344824159951105665459)
              ·
                refine ⟨40571017236239926658498189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27047344824159951105665459 40571017236239926658498189)
                ·
                  refine ⟨15214131463589972496936821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40571017236239926658498189 15214131463589972496936821)
                  ·
                    refine ⟨1426324824711559921587827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15214131463589972496936821 1426324824711559921587827)
                    ·
                      rfl

theorem cell23_8333273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_8333273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333273 prefixEnd_8333273 := by exact prefixLift 8333273
  have htrace : WordTrace (prefixWord ++ tailWord_8333273) baseStart_8333273 baseEnd_8333273 := by
    simpa [prefixWord, tailWord_8333273, baseEnd_8333273] using wordTrace_append hprefix tailTrace_8333273
  have hstable : (prefixWord ++ tailWord_8333273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333273).length < 2 ^ (prefixWord ++ tailWord_8333273).sum := by decide
  have hdescent : baseEnd_8333273 < baseStart_8333273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333290 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 1, 5]
def baseStart_8333290 : Nat := 118140960795 + 8333290 * 2 ^ 59
def prefixEnd_8333290 : Nat := 4983230072969 + 3 ^ 40 * 8333290 * 2
def baseEnd_8333290 : Nat := 1426327734435268732750301

theorem tailTrace_8333290 : CollatzResearch.WordTrace tailWord_8333290 prefixEnd_8333290 1426327734435268732750301 := by
  unfold tailWord_8333290
  simp only [CollatzResearch.WordTrace]
  refine ⟨75985013994980254367341331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202626703986614011646243549 75985013994980254367341331)
  ·
    refine ⟨113977520992470381551011997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75985013994980254367341331 113977520992470381551011997)
    ·
      refine ⟨42741570372176393081629499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113977520992470381551011997 42741570372176393081629499)
      ·
        refine ⟨64112355558264589622444249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42741570372176393081629499 64112355558264589622444249)
        ·
          refine ⟨48084266668698442216833187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64112355558264589622444249 48084266668698442216833187)
          ·
            refine ⟨72126400003047663325249781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48084266668698442216833187 72126400003047663325249781)
            ·
              refine ⟨6761850000285718436742167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72126400003047663325249781 6761850000285718436742167)
              ·
                refine ⟨10142775000428577655113251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6761850000285718436742167 10142775000428577655113251)
                ·
                  refine ⟨15214162500642866482669877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10142775000428577655113251 15214162500642866482669877)
                  ·
                    refine ⟨1426327734435268732750301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15214162500642866482669877 1426327734435268732750301)
                    ·
                      rfl

theorem cell23_8333290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_8333290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333290 prefixEnd_8333290 := by exact prefixLift 8333290
  have htrace : WordTrace (prefixWord ++ tailWord_8333290) baseStart_8333290 baseEnd_8333290 := by
    simpa [prefixWord, tailWord_8333290, baseEnd_8333290] using wordTrace_append hprefix tailTrace_8333290
  have hstable : (prefixWord ++ tailWord_8333290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333290).length < 2 ^ (prefixWord ++ tailWord_8333290).sum := by decide
  have hdescent : baseEnd_8333290 < baseStart_8333290 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333310 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_8333310 : Nat := 118140960795 + 8333310 * 2 ^ 59
def prefixEnd_8333310 : Nat := 4983230072969 + 3 ^ 40 * 8333310 * 2
def baseEnd_8333310 : Nat := 4278993472918896120000811

theorem tailTrace_8333310 : CollatzResearch.WordTrace tailWord_8333310 prefixEnd_8333310 4278993472918896120000811 := by
  unfold tailWord_8333310
  simp only [CollatzResearch.WordTrace]
  refine ⟨37992598179981070110636673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202627190293232373923395589 37992598179981070110636673)
  ·
    refine ⟨28494448634985802582977505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37992598179981070110636673 28494448634985802582977505)
    ·
      refine ⟨21370836476239351937233129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28494448634985802582977505 21370836476239351937233129)
      ·
        refine ⟨16028127357179513952924847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21370836476239351937233129 16028127357179513952924847)
        ·
          refine ⟨24042191035769270929387271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16028127357179513952924847 24042191035769270929387271)
          ·
            refine ⟨36063286553653906394080907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24042191035769270929387271 36063286553653906394080907)
            ·
              refine ⟨54094929830480859591121361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36063286553653906394080907 54094929830480859591121361)
              ·
                refine ⟨40571197372860644693341021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54094929830480859591121361 40571197372860644693341021)
                ·
                  refine ⟨15214199014822741760002883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40571197372860644693341021 15214199014822741760002883)
                  ·
                    refine ⟨22821298522234112640004325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15214199014822741760002883 22821298522234112640004325)
                    ·
                      refine ⟨4278993472918896120000811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22821298522234112640004325 4278993472918896120000811)
                      ·
                        rfl

theorem cell23_8333310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_8333310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333310 prefixEnd_8333310 := by exact prefixLift 8333310
  have htrace : WordTrace (prefixWord ++ tailWord_8333310) baseStart_8333310 baseEnd_8333310 := by
    simpa [prefixWord, tailWord_8333310, baseEnd_8333310] using wordTrace_append hprefix tailTrace_8333310
  have hstable : (prefixWord ++ tailWord_8333310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333310).length < 2 ^ (prefixWord ++ tailWord_8333310).sum := by decide
  have hdescent : baseEnd_8333310 < baseStart_8333310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333313 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_8333313 : Nat := 118140960795 + 8333313 * 2 ^ 59
def prefixEnd_8333313 : Nat := 4983230072969 + 3 ^ 40 * 8333313 * 2
def baseEnd_8333313 : Nat := 4278995013360859608263297

theorem tailTrace_8333313 : CollatzResearch.WordTrace tailWord_8333313 prefixEnd_8333313 4278995013360859608263297 := by
  unfold tailWord_8333313
  simp only [CollatzResearch.WordTrace]
  refine ⟨303940894858837692397452593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202627263239225128264968395 303940894858837692397452593)
  ·
    refine ⟨227955671144128269298089445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303940894858837692397452593 227955671144128269298089445)
    ·
      refine ⟨42741688339524050493391771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227955671144128269298089445 42741688339524050493391771)
      ·
        refine ⟨64112532509286075740087657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42741688339524050493391771 64112532509286075740087657)
        ·
          refine ⟨48084399381964556805065743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64112532509286075740087657 48084399381964556805065743)
          ·
            refine ⟨72126599072946835207598615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48084399381964556805065743 72126599072946835207598615)
            ·
              refine ⟨108189898609420252811397923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72126599072946835207598615 108189898609420252811397923)
              ·
                refine ⟨162284847914130379217096885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108189898609420252811397923 162284847914130379217096885)
                ·
                  refine ⟨15214204491949723051602833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 162284847914130379217096885 15214204491949723051602833)
                  ·
                    refine ⟨11410653368962292288702125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15214204491949723051602833 11410653368962292288702125)
                    ·
                      refine ⟨4278995013360859608263297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11410653368962292288702125 4278995013360859608263297)
                      ·
                        rfl

theorem cell23_8333313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_8333313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333313 prefixEnd_8333313 := by exact prefixLift 8333313
  have htrace : WordTrace (prefixWord ++ tailWord_8333313) baseStart_8333313 baseEnd_8333313 := by
    simpa [prefixWord, tailWord_8333313, baseEnd_8333313] using wordTrace_append hprefix tailTrace_8333313
  have hstable : (prefixWord ++ tailWord_8333313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333313).length < 2 ^ (prefixWord ++ tailWord_8333313).sum := by decide
  have hdescent : baseEnd_8333313 < baseStart_8333313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333323 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 4]
def baseStart_8333323 : Nat := 118140960795 + 8333323 * 2 ^ 59
def prefixEnd_8333323 : Nat := 4983230072969 + 3 ^ 40 * 8333323 * 2
def baseEnd_8333323 : Nat := 4279000148167404569138251

theorem tailTrace_8333323 : CollatzResearch.WordTrace tailWord_8333323 prefixEnd_8333323 4279000148167404569138251 := by
  unfold tailWord_8333323
  simp only [CollatzResearch.WordTrace]
  refine ⟨303941259588801464105316623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202627506392534309403544415 303941259588801464105316623)
  ·
    refine ⟨455911889383202196157974935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303941259588801464105316623 455911889383202196157974935)
    ·
      refine ⟨683867834074803294236962403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455911889383202196157974935 683867834074803294236962403)
      ·
        refine ⟨1025801751112204941355443605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683867834074803294236962403 1025801751112204941355443605)
        ·
          refine ⟨48084457083384606626036419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1025801751112204941355443605 48084457083384606626036419)
          ·
            refine ⟨72126685625076909939054629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48084457083384606626036419 72126685625076909939054629)
            ·
              refine ⟨13523753554701920613572743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72126685625076909939054629 13523753554701920613572743)
              ·
                refine ⟨20285630332052880920359115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13523753554701920613572743 20285630332052880920359115)
                ·
                  refine ⟨30428445498079321380538673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20285630332052880920359115 30428445498079321380538673)
                  ·
                    refine ⟨22821334123559491035404005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30428445498079321380538673 22821334123559491035404005)
                    ·
                      refine ⟨4279000148167404569138251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22821334123559491035404005 4279000148167404569138251)
                      ·
                        rfl

theorem cell23_8333323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 4].length) (baseStart_8333323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333323 prefixEnd_8333323 := by exact prefixLift 8333323
  have htrace : WordTrace (prefixWord ++ tailWord_8333323) baseStart_8333323 baseEnd_8333323 := by
    simpa [prefixWord, tailWord_8333323, baseEnd_8333323] using wordTrace_append hprefix tailTrace_8333323
  have hstable : (prefixWord ++ tailWord_8333323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333323).length < 2 ^ (prefixWord ++ tailWord_8333323).sum := by decide
  have hdescent : baseEnd_8333323 < baseStart_8333323 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333343 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 3]
def baseStart_8333343 : Nat := 118140960795 + 8333343 * 2 ^ 59
def prefixEnd_8333343 : Nat := 4983230072969 + 3 ^ 40 * 8333343 * 2
def baseEnd_8333343 : Nat := 4279010417780494490888159

theorem tailTrace_8333343 : CollatzResearch.WordTrace tailWord_8333343 prefixEnd_8333343 4279010417780494490888159 := by
  unfold tailWord_8333343
  simp only [CollatzResearch.WordTrace]
  refine ⟨303941989048729007521044683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202627992699152671680696455 303941989048729007521044683)
  ·
    refine ⟨455912983573093511281567025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303941989048729007521044683 455912983573093511281567025)
    ·
      refine ⟨341934737679820133461175269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455912983573093511281567025 341934737679820133461175269)
      ·
        refine ⟨64112763314966275023970363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 341934737679820133461175269 64112763314966275023970363)
        ·
          refine ⟨96169144972449412535955545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64112763314966275023970363 96169144972449412535955545)
          ·
            refine ⟨72126858729337059401966659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96169144972449412535955545 72126858729337059401966659)
            ·
              refine ⟨108190288094005589102949989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72126858729337059401966659 108190288094005589102949989)
              ·
                refine ⟨20285679017626047956803123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108190288094005589102949989 20285679017626047956803123)
                ·
                  refine ⟨30428518526439071935204685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20285679017626047956803123 30428518526439071935204685)
                  ·
                    refine ⟨11410694447414651975701757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30428518526439071935204685 11410694447414651975701757)
                    ·
                      refine ⟨4279010417780494490888159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11410694447414651975701757 4279010417780494490888159)
                      ·
                        rfl

theorem cell23_8333343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_8333343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333343 prefixEnd_8333343 := by exact prefixLift 8333343
  have htrace : WordTrace (prefixWord ++ tailWord_8333343) baseStart_8333343 baseEnd_8333343 := by
    simpa [prefixWord, tailWord_8333343, baseEnd_8333343] using wordTrace_append hprefix tailTrace_8333343
  have hstable : (prefixWord ++ tailWord_8333343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333343).length < 2 ^ (prefixWord ++ tailWord_8333343).sum := by decide
  have hdescent : baseEnd_8333343 < baseStart_8333343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333356 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_8333356 : Nat := 118140960795 + 8333356 * 2 ^ 59
def prefixEnd_8333356 : Nat := 4983230072969 + 3 ^ 40 * 8333356 * 2
def baseEnd_8333356 : Nat := 4279017093029002940025599

theorem tailTrace_8333356 : CollatzResearch.WordTrace tailWord_8333356 prefixEnd_8333356 4279017093029002940025599 := by
  unfold tailWord_8333356
  simp only [CollatzResearch.WordTrace]
  refine ⟨151971231598840955370633961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202628308798454607160845281 151971231598840955370633961)
  ·
    refine ⟨113978423699130716527975471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151971231598840955370633961 113978423699130716527975471)
    ·
      refine ⟨170967635548696074791963207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113978423699130716527975471 170967635548696074791963207)
      ·
        refine ⟨256451453323044112187944811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170967635548696074791963207 256451453323044112187944811)
        ·
          refine ⟨384677179984566168281917217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256451453323044112187944811 384677179984566168281917217)
          ·
            refine ⟨288507884988424626211437913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384677179984566168281917217 288507884988424626211437913)
            ·
              refine ⟨216380913741318469658578435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288507884988424626211437913 216380913741318469658578435)
              ·
                refine ⟨324571370611977704487867653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216380913741318469658578435 324571370611977704487867653)
                ·
                  refine ⟨60857131989745819591475185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324571370611977704487867653 60857131989745819591475185)
                  ·
                    refine ⟨45642848992309364693606389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60857131989745819591475185 45642848992309364693606389)
                    ·
                      refine ⟨4279017093029002940025599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45642848992309364693606389 4279017093029002940025599)
                      ·
                        rfl

theorem cell23_8333356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_8333356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333356 prefixEnd_8333356 := by exact prefixLift 8333356
  have htrace : WordTrace (prefixWord ++ tailWord_8333356) baseStart_8333356 baseEnd_8333356 := by
    simpa [prefixWord, tailWord_8333356, baseEnd_8333356] using wordTrace_append hprefix tailTrace_8333356
  have hstable : (prefixWord ++ tailWord_8333356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333356).length < 2 ^ (prefixWord ++ tailWord_8333356).sum := by decide
  have hdescent : baseEnd_8333356 < baseStart_8333356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333360 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 4, 1, 3]
def baseStart_8333360 : Nat := 118140960795 + 8333360 * 2 ^ 59
def prefixEnd_8333360 : Nat := 4983230072969 + 3 ^ 40 * 8333360 * 2
def baseEnd_8333360 : Nat := 4279019146951620924375581

theorem tailTrace_8333360 : CollatzResearch.WordTrace tailWord_8333360 prefixEnd_8333360 4279019146951620924375581 := by
  unfold tailWord_8333360
  simp only [CollatzResearch.WordTrace]
  refine ⟨151971304544833709712206767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202628406059778279616275689 151971304544833709712206767)
  ·
    refine ⟨227956956817250564568310151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151971304544833709712206767 227956956817250564568310151)
    ·
      refine ⟨341935435225875846852465227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227956956817250564568310151 341935435225875846852465227)
      ·
        refine ⟨512903152838813770278697841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341935435225875846852465227 512903152838813770278697841)
        ·
          refine ⟨384677364629110327709023381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512903152838813770278697841 384677364629110327709023381)
          ·
            refine ⟨18031751466989546611360471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 384677364629110327709023381 18031751466989546611360471)
            ·
              refine ⟨27047627200484319917040707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18031751466989546611360471 27047627200484319917040707)
              ·
                refine ⟨40571440800726479875561061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27047627200484319917040707 40571440800726479875561061)
                ·
                  refine ⟨7607145150136214976667699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40571440800726479875561061 7607145150136214976667699)
                  ·
                    refine ⟨11410717725204322465001549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7607145150136214976667699 11410717725204322465001549)
                    ·
                      refine ⟨4279019146951620924375581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11410717725204322465001549 4279019146951620924375581)
                      ·
                        rfl

theorem cell23_8333360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 4, 1, 3].length) (baseStart_8333360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333360 prefixEnd_8333360 := by exact prefixLift 8333360
  have htrace : WordTrace (prefixWord ++ tailWord_8333360) baseStart_8333360 baseEnd_8333360 := by
    simpa [prefixWord, tailWord_8333360, baseEnd_8333360] using wordTrace_append hprefix tailTrace_8333360
  have hstable : (prefixWord ++ tailWord_8333360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333360).length < 2 ^ (prefixWord ++ tailWord_8333360).sum := by decide
  have hdescent : baseEnd_8333360 < baseStart_8333360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333374 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_8333374 : Nat := 118140960795 + 8333374 * 2 ^ 59
def prefixEnd_8333374 : Nat := 4983230072969 + 3 ^ 40 * 8333374 * 2
def baseEnd_8333374 : Nat := 4279026335680783869600517

theorem tailTrace_8333374 : CollatzResearch.WordTrace tailWord_8333374 prefixEnd_8333374 4279026335680783869600517 := by
  unfold tailWord_8333374
  simp only [CollatzResearch.WordTrace]
  refine ⟨37992889963952087476927897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 202628746474411133210282117 37992889963952087476927897)
  ·
    refine ⟨28494667472964065607695923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37992889963952087476927897 28494667472964065607695923)
    ·
      refine ⟨42742001209446098411543885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28494667472964065607695923 42742001209446098411543885)
      ·
        refine ⟨16028250453542286904328957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42742001209446098411543885 16028250453542286904328957)
        ·
          refine ⟨6010593920078357589123359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16028250453542286904328957 6010593920078357589123359)
          ·
            refine ⟨9015890880117536383685039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010593920078357589123359 9015890880117536383685039)
            ·
              refine ⟨13523836320176304575527559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9015890880117536383685039 13523836320176304575527559)
              ·
                refine ⟨20285754480264456863291339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13523836320176304575527559 20285754480264456863291339)
                ·
                  refine ⟨30428631720396685294937009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20285754480264456863291339 30428631720396685294937009)
                  ·
                    refine ⟨22821473790297513971202757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30428631720396685294937009 22821473790297513971202757)
                    ·
                      refine ⟨4279026335680783869600517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22821473790297513971202757 4279026335680783869600517)
                      ·
                        rfl

theorem cell23_8333374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_8333374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333374 prefixEnd_8333374 := by exact prefixLift 8333374
  have htrace : WordTrace (prefixWord ++ tailWord_8333374) baseStart_8333374 baseEnd_8333374 := by
    simpa [prefixWord, tailWord_8333374, baseEnd_8333374] using wordTrace_append hprefix tailTrace_8333374
  have hstable : (prefixWord ++ tailWord_8333374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333374).length < 2 ^ (prefixWord ++ tailWord_8333374).sum := by decide
  have hdescent : baseEnd_8333374 < baseStart_8333374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333377 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_8333377 : Nat := 118140960795 + 8333377 * 2 ^ 59
def prefixEnd_8333377 : Nat := 4983230072969 + 3 ^ 40 * 8333377 * 2
def baseEnd_8333377 : Nat := 4279027876122747357863003

theorem tailTrace_8333377 : CollatzResearch.WordTrace tailWord_8333377 prefixEnd_8333377 4279027876122747357863003 := by
  unfold tailWord_8333377
  simp only [CollatzResearch.WordTrace]
  refine ⟨303943229130605831327782385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202628819420403887551854923 303943229130605831327782385)
  ·
    refine ⟨227957421847954373495836789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303943229130605831327782385 227957421847954373495836789)
    ·
      refine ⟨21371008298245722515234699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227957421847954373495836789 21371008298245722515234699)
      ·
        refine ⟨32056512447368583772852049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21371008298245722515234699 32056512447368583772852049)
        ·
          refine ⟨24042384335526437829639037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32056512447368583772852049 24042384335526437829639037)
          ·
            refine ⟨9015894125822414186114639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24042384335526437829639037 9015894125822414186114639)
            ·
              refine ⟨13523841188733621279171959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9015894125822414186114639 13523841188733621279171959)
              ·
                refine ⟨20285761783100431918757939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13523841188733621279171959 20285761783100431918757939)
                ·
                  refine ⟨30428642674650647878136909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20285761783100431918757939 30428642674650647878136909)
                  ·
                    refine ⟨11410741002993992954301341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30428642674650647878136909 11410741002993992954301341)
                    ·
                      refine ⟨4279027876122747357863003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11410741002993992954301341 4279027876122747357863003)
                      ·
                        rfl

theorem cell23_8333377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_8333377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333377 prefixEnd_8333377 := by exact prefixLift 8333377
  have htrace : WordTrace (prefixWord ++ tailWord_8333377) baseStart_8333377 baseEnd_8333377 := by
    simpa [prefixWord, tailWord_8333377, baseEnd_8333377] using wordTrace_append hprefix tailTrace_8333377
  have hstable : (prefixWord ++ tailWord_8333377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333377).length < 2 ^ (prefixWord ++ tailWord_8333377).sum := by decide
  have hdescent : baseEnd_8333377 < baseStart_8333377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333417 : List Nat := [1, 2, 1, 1, 1, 5, 2, 4, 2, 2, 2]
def baseStart_8333417 : Nat := 118140960795 + 8333417 * 2 ^ 59
def prefixEnd_8333417 : Nat := 4983230072969 + 3 ^ 40 * 8333417 * 2
def baseEnd_8333417 : Nat := 4279048415348927201362819

theorem tailTrace_8333417 : CollatzResearch.WordTrace tailWord_8333417 prefixEnd_8333417 4279048415348927201362819 := by
  unfold tailWord_8333417
  simp only [CollatzResearch.WordTrace]
  refine ⟨303944688050460918159238505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202629792033640612106159003 303944688050460918159238505)
  ·
    refine ⟨227958516037845688619428879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303944688050460918159238505 227958516037845688619428879)
    ·
      refine ⟨341937774056768532929143319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227958516037845688619428879 341937774056768532929143319)
      ·
        refine ⟨512906661085152799393714979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341937774056768532929143319 512906661085152799393714979)
        ·
          refine ⟨769359991627729199090572469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512906661085152799393714979 769359991627729199090572469)
          ·
            refine ⟨72127499215099612414741169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 769359991627729199090572469 72127499215099612414741169)
            ·
              refine ⟨54095624411324709311055877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72127499215099612414741169 54095624411324709311055877)
              ·
                refine ⟨10142929577123382995822977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54095624411324709311055877 10142929577123382995822977)
                ·
                  refine ⟨7607197182842537246867233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10142929577123382995822977 7607197182842537246867233)
                  ·
                    refine ⟨5705397887131902935150425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7607197182842537246867233 5705397887131902935150425)
                    ·
                      refine ⟨4279048415348927201362819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705397887131902935150425 4279048415348927201362819)
                      ·
                        rfl

theorem cell23_8333417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 2, 2].length) (baseStart_8333417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333417 prefixEnd_8333417 := by exact prefixLift 8333417
  have htrace : WordTrace (prefixWord ++ tailWord_8333417) baseStart_8333417 baseEnd_8333417 := by
    simpa [prefixWord, tailWord_8333417, baseEnd_8333417] using wordTrace_append hprefix tailTrace_8333417
  have hstable : (prefixWord ++ tailWord_8333417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333417).length < 2 ^ (prefixWord ++ tailWord_8333417).sum := by decide
  have hdescent : baseEnd_8333417 < baseStart_8333417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333423 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 7]
def baseStart_8333423 : Nat := 118140960795 + 8333423 * 2 ^ 59
def prefixEnd_8333423 : Nat := 4983230072969 + 3 ^ 40 * 8333423 * 2
def baseEnd_8333423 : Nat := 475450166248094908654199

theorem tailTrace_8333423 : CollatzResearch.WordTrace tailWord_8333423 prefixEnd_8333423 475450166248094908654199 := by
  unfold tailWord_8333423
  simp only [CollatzResearch.WordTrace]
  refine ⟨303944906888439181183956923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202629937925626120789304615 303944906888439181183956923)
  ·
    refine ⟨455917360332658771775935385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303944906888439181183956923 455917360332658771775935385)
    ·
      refine ⟨341938020249494078831951539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455917360332658771775935385 341938020249494078831951539)
      ·
        refine ⟨512907030374241118247927309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341938020249494078831951539 512907030374241118247927309)
        ·
          refine ⟨192340136390340419342972741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512907030374241118247927309 192340136390340419342972741)
          ·
            refine ⟨36063775573188828626807389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192340136390340419342972741 36063775573188828626807389)
            ·
              refine ⟨13523915839945810735052771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36063775573188828626807389 13523915839945810735052771)
              ·
                refine ⟨20285873759918716102579157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13523915839945810735052771 20285873759918716102579157)
                ·
                  refine ⟨475450166248094908654199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20285873759918716102579157 475450166248094908654199)
                  ·
                    rfl

theorem cell23_8333423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 7].length) (baseStart_8333423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333423 prefixEnd_8333423 := by exact prefixLift 8333423
  have htrace : WordTrace (prefixWord ++ tailWord_8333423) baseStart_8333423 baseEnd_8333423 := by
    simpa [prefixWord, tailWord_8333423, baseEnd_8333423] using wordTrace_append hprefix tailTrace_8333423
  have hstable : (prefixWord ++ tailWord_8333423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333423).length < 2 ^ (prefixWord ++ tailWord_8333423).sum := by decide
  have hdescent : baseEnd_8333423 < baseStart_8333423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333474 : List Nat := [3, 3, 1, 3, 1, 1, 4, 2, 5]
def baseStart_8333474 : Nat := 118140960795 + 8333474 * 2 ^ 59
def prefixEnd_8333474 : Nat := 4983230072969 + 3 ^ 40 * 8333474 * 2
def baseEnd_8333474 : Nat := 475453075971803719816673

theorem tailTrace_8333474 : CollatzResearch.WordTrace tailWord_8333474 prefixEnd_8333474 475453075971803719816673 := by
  unfold tailWord_8333474
  simp only [CollatzResearch.WordTrace]
  refine ⟨75986691752813604223515869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202631178007502944596042317 75986691752813604223515869)
  ·
    refine ⟨28495009407305101583818451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75986691752813604223515869 28495009407305101583818451)
    ·
      refine ⟨42742514110957652375727677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28495009407305101583818451 42742514110957652375727677)
      ·
        refine ⟨16028442791609119640897879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42742514110957652375727677 16028442791609119640897879)
        ·
          refine ⟨24042664187413679461346819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16028442791609119640897879 24042664187413679461346819)
          ·
            refine ⟨36063996281120519192020229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24042664187413679461346819 36063996281120519192020229)
            ·
              refine ⟨6761999302710097348503793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36063996281120519192020229 6761999302710097348503793)
              ·
                refine ⟨5071499477032573011377845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6761999302710097348503793 5071499477032573011377845)
                ·
                  refine ⟨475453075971803719816673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5071499477032573011377845 475453075971803719816673)
                  ·
                    rfl

theorem cell23_8333474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_8333474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333474 prefixEnd_8333474 := by exact prefixLift 8333474
  have htrace : WordTrace (prefixWord ++ tailWord_8333474) baseStart_8333474 baseEnd_8333474 := by
    simpa [prefixWord, tailWord_8333474, baseEnd_8333474] using wordTrace_append hprefix tailTrace_8333474
  have hstable : (prefixWord ++ tailWord_8333474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333474).length < 2 ^ (prefixWord ++ tailWord_8333474).sum := by decide
  have hdescent : baseEnd_8333474 < baseStart_8333474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333530 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 6]
def baseStart_8333530 : Nat := 118140960795 + 8333530 * 2 ^ 59
def prefixEnd_8333530 : Nat := 4983230072969 + 3 ^ 40 * 8333530 * 2
def baseEnd_8333530 : Nat := 475456270962542806583311

theorem tailTrace_8333530 : CollatzResearch.WordTrace tailWord_8333530 prefixEnd_8333530 475456270962542806583311 := by
  unfold tailWord_8333530
  simp only [CollatzResearch.WordTrace]
  refine ⟨75987202374762884614525511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202632539666034358972068029 75987202374762884614525511)
  ·
    refine ⟨113980803562144326921788267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75987202374762884614525511 113980803562144326921788267)
    ·
      refine ⟨170971205343216490382682401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113980803562144326921788267 170971205343216490382682401)
      ·
        refine ⟨128228404007412367787011801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170971205343216490382682401 128228404007412367787011801)
        ·
          refine ⟨96171303005559275840258851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128228404007412367787011801 96171303005559275840258851)
          ·
            refine ⟨144256954508338913760388277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96171303005559275840258851 144256954508338913760388277)
            ·
              refine ⟨13524089485156773165036401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 144256954508338913760388277 13524089485156773165036401)
              ·
                refine ⟨10143067113867579873777301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13524089485156773165036401 10143067113867579873777301)
                ·
                  refine ⟨475456270962542806583311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10143067113867579873777301 475456270962542806583311)
                  ·
                    rfl

theorem cell23_8333530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_8333530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333530 prefixEnd_8333530 := by exact prefixLift 8333530
  have htrace : WordTrace (prefixWord ++ tailWord_8333530) baseStart_8333530 baseEnd_8333530 := by
    simpa [prefixWord, tailWord_8333530, baseEnd_8333530] using wordTrace_append hprefix tailTrace_8333530
  have hstable : (prefixWord ++ tailWord_8333530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333530).length < 2 ^ (prefixWord ++ tailWord_8333530).sum := by decide
  have hdescent : baseEnd_8333530 < baseStart_8333530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333553 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_8333553 : Nat := 118140960795 + 8333553 * 2 ^ 59
def prefixEnd_8333553 : Nat := 4983230072969 + 3 ^ 40 * 8333553 * 2
def baseEnd_8333553 : Nat := 4279118248717938669262193

theorem tailTrace_8333553 : CollatzResearch.WordTrace tailWord_8333553 prefixEnd_8333553 4279118248717938669262193 := by
  unfold tailWord_8333553
  simp only [CollatzResearch.WordTrace]
  refine ⟨303949648377968213386189313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202633098918645475590792875 303949648377968213386189313)
  ·
    refine ⟨227962236283476160039641985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303949648377968213386189313 227962236283476160039641985)
    ·
      refine ⟨170971677212607120029731489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227962236283476160039641985 170971677212607120029731489)
      ·
        refine ⟨128228757909455340022298617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170971677212607120029731489 128228757909455340022298617)
        ·
          refine ⟨96171568432091505016723963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128228757909455340022298617 96171568432091505016723963)
          ·
            refine ⟨144257352648137257525085945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96171568432091505016723963 144257352648137257525085945)
            ·
              refine ⟨108193014486102943143814459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 144257352648137257525085945 108193014486102943143814459)
              ·
                refine ⟨162289521729154414715721689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108193014486102943143814459 162289521729154414715721689)
                ·
                  refine ⟨121717141296865811036791267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162289521729154414715721689 121717141296865811036791267)
                  ·
                    refine ⟨182575711945298716555186901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121717141296865811036791267 182575711945298716555186901)
                    ·
                      refine ⟨4279118248717938669262193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 182575711945298716555186901 4279118248717938669262193)
                      ·
                        rfl

theorem cell23_8333553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_8333553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333553 prefixEnd_8333553 := by exact prefixLift 8333553
  have htrace : WordTrace (prefixWord ++ tailWord_8333553) baseStart_8333553 baseEnd_8333553 := by
    simpa [prefixWord, tailWord_8333553, baseEnd_8333553] using wordTrace_append hprefix tailTrace_8333553
  have hstable : (prefixWord ++ tailWord_8333553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333553).length < 2 ^ (prefixWord ++ tailWord_8333553).sum := by decide
  have hdescent : baseEnd_8333553 < baseStart_8333553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333563 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4]
def baseStart_8333563 : Nat := 118140960795 + 8333563 * 2 ^ 59
def prefixEnd_8333563 : Nat := 4983230072969 + 3 ^ 40 * 8333563 * 2
def baseEnd_8333563 : Nat := 4279123383524483630137147

theorem tailTrace_8333563 : CollatzResearch.WordTrace tailWord_8333563 prefixEnd_8333563 4279123383524483630137147 := by
  unfold tailWord_8333563
  simp only [CollatzResearch.WordTrace]
  refine ⟨303950013107931985094053343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202633342071954656729368895 303950013107931985094053343)
  ·
    refine ⟨455925019661897977641080015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303950013107931985094053343 455925019661897977641080015)
    ·
      refine ⟨683887529492846966461620023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455925019661897977641080015 683887529492846966461620023)
      ·
        refine ⟨1025831294239270449692430035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683887529492846966461620023 1025831294239270449692430035)
        ·
          refine ⟨1538746941358905674538645053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025831294239270449692430035 1538746941358905674538645053)
          ·
            refine ⟨577030103009589627951991895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1538746941358905674538645053 577030103009589627951991895)
            ·
              refine ⟨865545154514384441927987843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577030103009589627951991895 865545154514384441927987843)
              ·
                refine ⟨1298317731771576662891981765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 865545154514384441927987843 1298317731771576662891981765)
                ·
                  refine ⟨243434574707170624292246581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1298317731771576662891981765 243434574707170624292246581)
                  ·
                    refine ⟨22821991378797246027398117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 243434574707170624292246581 22821991378797246027398117)
                    ·
                      refine ⟨4279123383524483630137147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22821991378797246027398117 4279123383524483630137147)
                      ·
                        rfl

theorem cell23_8333563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_8333563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333563 prefixEnd_8333563 := by exact prefixLift 8333563
  have htrace : WordTrace (prefixWord ++ tailWord_8333563) baseStart_8333563 baseEnd_8333563 := by
    simpa [prefixWord, tailWord_8333563, baseEnd_8333563] using wordTrace_append hprefix tailTrace_8333563
  have hstable : (prefixWord ++ tailWord_8333563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333563).length < 2 ^ (prefixWord ++ tailWord_8333563).sum := by decide
  have hdescent : baseEnd_8333563 < baseStart_8333563 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333567 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 2, 3, 2]
def baseStart_8333567 : Nat := 118140960795 + 8333567 * 2 ^ 59
def prefixEnd_8333567 : Nat := 4983230072969 + 3 ^ 40 * 8333567 * 2
def baseEnd_8333567 : Nat := 4279125437447101614487129

theorem tailTrace_8333567 : CollatzResearch.WordTrace tailWord_8333567 prefixEnd_8333567 4279125437447101614487129 := by
  unfold tailWord_8333567
  simp only [CollatzResearch.WordTrace]
  refine ⟨303950158999917493777198955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202633439333278329184799303 303950158999917493777198955)
  ·
    refine ⟨455925238499876240665798433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303950158999917493777198955 455925238499876240665798433)
    ·
      refine ⟨341943928874907180499348825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455925238499876240665798433 341943928874907180499348825)
      ·
        refine ⟨256457946656180385374511619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341943928874907180499348825 256457946656180385374511619)
        ·
          refine ⟨384686919984270578061767429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256457946656180385374511619 384686919984270578061767429)
          ·
            refine ⟨72128797497050733386581393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 384686919984270578061767429 72128797497050733386581393)
            ·
              refine ⟨54096598122788050039936045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72128797497050733386581393 54096598122788050039936045)
              ·
                refine ⟨20286224296045518764976017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54096598122788050039936045 20286224296045518764976017)
                ·
                  refine ⟨15214668222034139073732013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20286224296045518764976017 15214668222034139073732013)
                  ·
                    refine ⟨5705500583262802152649505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15214668222034139073732013 5705500583262802152649505)
                    ·
                      refine ⟨4279125437447101614487129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705500583262802152649505 4279125437447101614487129)
                      ·
                        rfl

theorem cell23_8333567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 3, 2].length) (baseStart_8333567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333567 prefixEnd_8333567 := by exact prefixLift 8333567
  have htrace : WordTrace (prefixWord ++ tailWord_8333567) baseStart_8333567 baseEnd_8333567 := by
    simpa [prefixWord, tailWord_8333567, baseEnd_8333567] using wordTrace_append hprefix tailTrace_8333567
  have hstable : (prefixWord ++ tailWord_8333567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333567).length < 2 ^ (prefixWord ++ tailWord_8333567).sum := by decide
  have hdescent : baseEnd_8333567 < baseStart_8333567 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333631 : List Nat := [1, 1, 2, 2, 4, 1, 2, 5, 1, 2, 2]
def baseStart_8333631 : Nat := 118140960795 + 8333631 * 2 ^ 59
def prefixEnd_8333631 : Nat := 4983230072969 + 3 ^ 40 * 8333631 * 2
def baseEnd_8333631 : Nat := 4279158300208989364086835

theorem tailTrace_8333631 : CollatzResearch.WordTrace tailWord_8333631 prefixEnd_8333631 4279158300208989364086835 := by
  unfold tailWord_8333631
  simp only [CollatzResearch.WordTrace]
  refine ⟨303952493271685632707528747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202634995514457088471685831 303952493271685632707528747)
  ·
    refine ⟨455928739907528449061293121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303952493271685632707528747 455928739907528449061293121)
    ·
      refine ⟨341946554930646336795969841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 455928739907528449061293121 341946554930646336795969841)
      ·
        refine ⟨256459916197984752596977381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341946554930646336795969841 256459916197984752596977381)
        ·
          refine ⟨48086234287122141111933259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 256459916197984752596977381 48086234287122141111933259)
          ·
            refine ⟨72129351430683211667899889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48086234287122141111933259 72129351430683211667899889)
            ·
              refine ⟨54097013573012408750924917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72129351430683211667899889 54097013573012408750924917)
              ·
                refine ⟨5071595022469913320399211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54097013573012408750924917 5071595022469913320399211)
                ·
                  refine ⟨7607392533704869980598817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071595022469913320399211 7607392533704869980598817)
                  ·
                    refine ⟨5705544400278652485449113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7607392533704869980598817 5705544400278652485449113)
                    ·
                      refine ⟨4279158300208989364086835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705544400278652485449113 4279158300208989364086835)
                      ·
                        rfl

theorem cell23_8333631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 5, 1, 2, 2].length) (baseStart_8333631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333631 prefixEnd_8333631 := by exact prefixLift 8333631
  have htrace : WordTrace (prefixWord ++ tailWord_8333631) baseStart_8333631 baseEnd_8333631 := by
    simpa [prefixWord, tailWord_8333631, baseEnd_8333631] using wordTrace_append hprefix tailTrace_8333631
  have hstable : (prefixWord ++ tailWord_8333631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333631).length < 2 ^ (prefixWord ++ tailWord_8333631).sum := by decide
  have hdescent : baseEnd_8333631 < baseStart_8333631 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333648 : List Nat := [2, 1, 1, 1, 1, 6, 4, 2, 1, 2, 2]
def baseStart_8333648 : Nat := 118140960795 + 8333648 * 2 ^ 59
def prefixEnd_8333648 : Nat := 4983230072969 + 3 ^ 40 * 8333648 * 2
def baseEnd_8333648 : Nat := 4279167029380115797574257

theorem tailTrace_8333648 : CollatzResearch.WordTrace tailWord_8333648 prefixEnd_8333648 4279167029380115797574257 := by
  unfold tailWord_8333648
  simp only [CollatzResearch.WordTrace]
  refine ⟨151976556656312022305448799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202635408875082696407265065 151976556656312022305448799)
  ·
    refine ⟨227964834984468033458173199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151976556656312022305448799 227964834984468033458173199)
    ·
      refine ⟨341947252476702050187259799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227964834984468033458173199 341947252476702050187259799)
      ·
        refine ⟨512920878715053075280889699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341947252476702050187259799 512920878715053075280889699)
        ·
          refine ⟨769381318072579612921334549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512920878715053075280889699 769381318072579612921334549)
          ·
            refine ⟨36064749284652169355687557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 769381318072579612921334549 36064749284652169355687557)
            ·
              refine ⟨6762140490872281754191417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36064749284652169355687557 6762140490872281754191417)
              ·
                refine ⟨5071605368154211315643563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6762140490872281754191417 5071605368154211315643563)
                ·
                  refine ⟨7607408052231316973465345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071605368154211315643563 7607408052231316973465345)
                  ·
                    refine ⟨5705556039173487730099009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7607408052231316973465345 5705556039173487730099009)
                    ·
                      refine ⟨4279167029380115797574257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705556039173487730099009 4279167029380115797574257)
                      ·
                        rfl

theorem cell23_8333648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2, 1, 2, 2].length) (baseStart_8333648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333648 prefixEnd_8333648 := by exact prefixLift 8333648
  have htrace : WordTrace (prefixWord ++ tailWord_8333648) baseStart_8333648 baseEnd_8333648 := by
    simpa [prefixWord, tailWord_8333648, baseEnd_8333648] using wordTrace_append hprefix tailTrace_8333648
  have hstable : (prefixWord ++ tailWord_8333648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333648).length < 2 ^ (prefixWord ++ tailWord_8333648).sum := by decide
  have hdescent : baseEnd_8333648 < baseStart_8333648 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333650 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 2, 7]
def baseStart_8333650 : Nat := 118140960795 + 8333650 * 2 ^ 59
def prefixEnd_8333650 : Nat := 4983230072969 + 3 ^ 40 * 8333650 * 2
def baseEnd_8333650 : Nat := 1426389352113808263249749

theorem tailTrace_8333650 : CollatzResearch.WordTrace tailWord_8333650 prefixEnd_8333650 1426389352113808263249749 := by
  unfold tailWord_8333650
  simp only [CollatzResearch.WordTrace]
  refine ⟨75988296564654199738117601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202635457505744532634980269 75988296564654199738117601)
  ·
    refine ⟨56991222423490649803588201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75988296564654199738117601 56991222423490649803588201)
    ·
      refine ⟨42743416817617987352691151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56991222423490649803588201 42743416817617987352691151)
      ·
        refine ⟨64115125226426981029036727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42743416817617987352691151 64115125226426981029036727)
        ·
          refine ⟨96172687839640471543555091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64115125226426981029036727 96172687839640471543555091)
          ·
            refine ⟨144259031759460707315332637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96172687839640471543555091 144259031759460707315332637)
            ·
              refine ⟨54097136909797765243249739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144259031759460707315332637 54097136909797765243249739)
              ·
                refine ⟨81145705364696647864874609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54097136909797765243249739 81145705364696647864874609)
                ·
                  refine ⟨60859279023522485898655957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81145705364696647864874609 60859279023522485898655957)
                  ·
                    refine ⟨1426389352113808263249749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60859279023522485898655957 1426389352113808263249749)
                    ·
                      rfl

theorem cell23_8333650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_8333650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333650 prefixEnd_8333650 := by exact prefixLift 8333650
  have htrace : WordTrace (prefixWord ++ tailWord_8333650) baseStart_8333650 baseEnd_8333650 := by
    simpa [prefixWord, tailWord_8333650, baseEnd_8333650] using wordTrace_append hprefix tailTrace_8333650
  have hstable : (prefixWord ++ tailWord_8333650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333650).length < 2 ^ (prefixWord ++ tailWord_8333650).sum := by decide
  have hdescent : baseEnd_8333650 < baseStart_8333650 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333664 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3]
def baseStart_8333664 : Nat := 118140960795 + 8333664 * 2 ^ 59
def prefixEnd_8333664 : Nat := 4983230072969 + 3 ^ 40 * 8333664 * 2
def baseEnd_8333664 : Nat := 4279175245070587734974183

theorem tailTrace_8333664 : CollatzResearch.WordTrace tailWord_8333664 prefixEnd_8333664 4279175245070587734974183 := by
  unfold tailWord_8333664
  simp only [CollatzResearch.WordTrace]
  refine ⟨151976848440283039671740023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202635797920377386228986697 151976848440283039671740023)
  ·
    refine ⟨227965272660424559507610035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151976848440283039671740023 227965272660424559507610035)
    ·
      refine ⟨341947908990636839261415053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227965272660424559507610035 341947908990636839261415053)
      ·
        refine ⟨128230465871488814723030645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341947908990636839261415053 128230465871488814723030645)
        ·
          refine ⟨12021606175452076380284123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 128230465871488814723030645 12021606175452076380284123)
          ·
            refine ⟨18032409263178114570426185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12021606175452076380284123 18032409263178114570426185)
            ·
              refine ⟨13524306947383585927819639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18032409263178114570426185 13524306947383585927819639)
              ·
                refine ⟨20286460421075378891729459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13524306947383585927819639 20286460421075378891729459)
                ·
                  refine ⟨30429690631613068337594189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20286460421075378891729459 30429690631613068337594189)
                  ·
                    refine ⟨11411133986854900626597821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30429690631613068337594189 11411133986854900626597821)
                    ·
                      refine ⟨4279175245070587734974183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11411133986854900626597821 4279175245070587734974183)
                      ·
                        rfl

theorem cell23_8333664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_8333664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333664 prefixEnd_8333664 := by exact prefixLift 8333664
  have htrace : WordTrace (prefixWord ++ tailWord_8333664) baseStart_8333664 baseEnd_8333664 := by
    simpa [prefixWord, tailWord_8333664, baseEnd_8333664] using wordTrace_append hprefix tailTrace_8333664
  have hstable : (prefixWord ++ tailWord_8333664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333664).length < 2 ^ (prefixWord ++ tailWord_8333664).sum := by decide
  have hdescent : baseEnd_8333664 < baseStart_8333664 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333687 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 3, 4, 2]
def baseStart_8333687 : Nat := 118140960795 + 8333687 * 2 ^ 59
def prefixEnd_8333687 : Nat := 4983230072969 + 3 ^ 40 * 8333687 * 2
def baseEnd_8333687 : Nat := 4279187055125641144986577

theorem tailTrace_8333687 : CollatzResearch.WordTrace tailWord_8333687 prefixEnd_8333687 4279187055125641144986577 := by
  unfold tailWord_8333687
  simp only [CollatzResearch.WordTrace]
  refine ⟨303954535759482754271567315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202636357172988502847711543 303954535759482754271567315)
  ·
    refine ⟨455931803639224131407350973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303954535759482754271567315 455931803639224131407350973)
    ·
      refine ⟨170974426364709049277756615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455931803639224131407350973 170974426364709049277756615)
      ·
        refine ⟨256461639547063573916634923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170974426364709049277756615 256461639547063573916634923)
        ·
          refine ⟨384692459320595360874952385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256461639547063573916634923 384692459320595360874952385)
          ·
            refine ⟨288519344490446520656214289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384692459320595360874952385 288519344490446520656214289)
            ·
              refine ⟨216389508367834890492160717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288519344490446520656214289 216389508367834890492160717)
              ·
                refine ⟨81146065637938083934560269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 216389508367834890492160717 81146065637938083934560269)
                ·
                  refine ⟨30429774614226781475460101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81146065637938083934560269 30429774614226781475460101)
                  ·
                    refine ⟨5705582740167521526648769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30429774614226781475460101 5705582740167521526648769)
                    ·
                      refine ⟨4279187055125641144986577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705582740167521526648769 4279187055125641144986577)
                      ·
                        rfl

theorem cell23_8333687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 4, 2].length) (baseStart_8333687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333687 prefixEnd_8333687 := by exact prefixLift 8333687
  have htrace : WordTrace (prefixWord ++ tailWord_8333687) baseStart_8333687 baseEnd_8333687 := by
    simpa [prefixWord, tailWord_8333687, baseEnd_8333687] using wordTrace_append hprefix tailTrace_8333687
  have hstable : (prefixWord ++ tailWord_8333687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333687).length < 2 ^ (prefixWord ++ tailWord_8333687).sum := by decide
  have hdescent : baseEnd_8333687 < baseStart_8333687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333691 : List Nat := [1, 1, 1, 1, 1, 7, 4, 1, 1, 3, 2]
def baseStart_8333691 : Nat := 118140960795 + 8333691 * 2 ^ 59
def prefixEnd_8333691 : Nat := 4983230072969 + 3 ^ 40 * 8333691 * 2
def baseEnd_8333691 : Nat := 4279189109048259129336559

theorem tailTrace_8333691 : CollatzResearch.WordTrace tailWord_8333691 prefixEnd_8333691 4279189109048259129336559 := by
  unfold tailWord_8333691
  simp only [CollatzResearch.WordTrace]
  refine ⟨303954681651468262954712927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202636454434312175303141951 303954681651468262954712927)
  ·
    refine ⟨455932022477202394432069391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303954681651468262954712927 455932022477202394432069391)
    ·
      refine ⟨683898033715803591648104087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455932022477202394432069391 683898033715803591648104087)
      ·
        refine ⟨1025847050573705387472156131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 683898033715803591648104087 1025847050573705387472156131)
        ·
          refine ⟨1538770575860558081208234197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025847050573705387472156131 1538770575860558081208234197)
          ·
            refine ⟨36064935371731830028317989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1538770575860558081208234197 36064935371731830028317989)
            ·
              refine ⟨6762175382199718130309623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36064935371731830028317989 6762175382199718130309623)
              ·
                refine ⟨10143263073299577195464435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762175382199718130309623 10143263073299577195464435)
                ·
                  refine ⟨15214894609949365793196653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10143263073299577195464435 15214894609949365793196653)
                  ·
                    refine ⟨5705585478731012172448745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15214894609949365793196653 5705585478731012172448745)
                    ·
                      refine ⟨4279189109048259129336559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705585478731012172448745 4279189109048259129336559)
                      ·
                        rfl

theorem cell23_8333691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 1, 1, 3, 2].length) (baseStart_8333691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333691 prefixEnd_8333691 := by exact prefixLift 8333691
  have htrace : WordTrace (prefixWord ++ tailWord_8333691) baseStart_8333691 baseEnd_8333691 := by
    simpa [prefixWord, tailWord_8333691, baseEnd_8333691] using wordTrace_append hprefix tailTrace_8333691
  have hstable : (prefixWord ++ tailWord_8333691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333691).length < 2 ^ (prefixWord ++ tailWord_8333691).sum := by decide
  have hdescent : baseEnd_8333691 < baseStart_8333691 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333697 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 2, 6]
def baseStart_8333697 : Nat := 118140960795 + 8333697 * 2 ^ 59
def prefixEnd_8333697 : Nat := 4983230072969 + 3 ^ 40 * 8333697 * 2
def baseEnd_8333697 : Nat := 1426397396644062035287177

theorem tailTrace_8333697 : CollatzResearch.WordTrace tailWord_8333697 prefixEnd_8333697 1426397396644062035287177 := by
  unfold tailWord_8333697
  simp only [CollatzResearch.WordTrace]
  refine ⟨303954900489446525979431345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202636600326297683986287563 303954900489446525979431345)
  ·
    refine ⟨227966175367084894484573509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303954900489446525979431345 227966175367084894484573509)
    ·
      refine ⟨42743657881328417715857533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227966175367084894484573509 42743657881328417715857533)
      ·
        refine ⟨16028871705498156643446575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42743657881328417715857533 16028871705498156643446575)
        ·
          refine ⟨24043307558247234965169863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16028871705498156643446575 24043307558247234965169863)
          ·
            refine ⟨36064961337370852447754795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24043307558247234965169863 36064961337370852447754795)
            ·
              refine ⟨54097442006056278671632193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36064961337370852447754795 54097442006056278671632193)
              ·
                refine ⟨40573081504542209003724145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54097442006056278671632193 40573081504542209003724145)
                ·
                  refine ⟨30429811128406656752793109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40573081504542209003724145 30429811128406656752793109)
                  ·
                    refine ⟨1426397396644062035287177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30429811128406656752793109 1426397396644062035287177)
                    ·
                      rfl

theorem cell23_8333697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_8333697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333697 prefixEnd_8333697 := by exact prefixLift 8333697
  have htrace : WordTrace (prefixWord ++ tailWord_8333697) baseStart_8333697 baseEnd_8333697 := by
    simpa [prefixWord, tailWord_8333697, baseEnd_8333697] using wordTrace_append hprefix tailTrace_8333697
  have hstable : (prefixWord ++ tailWord_8333697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333697).length < 2 ^ (prefixWord ++ tailWord_8333697).sum := by decide
  have hdescent : baseEnd_8333697 < baseStart_8333697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333698 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_8333698 : Nat := 118140960795 + 8333698 * 2 ^ 59
def prefixEnd_8333698 : Nat := 4983230072969 + 3 ^ 40 * 8333698 * 2
def baseEnd_8333698 : Nat := 4279192703412840601949027

theorem tailTrace_8333698 : CollatzResearch.WordTrace tailWord_8333698 prefixEnd_8333698 4279192703412840601949027 := by
  unfold tailWord_8333698
  simp only [CollatzResearch.WordTrace]
  refine ⟨75988734240610725787554437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 202636624641628602100145165 75988734240610725787554437)
  ·
    refine ⟨14247887670114511085166457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75988734240610725787554437 14247887670114511085166457)
    ·
      refine ⟨10685915752585883313874843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14247887670114511085166457 10685915752585883313874843)
      ·
        refine ⟨16028873628878824970812265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10685915752585883313874843 16028873628878824970812265)
        ·
          refine ⟨12021655221659118728109199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16028873628878824970812265 12021655221659118728109199)
          ·
            refine ⟨18032482832488678092163799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12021655221659118728109199 18032482832488678092163799)
            ·
              refine ⟨27048724248733017138245699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18032482832488678092163799 27048724248733017138245699)
              ·
                refine ⟨40573086373099525707368549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27048724248733017138245699 40573086373099525707368549)
                ·
                  refine ⟨7607453694956161070131603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40573086373099525707368549 7607453694956161070131603)
                  ·
                    refine ⟨11411180542434241605197405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7607453694956161070131603 11411180542434241605197405)
                    ·
                      refine ⟨4279192703412840601949027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11411180542434241605197405 4279192703412840601949027)
                      ·
                        rfl

theorem cell23_8333698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_8333698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333698 prefixEnd_8333698 := by exact prefixLift 8333698
  have htrace : WordTrace (prefixWord ++ tailWord_8333698) baseStart_8333698 baseEnd_8333698 := by
    simpa [prefixWord, tailWord_8333698, baseEnd_8333698] using wordTrace_append hprefix tailTrace_8333698
  have hstable : (prefixWord ++ tailWord_8333698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333698).length < 2 ^ (prefixWord ++ tailWord_8333698).sum := by decide
  have hdescent : baseEnd_8333698 < baseStart_8333698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333747 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 7, 2]
def baseStart_8333747 : Nat := 118140960795 + 8333747 * 2 ^ 59
def prefixEnd_8333747 : Nat := 4983230072969 + 3 ^ 40 * 8333747 * 2
def baseEnd_8333747 : Nat := 4279217863964910910236301

theorem tailTrace_8333747 : CollatzResearch.WordTrace tailWord_8333747 prefixEnd_8333747 4279217863964910910236301 := by
  unfold tailWord_8333747
  simp only [CollatzResearch.WordTrace]
  refine ⟨303956724139265384518751495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202637816092843589679167663 303956724139265384518751495)
  ·
    refine ⟨455935086208898076778127243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303956724139265384518751495 455935086208898076778127243)
    ·
      refine ⟨683902629313347115167190865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 455935086208898076778127243 683902629313347115167190865)
      ·
        refine ⟨512926971985010336375393149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683902629313347115167190865 512926971985010336375393149)
        ·
          refine ⟨192347614494378876140772431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512926971985010336375393149 192347614494378876140772431)
          ·
            refine ⟨288521421741568314211158647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192347614494378876140772431 288521421741568314211158647)
            ·
              refine ⟨432782132612352471316737971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288521421741568314211158647 432782132612352471316737971)
              ·
                refine ⟨649173198918528706975106957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432782132612352471316737971 649173198918528706975106957)
                ·
                  refine ⟨243439949594448265115665109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 649173198918528706975106957 243439949594448265115665109)
                  ·
                    refine ⟨5705623818619881213648401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 243439949594448265115665109 5705623818619881213648401)
                    ·
                      refine ⟨4279217863964910910236301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705623818619881213648401 4279217863964910910236301)
                      ·
                        rfl

theorem cell23_8333747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 7, 2].length) (baseStart_8333747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333747 prefixEnd_8333747 := by exact prefixLift 8333747
  have htrace : WordTrace (prefixWord ++ tailWord_8333747) baseStart_8333747 baseEnd_8333747 := by
    simpa [prefixWord, tailWord_8333747, baseEnd_8333747] using wordTrace_append hprefix tailTrace_8333747
  have hstable : (prefixWord ++ tailWord_8333747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333747).length < 2 ^ (prefixWord ++ tailWord_8333747).sum := by decide
  have hdescent : baseEnd_8333747 < baseStart_8333747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333757 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_8333757 : Nat := 118140960795 + 8333757 * 2 ^ 59
def prefixEnd_8333757 : Nat := 4983230072969 + 3 ^ 40 * 8333757 * 2
def baseEnd_8333757 : Nat := 1426407666257151957037085

theorem tailTrace_8333757 : CollatzResearch.WordTrace tailWord_8333757 prefixEnd_8333757 1426407666257151957037085 := by
  unfold tailWord_8333757
  simp only [CollatzResearch.WordTrace]
  refine ⟨303957088869229156226615525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202638059246152770817743683 303957088869229156226615525)
  ·
    refine ⟨56991954162980466792490411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303957088869229156226615525 56991954162980466792490411)
    ·
      refine ⟨85487931244470700188735617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56991954162980466792490411 85487931244470700188735617)
      ·
        refine ⟨64115948433353025141551713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85487931244470700188735617 64115948433353025141551713)
        ·
          refine ⟨48086961325014768856163785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64115948433353025141551713 48086961325014768856163785)
          ·
            refine ⟨36065220993761076642122839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48086961325014768856163785 36065220993761076642122839)
            ·
              refine ⟨54097831490641614963184259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36065220993761076642122839 54097831490641614963184259)
              ·
                refine ⟨81146747235962422444776389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54097831490641614963184259 81146747235962422444776389)
                ·
                  refine ⟨15215015106742954208395573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81146747235962422444776389 15215015106742954208395573)
                  ·
                    refine ⟨1426407666257151957037085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15215015106742954208395573 1426407666257151957037085)
                    ·
                      rfl

theorem cell23_8333757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_8333757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333757 prefixEnd_8333757 := by exact prefixLift 8333757
  have htrace : WordTrace (prefixWord ++ tailWord_8333757) baseStart_8333757 baseEnd_8333757 := by
    simpa [prefixWord, tailWord_8333757, baseEnd_8333757] using wordTrace_append hprefix tailTrace_8333757
  have hstable : (prefixWord ++ tailWord_8333757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333757).length < 2 ^ (prefixWord ++ tailWord_8333757).sum := by decide
  have hdescent : baseEnd_8333757 < baseStart_8333757 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333767 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_8333767 : Nat := 118140960795 + 8333767 * 2 ^ 59
def prefixEnd_8333767 : Nat := 4983230072969 + 3 ^ 40 * 8333767 * 2
def baseEnd_8333767 : Nat := 4279228133578000831986209

theorem tailTrace_8333767 : CollatzResearch.WordTrace tailWord_8333767 prefixEnd_8333767 4279228133578000831986209 := by
  unfold tailWord_8333767
  simp only [CollatzResearch.WordTrace]
  refine ⟨303957453599192927934479555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202638302399461951956319703 303957453599192927934479555)
  ·
    refine ⟨455936180398789391901719333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 303957453599192927934479555 455936180398789391901719333)
    ·
      refine ⟨85488033824773010981572375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 455936180398789391901719333 85488033824773010981572375)
      ·
        refine ⟨128232050737159516472358563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85488033824773010981572375 128232050737159516472358563)
        ·
          refine ⟨192348076105739274708537845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128232050737159516472358563 192348076105739274708537845)
          ·
            refine ⟨18032632134913057003925423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 192348076105739274708537845 18032632134913057003925423)
            ·
              refine ⟨27048948202369585505888135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18032632134913057003925423 27048948202369585505888135)
              ·
                refine ⟨40573422303554378258832203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27048948202369585505888135 40573422303554378258832203)
                ·
                  refine ⟨60860133455331567388248305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40573422303554378258832203 60860133455331567388248305)
                  ·
                    refine ⟨45645100091498675541186229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60860133455331567388248305 45645100091498675541186229)
                    ·
                      refine ⟨4279228133578000831986209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45645100091498675541186229 4279228133578000831986209)
                      ·
                        rfl

theorem cell23_8333767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_8333767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333767 prefixEnd_8333767 := by exact prefixLift 8333767
  have htrace : WordTrace (prefixWord ++ tailWord_8333767) baseStart_8333767 baseEnd_8333767 := by
    simpa [prefixWord, tailWord_8333767, baseEnd_8333767] using wordTrace_append hprefix tailTrace_8333767
  have hstable : (prefixWord ++ tailWord_8333767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333767).length < 2 ^ (prefixWord ++ tailWord_8333767).sum := by decide
  have hdescent : baseEnd_8333767 < baseStart_8333767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333772 : List Nat := [2, 2, 1, 4, 4, 1, 2, 1, 2, 2, 2]
def baseStart_8333772 : Nat := 118140960795 + 8333772 * 2 ^ 59
def prefixEnd_8333772 : Nat := 4983230072969 + 3 ^ 40 * 8333772 * 2
def baseEnd_8333772 : Nat := 4279230700981273312423687

theorem tailTrace_8333772 : CollatzResearch.WordTrace tailWord_8333772 prefixEnd_8333772 4279230700981273312423687 := by
  unfold tailWord_8333772
  simp only [CollatzResearch.WordTrace]
  refine ⟨151978817982087406894205785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 202638423976116542525607713 151978817982087406894205785)
  ·
    refine ⟨113984113486565555170654339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151978817982087406894205785 113984113486565555170654339)
    ·
      refine ⟨170976170229848332755981509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113984113486565555170654339 170976170229848332755981509)
      ·
        refine ⟨32058031918096562391746533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170976170229848332755981509 32058031918096562391746533)
        ·
          refine ⟨6010880984643105448452475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32058031918096562391746533 6010880984643105448452475)
          ·
            refine ⟨9016321476964658172678713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6010880984643105448452475 9016321476964658172678713)
            ·
              refine ⟨6762241107723493629509035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9016321476964658172678713 6762241107723493629509035)
              ·
                refine ⟨10143361661585240444263553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6762241107723493629509035 10143361661585240444263553)
                ·
                  refine ⟨7607521246188930333197665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10143361661585240444263553 7607521246188930333197665)
                  ·
                    refine ⟨5705640934641697749898249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7607521246188930333197665 5705640934641697749898249)
                    ·
                      refine ⟨4279230700981273312423687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5705640934641697749898249 4279230700981273312423687)
                      ·
                        rfl

theorem cell23_8333772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_8333772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333772 prefixEnd_8333772 := by exact prefixLift 8333772
  have htrace : WordTrace (prefixWord ++ tailWord_8333772) baseStart_8333772 baseEnd_8333772 := by
    simpa [prefixWord, tailWord_8333772, baseEnd_8333772] using wordTrace_append hprefix tailTrace_8333772
  have hstable : (prefixWord ++ tailWord_8333772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333772).length < 2 ^ (prefixWord ++ tailWord_8333772).sum := by decide
  have hdescent : baseEnd_8333772 < baseStart_8333772 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333817 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 6]
def baseStart_8333817 : Nat := 118140960795 + 8333817 * 2 ^ 59
def prefixEnd_8333817 : Nat := 4983230072969 + 3 ^ 40 * 8333817 * 2
def baseEnd_8333817 : Nat := 475472645290080626262331

theorem tailTrace_8333817 : CollatzResearch.WordTrace tailWord_8333817 prefixEnd_8333817 475472645290080626262331 := by
  unfold tailWord_8333817
  simp only [CollatzResearch.WordTrace]
  refine ⟨303959277249011786473799705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202639518166007857649199803 303959277249011786473799705)
  ·
    refine ⟨227969457936758839855349779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303959277249011786473799705 227969457936758839855349779)
    ·
      refine ⟨341954186905138259783024669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227969457936758839855349779 341954186905138259783024669)
      ·
        refine ⟨128232820089426847418634251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 341954186905138259783024669 128232820089426847418634251)
        ·
          refine ⟨192349230134140271127951377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128232820089426847418634251 192349230134140271127951377)
          ·
            refine ⟨144261922600605203345963533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 192349230134140271127951377 144261922600605203345963533)
            ·
              refine ⟨54098220975226951254736325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 144261922600605203345963533 54098220975226951254736325)
              ·
                refine ⟨10143416432855053360263061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54098220975226951254736325 10143416432855053360263061)
                ·
                  refine ⟨475472645290080626262331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10143416432855053360263061 475472645290080626262331)
                  ·
                    rfl

theorem cell23_8333817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 6].length) (baseStart_8333817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333817 prefixEnd_8333817 := by exact prefixLift 8333817
  have htrace : WordTrace (prefixWord ++ tailWord_8333817) baseStart_8333817 baseEnd_8333817 := by
    simpa [prefixWord, tailWord_8333817, baseEnd_8333817] using wordTrace_append hprefix tailTrace_8333817
  have hstable : (prefixWord ++ tailWord_8333817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333817).length < 2 ^ (prefixWord ++ tailWord_8333817).sum := by decide
  have hdescent : baseEnd_8333817 < baseStart_8333817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333821 : List Nat := [1, 4, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_8333821 : Nat := 118140960795 + 8333821 * 2 ^ 59
def prefixEnd_8333821 : Nat := 4983230072969 + 3 ^ 40 * 8333821 * 2
def baseEnd_8333821 : Nat := 1426418620511114540236987

theorem tailTrace_8333821 : CollatzResearch.WordTrace tailWord_8333821 prefixEnd_8333821 1426418620511114540236987 := by
  unfold tailWord_8333821
  simp only [CollatzResearch.WordTrace]
  refine ⟨303959423140997295156945317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202639615427331530104630211 303959423140997295156945317)
  ·
    refine ⟨56992391838936992841927247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 303959423140997295156945317 56992391838936992841927247)
    ·
      refine ⟨85488587758405489262890871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56992391838936992841927247 85488587758405489262890871)
      ·
        refine ⟨128232881637608233894336307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85488587758405489262890871 128232881637608233894336307)
        ·
          refine ⟨192349322456412350841504461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128232881637608233894336307 192349322456412350841504461)
          ·
            refine ⟨72130995921154631565564173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 192349322456412350841504461 72130995921154631565564173)
            ·
              refine ⟨27049123470432986837086565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72130995921154631565564173 27049123470432986837086565)
              ·
                refine ⟨5071710650706185031953731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27049123470432986837086565 5071710650706185031953731)
                ·
                  refine ⟨7607565976059277547930597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5071710650706185031953731 7607565976059277547930597)
                  ·
                    refine ⟨1426418620511114540236987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7607565976059277547930597 1426418620511114540236987)
                    ·
                      rfl

theorem cell23_8333821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_8333821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333821 prefixEnd_8333821 := by exact prefixLift 8333821
  have htrace : WordTrace (prefixWord ++ tailWord_8333821) baseStart_8333821 baseEnd_8333821 := by
    simpa [prefixWord, tailWord_8333821, baseEnd_8333821] using wordTrace_append hprefix tailTrace_8333821
  have hstable : (prefixWord ++ tailWord_8333821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333821).length < 2 ^ (prefixWord ++ tailWord_8333821).sum := by decide
  have hdescent : baseEnd_8333821 < baseStart_8333821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333878 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_8333878 : Nat := 118140960795 + 8333878 * 2 ^ 59
def prefixEnd_8333878 : Nat := 4983230072969 + 3 ^ 40 * 8333878 * 2
def baseEnd_8333878 : Nat := 4279285129930649897698199

theorem tailTrace_8333878 : CollatzResearch.WordTrace tailWord_8333878 prefixEnd_8333878 4279285129930649897698199 := by
  unfold tailWord_8333878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18997593881361924618235643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 202641001401193862594513525 18997593881361924618235643)
  ·
    refine ⟨28496390822042886927353465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18997593881361924618235643 28496390822042886927353465)
    ·
      refine ⟨21372293116532165195515099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28496390822042886927353465 21372293116532165195515099)
      ·
        refine ⟨32058439674798247793272649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21372293116532165195515099 32058439674798247793272649)
        ·
          refine ⟨24043829756098685844954487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32058439674798247793272649 24043829756098685844954487)
          ·
            refine ⟨36065744634148028767431731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24043829756098685844954487 36065744634148028767431731)
            ·
              refine ⟨54098616951222043151147597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36065744634148028767431731 54098616951222043151147597)
              ·
                refine ⟨20286981356708266181680349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54098616951222043151147597 20286981356708266181680349)
                ·
                  refine ⟨7607618008765599818130131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20286981356708266181680349 7607618008765599818130131)
                  ·
                    refine ⟨11411427013148399727195197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7607618008765599818130131 11411427013148399727195197)
                    ·
                      refine ⟨4279285129930649897698199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11411427013148399727195197 4279285129930649897698199)
                      ·
                        rfl

theorem cell23_8333878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_8333878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333878 prefixEnd_8333878 := by exact prefixLift 8333878
  have htrace : WordTrace (prefixWord ++ tailWord_8333878) baseStart_8333878 baseEnd_8333878 := by
    simpa [prefixWord, tailWord_8333878, baseEnd_8333878] using wordTrace_append hprefix tailTrace_8333878
  have hstable : (prefixWord ++ tailWord_8333878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333878).length < 2 ^ (prefixWord ++ tailWord_8333878).sum := by decide
  have hdescent : baseEnd_8333878 < baseStart_8333878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333921 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_8333921 : Nat := 118140960795 + 8333921 * 2 ^ 59
def prefixEnd_8333921 : Nat := 4983230072969 + 3 ^ 40 * 8333921 * 2
def baseEnd_8333921 : Nat := 4279307209598793229460501

theorem tailTrace_8333921 : CollatzResearch.WordTrace tailWord_8333921 prefixEnd_8333921 4279307209598793229460501 := by
  unfold tailWord_8333921
  simp only [CollatzResearch.WordTrace]
  refine ⟨303963070440635012235585617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202642046960423341490390411 303963070440635012235585617)
  ·
    refine ⟨227972302830476259176689213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 303963070440635012235585617 227972302830476259176689213)
    ·
      refine ⟨85489613561428597191258455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227972302830476259176689213 85489613561428597191258455)
      ·
        refine ⟨128234420342142895786887683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85489613561428597191258455 128234420342142895786887683)
        ·
          refine ⟨192351630513214343680331525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128234420342142895786887683 192351630513214343680331525)
          ·
            refine ⟨36065930721227689440062161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 192351630513214343680331525 36065930721227689440062161)
            ·
              refine ⟨27049448040920767080046621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36065930721227689440062161 27049448040920767080046621)
              ·
                refine ⟨10143543015345287655017483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27049448040920767080046621 10143543015345287655017483)
                ·
                  refine ⟨15215314523017931482526225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10143543015345287655017483 15215314523017931482526225)
                  ·
                    refine ⟨11411485892263448611894669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15215314523017931482526225 11411485892263448611894669)
                    ·
                      refine ⟨4279307209598793229460501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11411485892263448611894669 4279307209598793229460501)
                      ·
                        rfl

theorem cell23_8333921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_8333921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333921 prefixEnd_8333921 := by exact prefixLift 8333921
  have htrace : WordTrace (prefixWord ++ tailWord_8333921) baseStart_8333921 baseEnd_8333921 := by
    simpa [prefixWord, tailWord_8333921, baseEnd_8333921] using wordTrace_append hprefix tailTrace_8333921
  have hstable : (prefixWord ++ tailWord_8333921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333921).length < 2 ^ (prefixWord ++ tailWord_8333921).sum := by decide
  have hdescent : baseEnd_8333921 < baseStart_8333921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8333941 : List Nat := [1, 3, 4, 2, 2, 1, 2, 8]
def baseStart_8333941 : Nat := 118140960795 + 8333941 * 2 ^ 59
def prefixEnd_8333941 : Nat := 4983230072969 + 3 ^ 40 * 8333941 * 2
def baseEnd_8333941 : Nat := 158493239970810487081867

theorem tailTrace_8333941 : CollatzResearch.WordTrace tailWord_8333941 prefixEnd_8333941 158493239970810487081867 := by
  unfold tailWord_8333941
  simp only [CollatzResearch.WordTrace]
  refine ⟨303963799900562555651313677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 202642533267041703767542451 303963799900562555651313677)
  ·
    refine ⟨113986424962710958369242629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 303963799900562555651313677 113986424962710958369242629)
    ·
      refine ⟨21372454680508304694232993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113986424962710958369242629 21372454680508304694232993)
      ·
        refine ⟨16029341010381228520674745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21372454680508304694232993 16029341010381228520674745)
        ·
          refine ⟨12022005757785921390506059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16029341010381228520674745 12022005757785921390506059)
          ·
            refine ⟨18033008636678882085759089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12022005757785921390506059 18033008636678882085759089)
            ·
              refine ⟨13524756477509161564319317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18033008636678882085759089 13524756477509161564319317)
              ·
                refine ⟨158493239970810487081867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13524756477509161564319317 158493239970810487081867)
                ·
                  rfl

theorem cell23_8333941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 8].length) (baseStart_8333941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8333941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8333941 prefixEnd_8333941 := by exact prefixLift 8333941
  have htrace : WordTrace (prefixWord ++ tailWord_8333941) baseStart_8333941 baseEnd_8333941 := by
    simpa [prefixWord, tailWord_8333941, baseEnd_8333941] using wordTrace_append hprefix tailTrace_8333941
  have hstable : (prefixWord ++ tailWord_8333941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8333941).length < 2 ^ (prefixWord ++ tailWord_8333941).sum := by decide
  have hdescent : baseEnd_8333941 < baseStart_8333941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8333941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
